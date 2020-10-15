use std::collections::{HashMap, VecDeque};

#[derive(Default)]
pub struct Theory {
	clauses: HashMap<String, Vec<Clause>>,
}

impl Theory {
	pub fn from_string(string: &str) -> Theory {
		let mut result: Theory = Default::default();
		for clause in string.split(".") {
			if clause.is_empty() { continue }
			let new_clause = Clause::from_string(clause);
			let name = new_clause.get_name();
			match result.clauses.get(&name) {
				None => {
					result.clauses.insert(new_clause.get_name(), vec![new_clause]);
				}
				_ => {
					let mut poped = result.clauses.remove(&name).unwrap();
					poped.push(new_clause);
					result.clauses.insert(name, poped);
				}
			}
		}
		result
	}
}

#[derive(Debug, Default)]
struct Clause {
	head: Pred,
	body: Vec<Pred>,
}

type InstMap = HashMap<String, Pred>;

impl Clause {
	fn get_name(&self) -> String {
		self.head.nodes.last().unwrap().ident.clone()
	}

	fn to_string(&self) -> String {
		let mut result = self.head.to_string();
		if self.body.is_empty() {
			return result;
		}
		result += " :- ";
		for body in self.body.iter() {
			result += &body.to_string();
			result += ", "
		}
		result.pop();
		result.pop();
		result
	}

	fn from_string(string: &str) -> Clause {
		use plex::lexer;
		pub enum TokenOrUnit {
			Ident(String),
			Whitespace,
			LeftParenthesis,
			RightParenthesis,
			Unit(usize),
		}

		lexer! {
			fn next_token(text: 'a) -> TokenOrUnit;

			r#"[A-Za-z0-9_]+"# => TokenOrUnit::Ident(text.to_owned()),
			r#"\("# => TokenOrUnit::LeftParenthesis,
			r#"\)"# => TokenOrUnit::RightParenthesis,
			r#"."# => TokenOrUnit::Whitespace,
		}

		let mut result: Clause = Default::default();

		let mut remaining = string;
		let mut token_stack = Vec::new();
		let mut plevel: usize = 0;
		let mut pred_num: usize = 0; // 0 is head
		let mut current_pred: Pred = Default::default();
		while let Some((token, new_remaining)) = next_token(&remaining) {
			match token {
				TokenOrUnit::Whitespace => {}
				TokenOrUnit::LeftParenthesis => {
					plevel += 1;
					token_stack.push(TokenOrUnit::LeftParenthesis);
				}
				TokenOrUnit::RightParenthesis => {
					let mut id_list = VecDeque::new();
					loop {
						match token_stack.pop() {
							Some(token) => match token {
								TokenOrUnit::LeftParenthesis => {
									match token_stack.pop() {
										Some(TokenOrUnit::Ident(string)) => {
											token_stack.push(TokenOrUnit::Unit(
												current_pred.push_node(string, Vec::from(id_list)),
											));
										}
										_ => {
											panic!("Invalid predicate name!");
										}
									}
									plevel -= 1;
									if plevel == 0 {
										if pred_num == 0 {
											result.head = current_pred;
										} else {
											result.body.push(current_pred);
										}
										pred_num += 1;
										current_pred = Default::default();
									}
									break;
								}
								TokenOrUnit::Ident(string) => {
									id_list.push_front(current_pred.push_node(string, Vec::new()));
								}
								TokenOrUnit::Unit(id) => {
									id_list.push_front(id);
								}
								_ => panic!("Invalid element during rightp collasping!"),
							},
							None => {
								panic!("Unmatched rightp!");
							}
						}
					}
				}
				other => {
					token_stack.push(other);
				}
			}
			remaining = new_remaining;
		}
		result
	}

	// If match success, return new targets(I-match-ed) and inst map(E-match)
	// This function doesn't check argity!
	// fn match_target(&mut self, target: Pred, alloc_id: usize) -> Option<(Vec<Pred>, InstMap)> {
	// }

	fn instantiate(&self, mut suffix_alloc_id: u32) -> (Clause, u32) {
		let mut new_clause: Clause = Default::default();
		let mut instmap: HashMap<String, String> = HashMap::new();
		for each_pred in std::iter::once(&self.head).chain(self.body.iter()) {
			let mut new_pred: Pred = Default::default();
			for each_node in each_pred.nodes.iter() {
				if each_node.get_type() == 0 {
					match instmap.get(&each_node.ident) {
						Some(name) => {
							new_pred.push_node(
								name.to_string(),
								each_node.data.clone(),
							);
						}
						None => {
							let name = format!("_{}", suffix_alloc_id);
							instmap.insert(each_node.ident.clone(), name.clone());
							new_pred.push_node(
								name,
								each_node.data.clone(),
							);
						}
					}
					suffix_alloc_id += 1;
				} else {
					new_pred.nodes.push(each_node.clone());
				}
			}
			if new_clause.head.nodes.is_empty() {
				new_clause.head = new_pred;
			} else {
				new_clause.body.push(new_pred);
			}
		}
		(new_clause, suffix_alloc_id)
	}
}

#[derive(Clone, Debug, Default)]
struct Pred {
	nodes: Vec<PredNode>,
}

impl Pred {
	pub fn target_match(&self, target: Pred, mut suffix_alloc_id: u32) -> Option<(HashMap<String, Pred>, u32)> {
		let mut my_nodes = vec![self.nodes.len() - 1];
		let mut t_nodes = vec![target.nodes.len() - 1];
		let mut map: InstMap = HashMap::new();
		// recurive head matcher
		loop {
			let my_node = match my_nodes.pop() {
				None => {break},
				Some(node) => node,
			};
			let t_node = match t_nodes.pop() {
				None => {unreachable!()},
				Some(node) => node,
			};
			let mi = self.nodes[my_node].ident.clone();
			let ti = target.nodes[my_node].ident.clone();
			match (self.nodes[my_node].get_type(), target.nodes[t_node].get_type()) {
				(1, 2) | (2, 1) => {return None},
				(2, 2) | (1, 1)=> {
					if self.nodes[my_node].ident != target.nodes[t_node].ident {
						return None;
					}
					for each_node in self.nodes[my_node].data.iter() {
						my_nodes.push(*each_node);
					}
					for each_node in target.nodes[my_node].data.iter() {
						t_nodes.push(*each_node);
					}
				},
				(0, 0) => {
					match (map.get(&mi), map.get(&ti)) {
						(None, None) => {
							let mut map_to: Pred = Default::default();
							map_to.push_node(
								format!("_{}", suffix_alloc_id),
								Vec::new(),
							);
							map.insert(mi, map_to.clone());
							map.insert(ti, map_to);
							suffix_alloc_id += 1;
						}
						(Some(m_pred), Some(t_pred)) => {
						}
						_ => {unreachable!()}
					}
				}
				_ => { unreachable!() }
			}
		}
		Some((map, suffix_alloc_id))
	}

	pub fn push_node(&mut self, ident: String, data: Vec<usize>) -> usize {
		self.nodes.push(PredNode { ident, data });
		self.nodes.len() - 1
	}

	pub fn to_string_recurse(&self, id: usize) -> String {
		let mut result = self.nodes[id].ident.clone();
		if self.nodes[id].data.is_empty() {
			return result;
		}
		result += "(";
		for each_node in self.nodes[id].data.iter() {
			result += &self.to_string_recurse(*each_node);
			result += ", ";
		}
		result.pop();
		result.pop();
		result += ")";
		result
	}

	pub fn to_string(&self) -> String {
		self.to_string_recurse(self.nodes.len() - 1)
	}
}

#[derive(Clone, Debug)]
struct PredNode {
	ident: String,
	data: Vec<usize>,
}

impl PredNode {
	// 0: v, 1: c, 2: r
	fn get_type(&self) -> i32 {
		let vorc = match self.ident.chars().next().unwrap() {
			'A'..='Z' => {true},
			'a'..='z' => {false},
			'_' => return 0,
			_ => panic!("Unknown char!"),
		};
		if self.data.is_empty() {
			return 0;
		}
		if vorc { return 0; } else { return 1; }
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn clause_string_io() {
		let clause = Clause::from_string("father(tom, bob)");
		assert_eq!(clause.to_string(), "father(tom, bob)");
		let clause = Clause::from_string("greater(X, Y) :- greater(X, Z), greater(Z, Y)");
		assert_eq!(
			clause.to_string(),
			"greater(X, Y) :- greater(X, Z), greater(Z, Y)"
		);
		let clause = Clause::from_string("add(s(X), Y, s(Z)) :- add(X, Y, Z)");
		println!("{:#?}", clause);
		assert_eq!(clause.to_string(), "add(s(X), Y, s(Z)) :- add(X, Y, Z)");
	}

	#[test]
	fn clause_instantiate() {
		let clause = Clause::from_string("greater(X, Y) :- greater(X, Z), greater(Z, Y)");
		// reversed order, instantiate is not recursive algorithm
		assert_eq!(
			clause.instantiate(0).0.to_string(),
			"greater(_1, _0) :- greater(_1, _2), greater(_2, _0)"
		);
	}
}
