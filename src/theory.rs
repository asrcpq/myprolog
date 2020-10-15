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

fn instmap_merge(mut map1: InstMap, mut map2: InstMap, mut id: u32) -> Option<(InstMap, u32)> {
	while !map2.is_empty() {
		let key = map2.keys().next().unwrap().clone();
		let value = map2.remove(&key).unwrap();
		if map1.get(&key).is_none() { map1.insert(key.to_string(), value); }
		else {
			let value1 = map1.remove(&key).unwrap();
			let new_map = match value1.target_match(value, id) {
				None => return None,
				Some((new_map, new_id)) => {
					id = new_id;
					new_map
				}
			};
			match instmap_merge(map2, new_map, id) {
				None => return None,
				Some((new_map, new_id)) => {
					id = new_id;
					map2 = new_map;
				}
			}
		}
	}
	Some((map1, id))
}

impl Pred {
	fn clone_subtree(&self, mut target: &mut Pred, id: usize) -> usize {
		let mut id_list = Vec::new();
		for child in self.nodes[id].data.iter() {
			id_list.push(self.clone_subtree(target, *child));
		}
		target.push_node(self.nodes[id].ident.clone(), id_list)
	}

	fn subtree(&self, id: usize) -> Pred {
		let mut result: Pred = Default::default();
		self.clone_subtree(&mut result, id);
		result
	}

	pub fn target_match(&self, target: Pred, mut suffix_alloc_id: u32) -> Option<(InstMap, u32)> {
		let mut map: InstMap = HashMap::new();
		// recurive head matcher
		let mnode = self.nodes.last().unwrap().clone();
		let tnode = target.nodes.last().unwrap().clone();
		match (mnode.get_type(), tnode.get_type()) {
			(1, 2) | (2, 1) => {return None},
			(2, 2) | (1, 1)=> {
				if mnode.ident != tnode.ident {
					return None;
				}
				for (m_node, t_node) in mnode.data.iter().zip(tnode.data.iter()) {
					let mchild = self.subtree(*m_node);
					let tchild = self.subtree(*t_node);
					match mchild.target_match(tchild, suffix_alloc_id) {
						None => return None,
						Some((new_map, new_id)) => {
							suffix_alloc_id = new_id;
						}
					}
				}
			},
			(0, 0) => {
				match (map.remove(&mnode.ident), map.remove(&tnode.ident)) {
					(None, None) => {
						let mut map_to: Pred = Default::default();
						map_to.push_node(
							format!("_{}", suffix_alloc_id),
							Vec::new(),
						);
						map.insert(mnode.ident.clone(), map_to.clone());
						map.insert(tnode.ident.clone(), map_to);
						suffix_alloc_id += 1;
					}
					(Some(m_pred), Some(t_pred)) => {
						match m_pred.target_match(t_pred, suffix_alloc_id) {
							None => return None,
							Some((new_map, new_id)) => {
								suffix_alloc_id = new_id;
								map.extend(new_map);
							}
						}
					}
					_ => {unreachable!()}
				}
			}
			_ => { unreachable!() }
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
