use std::collections::{HashMap, VecDeque};

use crate::pred::Pred;

#[derive(Debug, Default)]
pub struct Clause {
	pub head: Pred,
	pub body: Vec<Pred>,
}

impl Clause {
	pub fn get_name(&self) -> String {
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

	pub fn from_string(string: &str, mut suffix_alloc_id: u32) -> (Clause, u32) {
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
									if string == "_" {
										id_list.push_front(current_pred.push_node(
											format!("_{}", suffix_alloc_id),
											Vec::new(),
										));
										suffix_alloc_id += 1;
									} else {
										id_list
											.push_front(current_pred.push_node(string, Vec::new()));
									}
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
		(result, suffix_alloc_id)
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
							new_pred.push_node(name.to_string(), each_node.data.clone());
						}
						None => {
							let name = format!("_{}", suffix_alloc_id);
							instmap.insert(each_node.ident.clone(), name.clone());
							new_pred.push_node(name, each_node.data.clone());
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

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn clause_string_io() {
		let (clause, _) = Clause::from_string("father(tom, bob)", 0);
		assert_eq!(clause.to_string(), "father(tom, bob)");
		let (clause, _) = Clause::from_string("greater(X, Y) :- greater(X, Z), greater(Z, Y)", 0);
		assert_eq!(
			clause.to_string(),
			"greater(X, Y) :- greater(X, Z), greater(Z, Y)"
		);
		let (clause, _) = Clause::from_string("add(s(X), Y, s(Z)) :- add(X, Y, Z)", 0);
		println!("{:#?}", clause);
		assert_eq!(clause.to_string(), "add(s(X), Y, s(Z)) :- add(X, Y, Z)");
	}

	#[test]
	fn clause_instantiate() {
		let (clause, _) = Clause::from_string("greater(X, Y) :- greater(X, Z), greater(Z, Y)", 0);
		// reversed order, instantiate is not recursive algorithm
		assert_eq!(
			clause.instantiate(0).0.to_string(),
			"greater(_1, _0) :- greater(_1, _2), greater(_2, _0)"
		);
	}
}
