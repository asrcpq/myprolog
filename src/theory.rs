use std::collections::{HashMap, VecDeque};

pub struct Theory {
	clauses: HashMap<String, Vec<Clause>>,
}

#[derive(Debug, Default)]
struct Clause {
	head: Pred,
	body: Vec<Pred>,
}

impl Clause {
	fn to_string(&self) -> String {
		let mut result = self.head.to_string();
		if self.body.is_empty() { return result }
		result += " :- ";
		for body in self.body.iter() {
			result += &body.to_string();
			result += ","
		}
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
				TokenOrUnit::Whitespace => {},
				TokenOrUnit::LeftParenthesis => {
					plevel += 1;
					token_stack.push(TokenOrUnit::LeftParenthesis);
				}
				TokenOrUnit::RightParenthesis => {
					let mut id_list = VecDeque::new();
					loop {
					match token_stack.pop() {
						Some(token) => { match token {
							TokenOrUnit::LeftParenthesis => {
								match token_stack.pop() {
									Some(TokenOrUnit::Ident(string)) => {
										current_pred.push_node(string, Vec::from(id_list));
									}
									_ => {panic!("Invalid predicate name!");}
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
								break
							}
							TokenOrUnit::Ident(string) => {
								id_list.push_front(current_pred.push_node(string, Vec::new()));
							}
							TokenOrUnit::Unit(id) => {
								id_list.push_front(id);
							}
							_ => { panic!("Invalid element during rightp collasping!") }
						}}
						None => { panic!("Unmatched rightp!"); }
					}
					}
				},
				other => {
					token_stack.push(other);
				}
			}
			remaining = new_remaining;
		}
		result
	}
}

#[derive(Debug, Default)]
struct Pred {
	nodes: Vec<PredNode>,
}

impl Pred {
	pub fn push_node(&mut self, ident: String, data: Vec<usize>) -> usize {
		self.nodes.push(PredNode {
			ident,
			data,
		});
		self.nodes.len() - 1
	}

	pub fn to_string_recurse(&self, id: usize) -> String {
		let mut result = self.nodes[id].ident.clone();
		if self.nodes[id].data.is_empty() { return result }
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

#[derive(Debug)]
struct PredNode {
	ident: String,
	data: Vec<usize>,
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn clause_from_string() {
		let clause = Clause::from_string("father(tom, bob)");
		println!("{:#?}", clause);
		assert_eq!(clause.to_string(), "father(tom, bob)");
	}
}
