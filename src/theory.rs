use std::collections::{HashMap, VecDeque};

#[derive(Default)]
pub struct Theory {
	clauses: HashMap<String, Vec<Clause>>,
	suffix_alloc_id: u32,
}

impl Theory {
	pub fn from_string(string: &str) -> Theory {
		let mut result: Theory = Default::default();
		let suffix_alloc_id = 0;
		for clause in string.split(".") {
			if clause.is_empty() {
				continue;
			}
			let (new_clause, suffix_alloc_id) = Clause::from_string(clause, suffix_alloc_id);
			let name = new_clause.get_name();
			match result.clauses.get(&name) {
				None => {
					result
						.clauses
						.insert(new_clause.get_name(), vec![new_clause]);
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

	fn from_string(string: &str, mut suffix_alloc_id: u32) -> (Clause, u32) {
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

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
struct Pred {
	nodes: Vec<PredNode>,
}

fn instmap_compress(mut map: InstMap) -> InstMap {
	println!("Compress {:#?}", map);
	let mut graph: HashMap<String, Vec<Pred>> = Default::default();
	for (key, value) in map.into_iter() {
		match graph.remove(&key) {
			Some(mut vec) => {
				vec.push(value.clone());
				graph.insert(key.clone(), vec);
			}
			None => {
				graph.insert(key.clone(), vec![value.clone()]);
			}
		}
		if value.get_type() == 0 {
			match graph.remove(&value.nodes[0].ident) {
				Some(mut vec) => {
					vec.push(Pred::vc_from_string(key));
					graph.insert(value.nodes[0].ident.clone(), vec);
				}
				None => {
					graph.insert(value.nodes[0].ident.clone(), vec![Pred::vc_from_string(key)]);
				}
			}
		}
	}

	map = Default::default();

	let mut concomp_queue = Vec::new();
	let mut concomp_collect: Vec<String> = Vec::new();
	let mut non_variable: Option<Pred> = None;
	while !graph.is_empty() {
		match concomp_queue.pop() {
			None => {
				if non_variable.is_none() {
					non_variable = Some(Pred::vc_from_string(concomp_collect[0].clone()));
				}
				for each_var in concomp_collect.into_iter() {
					map.insert(each_var, non_variable.clone().unwrap());
				}
				concomp_collect = Vec::new();
				non_variable = None;
				let key = graph.keys().next().unwrap();
				concomp_queue.push(key.clone());
			}
			Some(string) => {
				for each_pred in graph.remove(&string).unwrap().into_iter() {
					if each_pred.get_type() == 0 {
						concomp_queue.push(each_pred.nodes[0].ident.clone());
					} else {
						non_variable = Some(each_pred);
					}
				}
				concomp_collect.push(string);
			}
		}
	}

	map
}

fn instmap_merge(mut map1: InstMap, mut map2: InstMap, mut id: u32) -> Option<(InstMap, u32)> {
	let mut map_list = vec![map2];
	let mut merge_queue = HashMap::new().into_iter();
	loop {
		let (key, value) = match merge_queue.next() {
			Some((key, value)) => (key, value),
			None => {
				if map_list.is_empty() {
					break;
				} else {
					merge_queue = map_list.pop().unwrap().into_iter();
					continue;
				}
			}
		};
		if map1.get(&key).is_none() {
			map1.insert(key.to_string(), value);
		} else {
			let value1 = map1.remove(&key).unwrap();
			let new_map = match value1.match_target(value, id) {
				None => return None,
				Some((new_map, new_id)) => {
					id = new_id;
					new_map
				}
			};
			map_list.push(new_map);
		}
	}
	map1 = instmap_compress(map1);
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

	pub fn match_target(&self, target: Pred, mut suffix_alloc_id: u32) -> Option<(InstMap, u32)> {
		let mut map: InstMap = HashMap::new();
		// recurive head matcher
		let mnode = self.nodes.last().unwrap().clone();
		let tnode = target.nodes.last().unwrap().clone();
		match (mnode.get_type(), tnode.get_type()) {
			(1, 2) | (2, 1) => return None,
			(2, 2) | (1, 1) => {
				if mnode.ident != tnode.ident {
					return None;
				}
				for (m_node, t_node) in mnode.data.iter().zip(tnode.data.iter()) {
					let mchild = self.subtree(*m_node);
					let tchild = target.subtree(*t_node);
					match mchild.match_target(tchild, suffix_alloc_id) {
						None => return None,
						Some((new_map, new_id)) => {
							match instmap_merge(map, new_map, new_id) {
								None => return None,
								Some((new_map, new_id)) => {
									map = new_map;
									suffix_alloc_id = new_id;
								}
							}
							suffix_alloc_id = new_id;
						}
					}
				}
			}
			(0, 0) => match (map.remove(&mnode.ident), map.remove(&tnode.ident)) {
				(None, None) => {
					let mut new_map = HashMap::new();
					new_map.insert(mnode.ident, target.clone());
					match instmap_merge(map, new_map, suffix_alloc_id) {
						None => return None,
						Some((new_map, new_id)) => {
							map = new_map;
							suffix_alloc_id = new_id;
						}
					}
				}
				(Some(m_pred), Some(t_pred)) => {
					match m_pred.match_target(t_pred, suffix_alloc_id) {
						None => return None,
						Some((new_map, new_id)) => {
							suffix_alloc_id = new_id;
							match instmap_merge(map, new_map, new_id) {
								None => return None,
								Some((new_map, new_id)) => {
									map = new_map;
									suffix_alloc_id = new_id;
								}
							}
						}
					}
				}
				(Some(pred), None) | (None, Some(pred)) => {
					let mut new_map = HashMap::new();
					new_map.insert(mnode.ident.clone(), pred.clone());
					new_map.insert(tnode.ident.clone(), pred);
					match instmap_merge(map, new_map, suffix_alloc_id) {
						None => return None,
						Some((new_map, new_id)) => {
							map = new_map;
							suffix_alloc_id = new_id;
						}
					}
				}
			},
			(0, 1) | (1, 0) => {
				let (vid, cpred) = if mnode.get_type() == 0 {
					(mnode.ident.clone(), tnode)
				} else {
					(tnode.ident.clone(), mnode)
				};
				match map.remove(&vid) {
					None => {
						map.insert(vid, cpred.to_vc());
					}
					Some(pred) => {
						let pred_last = pred.nodes.last().unwrap().clone();
						match pred_last.get_type() {
							2 => return None,
							1 => {
								if pred_last.ident != cpred.ident {
									return None;
								}
								map.insert(vid, pred);
							}
							0 => {
								let mut new_map: InstMap = Default::default();
								for (key, value) in map.into_iter() {
									if value.nodes.last().unwrap().ident
										== pred.nodes.last().unwrap().ident
									{
										new_map.insert(key, cpred.to_vc());
									} else {
										new_map.insert(key, value);
									}
								}
								new_map.insert(vid, pred);
								map = new_map;
							}
							_ => unreachable!(),
						}
					}
				}
			}
			(0, 2) | (2, 0) => {
				let (vid, pred) = if mnode.get_type() == 0 {
					(mnode.ident.clone(), target.clone())
				} else {
					(tnode.ident.clone(), self.clone())
				};
				match map.remove(&vid) {
					None => {
						map.insert(vid, pred);
					}
					Some(pred) => {
						let mut new_map = HashMap::new();
						new_map.insert(vid, pred.clone());
						match instmap_merge(map, new_map, suffix_alloc_id) {
							None => return None,
							Some((new_map, new_id)) => {
								map = new_map;
								suffix_alloc_id = new_id;
							}
						}
					}
				}
			}
			_ => unreachable!(),
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

	pub fn vc_from_string(string: String) -> Pred {
		Pred {
			nodes: vec![PredNode {
				ident: string,
				data: Vec::new(),
			}]
		}
	}

	pub fn to_string(&self) -> String {
		self.to_string_recurse(self.nodes.len() - 1)
	}

	fn get_type(&self) -> i32 {
		self.nodes.last().unwrap().get_type()
	}
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct PredNode {
	ident: String,
	data: Vec<usize>,
}

impl PredNode {
	// 0: v, 1: c, 2: r
	fn get_type(&self) -> i32 {
		let vorc = match self.ident.chars().next().unwrap() {
			'A'..='Z' => true,
			'a'..='z' => false,
			'_' => return 0,
			_ => panic!("Unknown char!"),
		};
		if !self.data.is_empty() {
			return 2;
		}
		if vorc {
			return 0;
		} else {
			return 1;
		}
	}

	fn to_vc(&self) -> Pred {
		let mut node = self.clone();
		node.data.drain(..);
		Pred { nodes: vec![node] }
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

	#[test]
	fn pred_match_vc() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(X, Y) :- greater(x, y).", 0);
		match clause.head.match_target(clause.body[0].clone(), 0) {
			None => panic!("VV match failed"),
			Some((map, id)) => {
				assert_eq!(
					map.get(&"X".to_string())
						.unwrap()
						.nodes
						.last()
						.unwrap()
						.ident,
					"x"
				);
				assert_eq!(
					map.get(&"Y".to_string())
						.unwrap()
						.nodes
						.last()
						.unwrap()
						.ident,
					"y"
				);
			}
		}
	}

	#[test]
	fn pred_match_vvvc() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(X, X, b) :- greater(Y, a, Y).", 0);
		assert!(clause
			.head
			.match_target(clause.body[0].clone(), 0)
			.is_none());
	}

	#[test]
	fn pred_match_vvvc2() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(X, X, b) :- greater(Y, A, Y).", 0);
		match clause.head.match_target(clause.body[0].clone(), 0) {
			None => panic!("VV match failed"),
			Some((map, id)) => {
				assert_eq!(
					map.get(&"A".to_string())
						.unwrap()
						.nodes
						.last()
						.unwrap()
						.ident,
					"b"
				);
			}
		}
	}

	#[test]
	fn pred_match_vp_recurse_fail() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(X, X) :- greater(f(x), f(y)).", 0);
		assert!(clause
			.head
			.match_target(clause.body[0].clone(), 0)
			.is_none());
	}

	#[test]
	fn pred_match_vp_pname_fail() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(X, X) :- greater(f(x), g(x)).", 0);
		assert!(clause
			.head
			.match_target(clause.body[0].clone(), 0)
			.is_none());
	}

	#[test]
	fn pred_match_pp() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(f(X)) :- greater(f(x)).", 0);
		match clause.head.match_target(clause.body[0].clone(), 0) {
			None => panic!("PP match failed"),
			Some((map, id)) => {
				assert_eq!(
					map.get(&"X".to_string())
						.unwrap()
						.nodes
						.last()
						.unwrap()
						.ident,
					"x"
				);
			}
		}
	}

	#[test]
	fn pred_match_pp_fail() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(f(g(X))) :- greater(f(x)).", 0);
		assert!(clause
			.head
			.match_target(clause.body[0].clone(), 0)
			.is_none());
	}

	#[test]
	fn pred_match_pp_recurse_complex() {
		// construct a dummy clause to extract predicates
		let (clause, _) =
			Clause::from_string("greater(X, f(X, g(X))) :- greater(A, f(A, g(a))).", 0);
		match clause.head.match_target(clause.body[0].clone(), 0) {
			None => panic!("PP match failed"),
			Some((map, id)) => {
				assert_eq!(
					map.get(&"X".to_string())
						.unwrap()
						.nodes
						.last()
						.unwrap()
						.ident,
					"a"
				);
			}
		}
	}

	// #[test]
	// fn pred_match_pp_nested_instantiate() {
	// 	let (clause, _) = Clause::from_string(
	// 		"greater(X, f(X, g(X))) :- greater(b, f(A, g(a))).",
	// 		0,
	// 	);
	// 	assert!(clause.head.match_target(clause.body[0].clone(), 0).is_none());
	// }
}
