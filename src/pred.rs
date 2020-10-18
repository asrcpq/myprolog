#[allow(unused_imports)]
use ntest::timeout;
use std::collections::HashMap;

#[derive(Clone, Debug, Default, Eq, Hash, PartialEq)]
pub struct Pred {
	pub nodes: Vec<PredNode>,
}

pub type InstMap = HashMap<String, Pred>;

pub fn instmap_to_string(map: &InstMap) -> String {
	let mut result = String::new();
	for (key, value) in map.iter() {
		result += key;
		result += "->";
		result += &value.to_string();
		result += " ";
	}
	result
}

fn instmap_compress(mut map: InstMap) -> InstMap {
	if map.is_empty() {
		return map;
	}
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
					graph.insert(
						value.nodes[0].ident.clone(),
						vec![Pred::vc_from_string(key)],
					);
				}
			}
		}
	}

	map = Default::default();

	let mut concomp_queue = Vec::new();
	let mut concomp_collect: Vec<String> = Vec::new();
	let mut non_variable: Option<Pred> = None;
	loop {
		match concomp_queue.pop() {
			None => {
				if concomp_collect.is_empty() {
					let key = graph.keys().next().unwrap();
					concomp_queue.push(key.clone());
					continue;
				}
				if non_variable.is_none() {
					non_variable = Some(Pred::vc_from_string(concomp_collect[0].clone()));
				}
				for each_var in concomp_collect.into_iter() {
					map.insert(each_var, non_variable.clone().unwrap());
				}
				concomp_collect = Vec::new();
				non_variable = None;
				match graph.keys().next() {
					None => break,
					Some(key) => concomp_queue.push(key.clone()),
				};
			}
			Some(string) => {
				for each_pred in match graph.remove(&string) {
					Some(vec) => vec.into_iter(),
					None => Vec::new().into_iter(),
				} {
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

fn instmap_merge(mut map1: InstMap, map2: InstMap, mut id: u32) -> Option<(InstMap, u32)> {
	if map1.is_empty() {
		return Some((map2, id));
	}
	if map2.is_empty() {
		return Some((map1, id));
	}
	//println!("[31mMERGE[0m");
	let mut map_list = vec![map2];
	let mut merge_queue = HashMap::new().into_iter();
	loop {
		//println!("l {:?}", merge_queue);
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
		match map1.remove(&key) {
			None => {
				map1.insert(key.to_string(), value);
			}
			Some(value1) => {
				map1.insert(key.to_string(), value.clone());
				if value != value1 {
					let new_map = match value1.match_target(value, id) {
						None => return None,
						Some((new_map, new_id)) => {
							id = new_id;
							new_map
						}
					};
					//println!("[33mPUSHING:[0m {:?}", new_map);
					map_list.push(new_map);
				}
			}
		}
	}
	map1 = instmap_compress(map1);
	//println!("[32mmerged[0m{:?}", map1);
	Some((map1, id))
}

impl Pred {
	pub fn get_name(&self) -> String {
		self.nodes.last().unwrap().ident.clone()
	}

	fn clone_subtree(&self, target: &mut Pred, id: usize) -> usize {
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
		// println!("map {:#?} to {:#?}", self.to_string(), target.to_string());
		match (self.get_type(), target.get_type()) {
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
							suffix_alloc_id = new_id;
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
			}
			(0, 0) => {
				let mut new_map = HashMap::new();
				new_map.insert(mnode.ident, target);
				match instmap_merge(map, new_map, suffix_alloc_id) {
					None => return None,
					Some((new_map, new_id)) => {
						map = new_map;
						suffix_alloc_id = new_id;
					}
				}
			}
			(0, 1) | (1, 0) => {
				let (vid, cpred) = if mnode.get_type() == 0 {
					(mnode.ident, tnode)
				} else {
					(tnode.ident, mnode)
				};
				map.insert(vid, cpred.to_vc());
			}
			(0, 2) | (2, 0) => {
				let (vid, pred) = if mnode.get_type() == 0 {
					(mnode.ident, target)
				} else {
					(tnode.ident, self.clone())
				};
				map.insert(vid, pred);
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
			}],
		}
	}

	fn instantiate_recurse(&self, target: &mut Pred, instmap: &InstMap, id: usize) -> usize {
		//println!("{} {} {:#?}", self.to_string(), target.to_string(), instmap);
		let ident = self.nodes[id].ident.clone();
		if self.nodes[id].get_type() == 2 {
			let data_vec: Vec<usize> = self.nodes[id]
				.data
				.iter()
				.map(|x| self.instantiate_recurse(target, instmap, *x))
				.collect();
			target.push_node(ident, data_vec)
		} else {
			// No need to check const
			match instmap.get(&ident) {
				None => target.push_node(ident, Vec::new()),
				Some(pred) => {
					// variable may cause infinite recurse
					if pred.get_type() != 2 {
						return target.push_node(pred.nodes[0].ident.clone(), Vec::new());
					}
					// tricky!
					pred.instantiate_recurse(target, instmap, pred.nodes.len() - 1)
				}
			}
		}
	}

	pub fn instantiate(&self, instmap: &InstMap) -> Pred {
		let mut result: Pred = Default::default();
		self.instantiate_recurse(&mut result, instmap, self.nodes.len() - 1);
		result
	}

	pub fn get_type(&self) -> i32 {
		self.nodes.last().unwrap().get_type()
	}
}

impl std::fmt::Display for Pred {
	fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		if self.nodes.is_empty() {
			write!(f, "Empty")
		} else {
			write!(f, "{}", self.to_string_recurse(self.nodes.len() - 1))
		}
	}
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct PredNode {
	pub ident: String,
	pub data: Vec<usize>,
}

impl PredNode {
	// 0: v, 1: c, 2: r
	pub fn get_type(&self) -> i32 {
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
			0
		} else {
			1
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
	use crate::clause::Clause;
	#[test]
	#[timeout(1000)]
	fn pred_match_vc() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(X, Y) :- greater(x, y).", 0);
		match clause.head.match_target(clause.body[0].clone(), 0) {
			None => panic!("VV match failed"),
			Some((map, _)) => {
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
	#[timeout(1000)]
	fn pred_match_vvvc() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(X, X, b) :- greater(Y, a, Y).", 0);
		assert!(clause
			.head
			.match_target(clause.body[0].clone(), 0)
			.is_none());
	}

	#[test]
	#[timeout(1000)]
	fn pred_match_vvvc2() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(X, X, b) :- greater(Y, A, Y).", 0);
		match clause.head.match_target(clause.body[0].clone(), 0) {
			None => panic!("VV match failed"),
			Some((map, _)) => {
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
	#[timeout(1000)]
	fn pred_match_vp_recurse_fail() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(X, X) :- greater(f(x), f(y)).", 0);
		assert!(clause
			.head
			.match_target(clause.body[0].clone(), 0)
			.is_none());
	}

	#[test]
	#[timeout(1000)]
	fn pred_match_vp_pname_fail() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(X, X) :- greater(f(x), g(x)).", 0);
		assert!(clause
			.head
			.match_target(clause.body[0].clone(), 0)
			.is_none());
	}

	#[test]
	#[timeout(1000)]
	fn pred_match_pp() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(f(X)) :- greater(f(x)).", 0);
		match clause.head.match_target(clause.body[0].clone(), 0) {
			None => panic!("PP match failed"),
			Some((map, _)) => {
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
	#[timeout(1000)]
	fn pred_match_pp_fail() {
		// construct a dummy clause to extract predicates
		let (clause, _) = Clause::from_string("greater(f(g(X))) :- greater(f(x)).", 0);
		assert!(clause
			.head
			.match_target(clause.body[0].clone(), 0)
			.is_none());
	}

	#[test]
	#[timeout(1000)]
	fn pred_match_pp_recurse_complex() {
		// construct a dummy clause to extract predicates
		let (clause, _) =
			Clause::from_string("greater(X, f(X, g(X))) :- greater(A, f(A, g(a))).", 0);
		match clause.head.match_target(clause.body[0].clone(), 0) {
			None => panic!("PP match failed"),
			Some((map, _)) => {
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

	#[test]
	#[timeout(1000)]
	fn pred_match_pp_nested_instantiate() {
		let (clause, _) =
			Clause::from_string("greater(X, f(X, g(X))) :- greater(b, f(A, g(a))).", 0);
		assert!(clause
			.head
			.match_target(clause.body[0].clone(), 0)
			.is_none());
	}

	#[test]
	#[timeout(1000)]
	fn pred_match_infinite_nest() {
		let (clause, _) = Clause::from_string("greater(X, f(X)) :- greater(Y, Y).", 0);
		match clause.head.match_target(clause.body[0].clone(), 0) {
			None => panic!("PP match failed"),
			Some((map, _)) => {
				let pred = map.get(&"Y".to_string()).unwrap();
				assert_eq!(pred.nodes[0].ident, "X");
				assert_eq!(pred.nodes[1].ident, "f");
			}
		}
	}

	#[test]
	#[timeout(1000)]
	fn pred_match_infinite_nest_2() {
		let (clause, _) = Clause::from_string("greater(X, f(X), f(f(X))) :- greater(Y, Y, Y).", 0);
		match clause.head.match_target(clause.body[0].clone(), 0) {
			None => panic!("PP match failed"),
			Some((map, _)) => {
				let pred = map.get(&"X".to_string()).unwrap();
				assert_eq!(pred.nodes[0].ident, "X");
				assert_eq!(pred.nodes[1].ident, "f");
			}
		}
	}

	#[test]
	#[timeout(1000)]
	fn pred_match_infinite_nest_3() {
		let (clause, _) = Clause::from_string("greater(X, f(X), f(f(a))) :- greater(Y, Y, Y).", 0);
		assert!(clause
			.head
			.match_target(clause.body[0].clone(), 0)
			.is_none());
	}

	#[test]
	#[timeout(1000)]
	fn instmap_compress_nothing_should_not_fail() {
		let mut instmap: InstMap = Default::default();
		instmap = instmap_compress(instmap);
	}

	#[test]
	#[timeout(1000)]
	fn instmap_compress_vanilla() {
		let mut instmap: InstMap = Default::default();
		instmap.insert("A".to_string(), Pred::vc_from_string("a".to_string()));
		instmap = instmap_compress(instmap);
		assert_eq!(instmap.get("A").unwrap().nodes[0].ident, "a");
	}

	#[test]
	#[timeout(1000)]
	fn instmap_compress_2() {
		let mut instmap: InstMap = Default::default();
		instmap.insert("D".to_string(), Pred::vc_from_string("a".to_string()));
		instmap.insert("A".to_string(), Pred::vc_from_string("B".to_string()));
		instmap.insert("C".to_string(), Pred::vc_from_string("D".to_string()));
		instmap.insert("B".to_string(), Pred::vc_from_string("D".to_string()));
		instmap = instmap_compress(instmap);
		assert_eq!(instmap.get("A").unwrap().nodes[0].ident, "a");
	}
}
