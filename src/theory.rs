#[allow(unused_imports)]
use ntest::timeout;
use std::collections::{HashMap, VecDeque};

use crate::clause::Clause;
use crate::pred::instmap_to_string;
use crate::pred::Pred;

#[derive(Default)]
pub struct Theory {
	clauses: HashMap<String, Vec<Clause>>,
	suffix_alloc_id: u32,
}

#[derive(Debug, PartialEq)]
pub enum ProveResult {
	Succeed,
	Fail,
	DepthExceed,
}

impl Theory {
	pub fn display(&self) {
		for (_, clauses) in self.clauses.iter() {
			for clause in clauses.iter() {
				println!("{}", clause.to_string());
			}
		}
	}

	pub fn from_string(string: &str) -> Theory {
		let mut result: Theory = Default::default();
		let mut suffix_alloc_id = 0;
		let mut strings = string
			.split('.')
			.map(|x| x.to_string())
			.collect::<Vec<String>>();
		strings.pop();
		for clause in strings.into_iter() {
			if clause.is_empty() {
				continue;
			}
			let (new_clause, new_id) = Clause::from_string(&clause, suffix_alloc_id);
			suffix_alloc_id = new_id;
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
		result.suffix_alloc_id = suffix_alloc_id;
		result
	}

	pub fn prove(&self, dmax: usize) -> ProveResult {
		let mut target = Pred::vc_from_string("goal".to_string());
		let mut targets_stack: Vec<VecDeque<Pred>> =
			vec![std::iter::once(target.clone()).collect()];
		let mut id_stack: Vec<u32> = vec![self.suffix_alloc_id];
		let mut rule_id_stack: Vec<usize> = vec![0];
		let mut depth_flag = false;
		loop {
			//println!("ris {:?}", rule_id_stack);
			let mut rule_id = rule_id_stack.pop().unwrap();
			if targets_stack.len() > dmax {
				println!("[31mDEEP[0m");
				depth_flag = true;
			} else {
				if let Some(vec_clause) = self.clauses.get(&target.get_name()) {
					let id = id_stack.last().unwrap();
					if rule_id < vec_clause.len() {
						println!(
							"[33mTRY[0m {} with {}",
							target.to_string(),
							vec_clause[rule_id].to_string()
						);
						match vec_clause[rule_id].match_target(target.clone(), *id) {
							None => {
								rule_id += 1;
								rule_id_stack.push(rule_id);
								continue;
							}
							Some((mut new_targets, instmap, new_id)) => {
								rule_id_stack.push(rule_id);
								println!("[32mWITH[0m {}", instmap_to_string(&instmap));
								let mut targets_copy = targets_stack.last().unwrap().clone();
								targets_copy.pop_front().unwrap();
								id_stack.push(new_id);
								for target in targets_copy.iter_mut() {
									*target = target.instantiate(&instmap);
								}
								new_targets.extend(targets_copy);
								if new_targets.is_empty() {
									println!("[32mCLEAR[0m");
									return ProveResult::Succeed;
								}
								target = new_targets.iter().next().unwrap().clone();
								targets_stack.push(new_targets);
								rule_id_stack.push(0);
								continue;
							}
						}
					}
				}
			}
			println!("[31mFAIL[0m");
			// current stack element fail
			targets_stack.pop().unwrap();
			// println!("{} {}", targets_stack.len(), rule_id_stack.len());
			match targets_stack.last() {
				None => {
					if depth_flag {
						return ProveResult::DepthExceed;
					} else {
						return ProveResult::Fail;
					}
				}
				Some(targets) => target = targets.iter().next().unwrap().clone(),
			}
			*rule_id_stack.last_mut().unwrap() += 1;
			id_stack.pop();
		}
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	#[timeout(1000)]
	fn simple_prove() {
		let theory = Theory::from_string(
			"parent(X, Y) :- father(X, Y).
		father(a, b).
		goal() :- parent(a, b).
		",
		);
		match theory.prove(32) {
			ProveResult::Succeed => {}
			_ => panic!("Result not match!"),
		}
		let theory = Theory::from_string(
			"parent(X, Y) :- father(X, Y).
		father(a, b).
		goal() :- parent(b, a).
		",
		);
		assert_eq!(theory.prove(32), ProveResult::Fail);
	}

	#[test]
	#[timeout(1000)]
	fn prove_addition() {
		let theory = Theory::from_string(
			"add(s(X), Y, s(Z)) :- add(X, Y, Z).
		add(zero, X, X).
		goal() :- add(s(s(zero)), s(s(s(zero))), Answer).
		",
		);
		match theory.prove(32) {
			ProveResult::Succeed => {}
			_ => panic!("Result not match!"),
		}
		let theory = Theory::from_string(
			"add(s(X), Y, s(Z)) :- add(X, Y, Z).
		add(X, zero, X).
		goal() :- add(s(s(zero)), s(s(s(zero))), Answer).
		",
		);
		assert_eq!(theory.prove(32), ProveResult::Fail);
		let theory = Theory::from_string(
			"add(s(X), Y, s(Z)) :- add(X, Y, Z).
		add(zero, X, X).
		goal() :- add(Answer, s(s(s(zero))), s(s(zero))).
		",
		);
		assert_eq!(theory.prove(32), ProveResult::Fail);
	}

	#[test]
	#[timeout(1000)]
	fn prove_partial_order() {
		let theory = Theory::from_string(
			"greater(two, one).
		greater(three, two).
		greater(A, C) :- greater(A, B), greater(B, C).
		goal() :- greater(three, one).
		",
		);
		match theory.prove(32) {
			ProveResult::Succeed => {}
			_ => panic!("Result not match!"),
		}
		let theory = Theory::from_string(
			"greater(two, one).
		greater(three, two).
		greater(A, C) :- greater(A, B), greater(B, C).
		goal() :- greater(one, three).
		",
		);
		assert_eq!(theory.prove(32), ProveResult::DepthExceed);
	}
}
