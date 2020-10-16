use std::collections::HashMap;
use ntest::timeout;

use crate::clause::Clause;
use crate::pred::Pred;
use crate::pred::InstMap;
use crate::pred::instmap_merge;

#[derive(Default)]
pub struct Theory {
	clauses: HashMap<String, Vec<Clause>>,
	suffix_alloc_id: u32,
}

#[derive(Debug, PartialEq)]
pub enum ProveResult {
	Succeed(InstMap, u32),
	Fail,
	DepthExceed,
}

impl Theory {
	pub fn from_string(string: &str) -> Theory {
		let mut result: Theory = Default::default();
		let suffix_alloc_id = 0;
		let mut strings = string.split(".").map(|x| x.to_string()).collect::<Vec<String>>();
		strings.pop();
		for clause in strings.into_iter() {
			if clause.is_empty() {
				continue;
			}
			let (new_clause, suffix_alloc_id) = Clause::from_string(&clause, suffix_alloc_id);
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

	pub fn prove_recurse(&self, mut targets: Vec<Pred>, dmax: u32, dnow: u32, mut id: u32) -> ProveResult {
		print!("Targets: ");
		for each_target in targets.iter() {
			print!("{} ", each_target.to_string());
		}
		println!();
		let mut anycutoff = false;
		if dnow > dmax { return ProveResult::DepthExceed }
		let target = match targets.pop() {
			None => return ProveResult::Succeed(HashMap::new(), id),
			Some(target) => target,
		};
		match self.clauses.get(&target.get_name()) {
			None => return ProveResult::Fail,
			Some(vec_clause) => {
				for clause in vec_clause.iter() {
					match clause.match_target(target.clone(), id) {
						None => {},
						Some((new_targets, mut instmap, new_id)) => {
							let mut targets_copy = targets.clone();
							id = new_id;
							for target in targets_copy.iter_mut() {
								*target = target.instantiate(&instmap);
							}
							targets_copy.extend(new_targets);
							match self.prove_recurse(targets_copy, dmax, dnow + 1, id) {
								ProveResult::DepthExceed => anycutoff = true,
								ProveResult::Fail => {}
								ProveResult::Succeed(instmap_ret, id) => {
									instmap.extend(instmap_ret);
									return ProveResult::Succeed(instmap, id)
								}
							}
						}
					}
				}
			}
		}
		// all rules fail
		if anycutoff { return ProveResult::DepthExceed }
		ProveResult::Fail
	}

	pub fn prove(&self) -> ProveResult {
		self.prove_recurse(vec![Pred::vc_from_string("goal".to_string())], 64, 0, self.suffix_alloc_id)
	}
}

#[cfg(test)]
mod test {
	use super::*;

	#[test]
	fn simple_prove() {
		let theory = Theory::from_string("
		parent(X, Y) :- father(X, Y).
		father(a, b).
		goal() :- parent(a, b).
		");
		match theory.prove() {
			ProveResult::Succeed(instmap, _) => {},
			_ => panic!("Result not match!"),
		}
		let theory = Theory::from_string("
		parent(X, Y) :- father(X, Y).
		father(a, b).
		goal() :- parent(b, a).
		");
		assert_eq!(theory.prove(), ProveResult::Fail);
	}

	#[test]
	#[timeout(1000)]
	fn prove_addition() {
		let theory = Theory::from_string("
		add(s(X), Y, s(Z)) :- add(X, Y, Z).
		add(zero, X, X).
		goal() :- add(s(s(zero)), s(s(s(zero))), Answer).
		");
		match theory.prove() {
			ProveResult::Succeed(instmap, _) => {},
			_ => panic!("Result not match!"),
		}
		let theory = Theory::from_string("
		add(s(X), Y, s(Z)) :- add(X, Y, Z).
		add(X, zero, X).
		goal() :- add(s(s(zero)), s(s(s(zero))), Answer).
		");
		assert_eq!(theory.prove(), ProveResult::Fail);
		let theory = Theory::from_string("
		add(s(X), Y, s(Z)) :- add(X, Y, Z).
		add(zero, X, X).
		goal() :- add(Answer, s(s(s(zero))), s(s(zero))).
		");
		assert_eq!(theory.prove(), ProveResult::Fail);
	}
}
