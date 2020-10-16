use std::collections::HashMap;

use crate::clause::Clause;

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
