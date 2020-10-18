extern crate myprolog2;
extern crate rustyline;

use myprolog2::theory::Theory;
use rustyline::error::ReadlineError;
use rustyline::Editor;

fn main() {
	let axiom = include_str!("number");
	let mut theory: Theory = Default::default();
	theory.add_string(&axiom);
	theory.display();
	let mut rl = Editor::<()>::new();
	loop {
		let readline = rl.readline("[31m>[0m ");
		let line = match readline {
			Ok(line) => {
				rl.add_history_entry(line.as_str());
				line
			}
			Err(ReadlineError::Interrupted) => {
				println!("CTRL-C");
				break;
			}
			Err(ReadlineError::Eof) => {
				println!("CTRL-D");
				break;
			}
			Err(err) => {
				println!("Error: {:?}", err);
				break;
			}
		};
		let mut state = true;
		let mut s = "goal() :- ".to_string();
		for each_item in line.split_whitespace() {
			if state {
				s += &format!("{}(", each_item);
				state = false;
			} else {
				let mut num = match each_item.parse::<u32>() {
					Err(_) => {
						println!("Parse failed at ident {}", state);
						continue;
					}
					Ok(id) => id,
				};
				let mut rb = 0;
				while num > 0 {
					s = format!("{} number(d{}, ", s, num % 10);
					num /= 10;
					rb += 1;
				}
				s += "h)";
				for _ in 1..rb {
					s += ")";
				}
				s += ","
			}
		}
		s.pop();
		s += ").";
		println!("{}", s);
		let mut theory1 = theory.clone();
		theory1.add_string(&s);
		println!("{:?}", theory1.prove(1_000_000));
	}
}
