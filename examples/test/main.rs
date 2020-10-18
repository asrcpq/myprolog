extern crate myprolog2;

use std::io::prelude::*;

use myprolog2::theory::Theory;

fn main() {
	let arg = std::env::args()
		.skip(1)
		.next()
		.unwrap_or("theory".to_string());
	let mut string = "".to_string();
	let f = std::fs::File::open(arg).unwrap();
	let mut f = std::io::BufReader::new(f);
	f.read_to_string(&mut string).unwrap();
	let mut theory:Theory = Default::default();
	theory.add_string(&string);
	theory.display();
	println!("{:?}", theory.prove(1280000));
}
