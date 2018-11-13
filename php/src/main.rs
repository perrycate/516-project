extern crate z3;
mod php;

use std::env;

fn main() {
    let args: Vec<_> = env::args().collect();
    assert!(args.len() == 2, "Usage: cargo run n");
    let n: i32 = args[1].parse().unwrap();
    println!("{}", n);
    php::solve_php();
}
