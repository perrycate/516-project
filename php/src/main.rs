extern crate z3;
mod php;

use std::env;

fn main() {
    let args: Vec<_> = env::args().collect();
    assert!(args.len() == 2, "Usage: cargo run n");
    let n: u64 = args[1].parse().unwrap();
    println!("{}", n);
    println!("---");
    println!("Solving PHP for {} pigeons and {} holes", n + 1, n);
    match php::solve_php(n) {
        None => {
            println!("The solver says: unsat");
        }
        Some(v) => {
            println!("The solver says: sat");
            println!(
                "[{}]",
                v.iter()
                    .enumerate()
                    .map(|(i, x)| format!("x_{} = {}", i, *x))
                    .collect::<Vec<_>>()
                    .join(",")
            );
        }
    }
}
