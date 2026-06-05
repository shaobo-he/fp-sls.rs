//! Measure how compact `Dag::build` is on a real (heavily let-shared) formula:
//!   cargo run --release --example dag_size -- <file.smt2>
//! Reports the input Sexp node count vs. the resulting DAG node count.

use fp_sls::dag::Dag;
use fp_sls::parsing::parse::{get_formula, get_var_info};
use fp_sls::parsing::reader::read_all;
use fp_sls::sexp::Sexp;
use fp_sls::z3;

fn count_iter(root: &Sexp) -> usize {
    let mut n = 0usize;
    let mut stack = vec![root];
    while let Some(s) = stack.pop() {
        n += 1;
        if let Sexp::List(v) = s {
            stack.extend(v.iter());
        }
    }
    n
}

fn main() {
    let path = std::env::args().nth(1).expect("usage: dag_size <file.smt2>");
    let simplified = z3::simplify_jfs(&path).expect("z3 simplify");
    let content = std::fs::read_to_string(&simplified).expect("read simplified");
    let cmds = read_all(&content);
    let var_info = get_var_info(&cmds);
    let formula = get_formula(&cmds);
    let sexp_nodes = count_iter(&formula);

    // Deeply-nested formulas overflow the default stack during the recursive
    // build; give it a big stack.
    let handle = std::thread::Builder::new()
        .stack_size(1 << 30)
        .spawn(move || {
            let dag = Dag::build(&formula, &var_info);
            (dag.num_nodes(), dag.vars().len(), dag.num_asserts())
        })
        .unwrap();
    let (dag_nodes, vars, asserts) = handle.join().expect("build");

    println!("sexp nodes:  {sexp_nodes}");
    println!("dag nodes:   {dag_nodes}");
    println!("vars:        {vars}");
    println!("asserts:     {asserts}");
    println!(
        "compression: {:.1}x  (sexp/dag)",
        sexp_nodes as f64 / dag_nodes.max(1) as f64
    );
}
