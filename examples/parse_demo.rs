use fp_sls::parsing::parse::{get_var_info, prepare_formula};
use fp_sls::parsing::reader::read_file;

fn main() {
    let path = std::env::args().nth(1).expect("usage: parse_demo <file.smt2>");
    let cmds = read_file(&path).expect("read");
    let info = get_var_info(&cmds);
    let formula = prepare_formula(&cmds);
    println!("vars ({}):", info.len());
    let mut keys: Vec<_> = info.iter().collect();
    keys.sort_by_key(|(k, _)| (*k).clone());
    for (k, t) in keys {
        println!("  {k} : {t}");
    }
    println!("\nformula:\n{formula}");
}
