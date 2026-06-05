use fp_sls::parsing::parse::get_var_info;
use fp_sls::parsing::reader::read_file;
use fp_sls::z3;

fn main() {
    let path = std::env::args().nth(1).expect("usage: z3_demo <file.smt2>");
    let cmds = read_file(&path).expect("read");
    let var_info = get_var_info(&cmds);
    match z3::get_real_model(&cmds, &var_info) {
        Some(model) => {
            println!("real model parsed ({} vars):", model.len());
            let mut keys: Vec<_> = model.keys().collect();
            keys.sort();
            for k in keys {
                println!("  {k} = {:?}", model[k]);
            }
        }
        None => println!("no real model (unsat relaxation or parse failure)"),
    }
    match z3::eliminate_eqs(&path) {
        Ok(p) => {
            println!("\nelim-eqs produced: {}", p.display());
            print!("{}", std::fs::read_to_string(&p).unwrap_or_default());
        }
        Err(e) => println!("elim-eqs error: {e}"),
    }
}
