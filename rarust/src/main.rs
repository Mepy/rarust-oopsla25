use std::fs;
use std::fs::OpenOptions;

mod printer;
mod llbc;
mod scc;
mod rich_type;
mod enrich;
#[macro_use] mod lp;
mod functions;
mod typ_ctx;
mod typing;
mod subtyping;

use llbc::LLBC;
use serde::Deserialize;
use printer::Printer;

fn main() -> std::io::Result<()> { 
    let llbc_path = std::env::args().nth(1).expect("llbc_path");
    let result_path = std::env::args().nth(2).expect("result_path");

    let llbc_json = fs::read_to_string(llbc_path)?;
    let mut reader = serde_json::Deserializer::from_str(&llbc_json);
    reader.disable_recursion_limit();
    let reader = serde_stacker::Deserializer::new(&mut reader);
    let llbc : LLBC = LLBC::deserialize(reader)?;

    let file = OpenOptions::new().create(true).read(true).write(true).open(result_path)?;
    let printer = Printer::new(file); 
    llbc.handle(printer);


    Ok(())
}