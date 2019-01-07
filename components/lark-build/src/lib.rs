mod build;
mod codegen_c;
mod codegen_rust;

use lark_error::WithError;
use lark_query_system::LarkDatabase;

#[derive(Copy, Clone)]
pub enum CodegenType {
    Rust,
    C,
}

/// Converts the MIR context of definitions into the chosen source type
pub fn codegen(db: &LarkDatabase, codegen_type: CodegenType) -> WithError<String> {
    match codegen_type {
        CodegenType::Rust => codegen_rust::codegen_rust(db),
        CodegenType::C => codegen_c::codegen_c(db),
    }
}

/// Builds source code for the given source type
pub fn build(
    target_filename: &str,
    src: &String,
    codegen_type: CodegenType,
) -> std::io::Result<()> {
    build::build(target_filename, &src, codegen_type)
}
