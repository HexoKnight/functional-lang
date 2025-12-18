use std::{io::Read, process::ExitCode};

use clap::{Parser, Subcommand};
use clio::Input;

use functional_lang as fl;

#[derive(Parser)]
#[command(
    version,
    about, long_about = None,
    disable_help_subcommand = true
)]
struct Cli {
    /// Source file to use.
    #[arg(default_value = "-")]
    source_file: Input,

    #[command(subcommand)]
    subcommands: Subcommands,
}

#[derive(Subcommand)]
enum Subcommands {
    /// Parse source, displaying a representation on stdout
    Parse,
    /// Parse and validate source, displaying a representation on stdout
    Validate,
    /// Parse, validate and type-check source, displaying a representation on stdout
    TypeCheck,
    /// Parse, validate, type-check and evalutate source, displaying the output on stdout
    Evaluate,
}

fn parse(input: &str) -> Result<fl::reprs::ast::Term<'_>, String> {
    let parser = fl::parsing::Parser::new();
    parser.parse(input).map_err(|e| format!("parse error: {e}"))
}

fn validate(input: &str) -> Result<fl::reprs::untyped_ir::Term<'_>, String> {
    let ast = parse(input)?;
    fl::validation::validate(&ast).map_err(|e| format!("validation error: {e}"))
}

fn type_check(input: &str) -> Result<(fl::reprs::typed_ir::Term<'_>, String), String> {
    let untyped_ir = validate(input)?;
    fl::typing::type_check(&untyped_ir).map_err(|e| format!("typing error: {e}"))
}

fn evaluate(input: &str) -> Result<(), String> {
    let typed_ir = type_check(input)?;
    todo!()
}

fn program() -> Result<(), String> {
    let mut cli = Cli::parse();

    let mut input = String::new();
    cli.source_file
        .read_to_string(&mut input)
        .map_err(|e| format!("failed to read input:\n{e}"))?;

    match cli.subcommands {
        Subcommands::Parse => println!("{:#?}", parse(&input)?),
        Subcommands::Validate => println!("{:#?}", validate(&input)?),
        Subcommands::TypeCheck => println!("{:#?}", type_check(&input)?),
        Subcommands::Evaluate => println!("{:#?}", evaluate(&input)?),
    }
    Ok(())
}

fn main() -> ExitCode {
    match program() {
        Ok(()) => ExitCode::SUCCESS,
        Err(e) => {
            eprintln!("{e}");
            ExitCode::FAILURE
        }
    }
}
