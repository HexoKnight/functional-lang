use std::{io::Read, process::ExitCode};

use clap::{Parser, Subcommand};
use clio::Input;

use functional_lang::{
    error::CompilationError,
    evaluation, parsing,
    reprs::{self},
    typing, validation,
};

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
    /// Parse, validate, type-check and evaluate source, displaying the output on stdout
    Evaluate,
}

fn parse<'i>(input: &'i str) -> Result<reprs::ast::Term<'i>, CompilationError<'i>> {
    let parser = parsing::Parser::default();
    parser.parse(input).map_err(Into::into)
}

fn validate<'i>(input: &'i str) -> Result<reprs::untyped_ir::Term<'i>, CompilationError<'i>> {
    let ast = parse(input)?;
    validation::validate(&ast).map_err(Into::into)
}

fn type_check<'i>(
    input: &'i str,
) -> Result<(reprs::typed_ir::Term<'i>, String), CompilationError<'i>> {
    let untyped_ir = validate(input)?;
    typing::type_check(&untyped_ir).map_err(Into::into)
}

fn evaluate<'i>(
    input: &'i str,
) -> Result<(reprs::value::Value<'i, ()>, String), CompilationError<'i>> {
    let (typed_ir, ty) = type_check(input)?;

    let value = evaluation::evaluate(&typed_ir)?;
    Ok((value, ty))
}

fn program() -> Result<(), String> {
    let mut cli = Cli::parse();

    let mut input = String::new();
    cli.source_file
        .read_to_string(&mut input)
        .map_err(|e| format!("failed to read input:\n{e}"))?;

    let origin = cli.source_file.to_string();

    let result = match cli.subcommands {
        Subcommands::Parse => parse(&input).map(|ast| format!("{ast:#?}")),
        Subcommands::Validate => validate(&input).map(|uir| format!("{uir:#?}")),
        Subcommands::TypeCheck => type_check(&input).map(|(tir, ty)| format!("{tir:#?}\n{ty}")),
        Subcommands::Evaluate => evaluate(&input).map(|(val, ty)| format!("{val:#?}\n{ty}")),
    };

    match result {
        Ok(res) => println!("{res}"),
        Err(err) => println!("{}", err.render_styled(&input, &origin)),
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
