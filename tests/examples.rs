use include_dir::{Dir, File, include_dir};

use functional_lang::{error::CompilationError, evaluation, parsing, typing, validation};

use crate::common::render_error;

mod common;

const EXAMPLES_DIR_PATH: &str = "examples";
const EXAMPLES_DIR: Dir = include_dir!("$CARGO_MANIFEST_DIR/examples");

fn info<E>(info: impl std::fmt::Display) -> impl FnOnce(E) -> String
where
    E: std::fmt::Display,
{
    move |e| format!("{info}:\n{e}")
}

fn run_input<'i>(input: &'i str) -> Result<(String, String), CompilationError<'i>> {
    let ast = parsing::Parser::default().parse(input)?;
    let untyped_ir = validation::validate(&ast)?;

    let (typed_ir, ty) = typing::type_check(&untyped_ir).map_err(info("type check failure"))?;

    let value = evaluation::evaluate(&typed_ir)?;

    Ok((format!("{value:?}"), ty))
}

fn run_file<'i>(file: &'_ File<'i>) -> Result<(String, String), String> {
    let content = std::str::from_utf8(file.contents()).map_err(info(""))?;

    run_input(content).map_err(|e| {
        render_error(
            e,
            content,
            &[
                EXAMPLES_DIR_PATH,
                file.path()
                    .as_os_str()
                    .to_str()
                    .expect("path in File is a &str"),
            ]
            .join("/"),
        )
    })
}

#[test]
fn run_examples() {
    for file in EXAMPLES_DIR.files() {
        let file_path = file.path().to_string_lossy();
        let (value, ty) = run_file(file)
            .map_err(info(format!("error evaluating {file_path}")))
            .unwrap_or_else(|e| panic!("{e}"));
        println!("{file_path} produced the value:\n{value}\nwith type:\n{ty}",);
    }
}
