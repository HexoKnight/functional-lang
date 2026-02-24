use std::{fs::read_to_string, io::Read, process::ExitCode};

use clap::{Parser, ValueEnum};
use clio::Input;

use functional_lang::{
    error::CompilationError,
    importing::{GenericImportHandler, ImportError, ImportHandlerImpl, Importer},
    pipeline::Pipeline,
    reprs::common::FileInfo,
    stdlib::resolve_std_import,
};
use typed_arena::Arena;
use typed_path::Utf8UnixPath;

#[derive(Parser)]
#[command(
    version,
    about, long_about = None,
    disable_help_subcommand = true
)]
struct Cli {
    #[arg(value_enum)]
    operation: Operation,

    /// Source file to use.
    #[arg(default_value = "-")]
    source_file: Input,
}

#[derive(Copy, Clone, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
enum Operation {
    /// Parse source, displaying a representation on stdout
    Parse,
    /// Parse and validate source, displaying a representation on stdout
    Validate,
    /// Parse, validate and type-check source, displaying a representation on stdout
    TypeCheck,
    /// Parse, validate, type-check and evaluate source, displaying the output on stdout
    Evaluate,
}

struct ImportHandler;

impl<'i> ImportHandlerImpl<'i> for ImportHandler {
    fn handle_import(
        &mut self,
        package: Option<&str>,
        path: &Utf8UnixPath,
        full_path: &Utf8UnixPath,
    ) -> Result<FileInfo<'i>, ImportError> {
        if let Some(package) = package {
            let "std" = package else {
                return Err(ImportError::Package(
                    "only the stdlib module 'std' is supported".to_string(),
                ));
            };

            let text = resolve_std_import(path)?;

            Ok(FileInfo::new(full_path.to_string(), text))
        } else {
            let platform_path = full_path
                .with_platform_encoding_checked()
                .map_err(|err| ImportError::Path(format!("{err}: '{full_path}'")))?;

            let text = read_to_string(&platform_path)
                .map_err(|err| ImportError::Path(format!("{err}: '{platform_path}'")))?;

            Ok(FileInfo::new(full_path.to_string(), text))
        }
    }
}

fn run_pipeline<'i>(
    operation: Operation,
    full_path: &str,
    file_info: FileInfo<'i>,
    file_info_arena: &'i Arena<FileInfo<'i>>,
) -> Result<(), CompilationError<'i>> {
    let (initial, file_info, mut importer) =
        GenericImportHandler::new(ImportHandler, full_path, file_info, file_info_arena);

    match operation {
        Operation::Parse => {
            let ast = Pipeline::default().parse_single(file_info)?;
            println!("{ast:#?}");
        }
        Operation::Validate => {
            let uirs = Pipeline::default().validate_rec(initial, file_info, &mut importer)?;
            for (import_id, uir) in uirs {
                println!(
                    "{}:\n{uir:#?}\n",
                    importer
                        .read(import_id)
                        .map_err(ImportError::into_msg)
                        .unwrap()
                        .name()
                );
            }
        }
        Operation::TypeCheck => {
            let tirs = Pipeline::default().type_check_rec(initial, file_info, &mut importer)?;
            for (import_id, tir, ty) in tirs {
                println!(
                    "{}:\n{tir:#?}\n{ty}\n",
                    importer
                        .read(import_id)
                        .map_err(ImportError::into_msg)
                        .unwrap()
                        .name()
                );
            }
        }
        Operation::Evaluate => {
            let (val, ty) = Pipeline::default().evaluate_rec(initial, file_info, &mut importer)?;
            println!("{val:#?}\n{ty}")
        }
    }
    Ok(())
}

fn program() -> Result<(), String> {
    let mut cli = Cli::parse();

    let mut input = String::new();
    cli.source_file
        .read_to_string(&mut input)
        .map_err(|e| format!("failed to read input:\n{e}"))?;

    let full_path = std::str::from_utf8(cli.source_file.path().as_os_str().as_encoded_bytes())
        .map_err(|e| format!("failed to parse source file path: {e}"))?;

    let file_info = FileInfo::new(full_path, input);

    run_pipeline(cli.operation, full_path, file_info, &Arena::new())
        .map_err(CompilationError::render_styled)
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
