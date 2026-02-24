use include_dir::{Dir, File, include_dir};
use itertools::Itertools;
use typed_arena::Arena;
use typed_path::Utf8UnixPath;

use functional_lang::{
    error::CompilationError,
    evaluation,
    importing::{GenericImportHandler, ImportError, ImportHandlerImpl},
    pipeline::Pipeline,
    reprs::common::FileInfo,
    stdlib::resolve_std_import,
    typing,
};

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

fn file_path<'a>(file: &'_ File<'a>) -> &'a str {
    file.path()
        .to_str()
        .expect("`File.path` is a &str internally")
}

fn example_file_info<'i>(path: &str, text: &'i str) -> FileInfo<'i> {
    FileInfo::new([EXAMPLES_DIR_PATH, path].join("/"), text)
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

            let file = EXAMPLES_DIR.get_file(&platform_path).ok_or_else(|| {
                ImportError::Path(format!(
                    "path not found: '{platform_path}'\nfound paths:\n  {}",
                    EXAMPLES_DIR.files().map(file_path).join("\n  ")
                ))
            })?;
            let text = std::str::from_utf8(file.contents())
                .map_err(|err| ImportError::Other(err.to_string()))?;

            Ok(example_file_info(full_path.as_str(), text))
        }
    }
}

fn run_input<'i>(
    file: &'i File<'i>,
    file_info_arena: &'i Arena<FileInfo<'i>>,
) -> Result<(String, String), CompilationError<'i>> {
    let pipeline = Pipeline::default();

    let full_path = file
        .path()
        .as_os_str()
        .to_str()
        .expect("path in File is a &str");

    let (initial, file_info, mut importer) = GenericImportHandler::new(
        ImportHandler,
        full_path,
        example_file_info(
            full_path,
            file.contents_utf8().expect("example file should be utf8"),
        ),
        file_info_arena,
    );

    let untyped_irs = pipeline.validate_rec(initial, file_info, &mut importer)?;

    let mut imports = typing::type_check(untyped_irs.iter().map(|(import_id, i)| (*import_id, i)))?;

    let (main_import_id, typed_ir, ty) = imports.pop().expect("at least one ir should be present");
    debug_assert_eq!(main_import_id, initial);

    let value = evaluation::evaluate(
        &typed_ir,
        imports
            .iter()
            .map(|(import_id, typed_ir, _)| (*import_id, typed_ir)),
    )?;

    Ok((format!("{value:?}"), ty))
}

fn run_file<'i>(file: &'_ File<'i>) -> Result<(String, String), String> {
    run_input(file, &Arena::new()).map_err(render_error)
}

#[test]
fn run_examples() {
    for file in EXAMPLES_DIR.files() {
        let file_path = file.path().to_string_lossy();
        let (value, ty) = run_file(file)
            .map_err(info(format!("error evaluating '{file_path}'")))
            .unwrap_or_else(|e| panic!("{e}"));
        println!("{file_path} produced the value:\n{value}\nwith type:\n{ty}",);
    }
}
