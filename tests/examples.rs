use std::collections::HashMap;

use include_dir::{Dir, File, include_dir};
use typed_arena::Arena;
use typed_path::{Utf8Path, Utf8PlatformPathBuf, Utf8UnixPath, Utf8UnixPathBuf};

use functional_lang::{
    error::CompilationError,
    evaluation,
    pipeline::Pipeline,
    reprs::common::{FileInfo, ImportError, ImportId, ImportResolver, Importer},
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

fn get_parent(path: Utf8PlatformPathBuf) -> Utf8PlatformPathBuf {
    path.parent().map(Utf8Path::to_path_buf).unwrap_or(path)
}

type ImportInfo<'i> = (Option<&'i str>, Utf8PlatformPathBuf, &'i FileInfo<'i>);
type Imports<'i> = HashMap<ImportId, ImportInfo<'i>>;

fn find_import<'i, 'a>(
    imports: &'a Imports<'i>,
    name: impl for<'s> PartialEq<&'s str>,
) -> Option<ImportId> {
    imports
        .iter()
        .find_map(|(import_id, (_, _, file_info))| (name == file_info.name()).then_some(*import_id))
}

fn get_import<'i, 'a>(
    imports: &'a Imports<'i>,
    import_id: ImportId,
) -> Result<&'a ImportInfo<'i>, ImportError> {
    imports.get(&import_id).ok_or_else(|| {
        ImportError::Other("import from within an as yet unimported file".to_string())
    })
}

fn new_file_info<'i>(path: &str, text: &'i str) -> FileInfo<'i> {
    FileInfo::new([EXAMPLES_DIR_PATH, path].join("/"), text)
}

enum ImportType<'i> {
    Package(&'i str),
    Relative(ImportId),
}

struct ImportHandler<'i> {
    imports: Imports<'i>,
    file_info_arena: &'i Arena<FileInfo<'i>>,
}

impl<'i> ImportHandler<'i> {
    fn resolve_import(
        &mut self,
        import_type: ImportType<'i>,
        path: &str,
    ) -> Result<ImportId, ImportError> {
        let path = Utf8UnixPath::new(path);
        if !path.is_valid() {
            return Err(ImportError::Path(format!("path is not valid: '{path}'")));
        }
        if !path.is_relative() {
            return Err(ImportError::Path(format!("path is not relative: '{path}'")));
        }

        let path = path
            .with_platform_encoding_checked()
            .map_err(|err| ImportError::Path(err.to_string()))?;

        let (package, path) = {
            match import_type {
                ImportType::Package(package) => {
                    let mut full_name = Utf8UnixPathBuf::new();
                    full_name.push_checked(format!("@{package}"));
                    full_name.push_checked(&path);
                    (Some(package), full_name)
                }
                ImportType::Relative(current) => {
                    let (current_package, current_dir, _) = get_import(&self.imports, current)?;

                    (
                        *current_package,
                        current_dir
                            .join_checked(path)
                            .map_err(|err| ImportError::Path(err.to_string()))?
                            .normalize(),
                    )
                }
            }
        };

        if let Some(import_id) = find_import(&self.imports, &path) {
            return Ok(import_id);
        }
        let text = {
            let file = EXAMPLES_DIR.get_file(&path).ok_or_else(|| {
                ImportError::Path(format!(
                    "path not found: {}\n{:#?}",
                    path,
                    EXAMPLES_DIR.entries()
                ))
            })?;
            std::str::from_utf8(file.contents())
                .map_err(|err| ImportError::Other(err.to_string()))?
        };

        let file_info = new_file_info(path.as_str(), text);

        let import_dir = get_parent(path);

        let import_id = ImportId(self.imports.len());

        self.imports.insert(
            import_id,
            (None, import_dir, self.file_info_arena.alloc(file_info)),
        );

        Ok(import_id)
    }
}

impl<'i> ImportResolver for ImportHandler<'i> {
    fn resolve_relative(&mut self, current: ImportId, path: &str) -> Result<ImportId, ImportError> {
        let path = Utf8UnixPath::new(path);
        if !path.is_valid() {
            return Err(ImportError::Path(format!("path is not valid: '{path}'")));
        }
        if !path.is_relative() {
            return Err(ImportError::Path(format!("path is not relative: '{path}'")));
        }

        let path = path
            .with_platform_encoding_checked()
            .map_err(|err| ImportError::Path(err.to_string()))?;

        let (current_package, current_dir, _) = get_import(&self.imports, current)?;

        if let Some(current_package) = current_package {}

        let path = current_dir
            .join_checked(path)
            .map_err(|err| ImportError::Path(err.to_string()))?
            .normalize();

        if let Some(import_id) = find_import(&self.imports, &path) {
            return Ok(import_id);
        }

        let file = EXAMPLES_DIR.get_file(&path).ok_or_else(|| {
            ImportError::Path(format!(
                "path not found: {}\n{:#?}",
                path,
                EXAMPLES_DIR.entries()
            ))
        })?;
        let text = std::str::from_utf8(file.contents())
            .map_err(|err| ImportError::Other(err.to_string()))?;

        let file_info = new_file_info(path.as_str(), text);

        let import_dir = get_parent(path);

        let import_id = ImportId(self.imports.len());

        self.imports.insert(
            import_id,
            (None, import_dir, self.file_info_arena.alloc(file_info)),
        );

        Ok(import_id)
    }

    fn resolve_package(&mut self, package: &str, path: &str) -> Result<ImportId, ImportError> {
        let full_name = format!("@{package}/{path}");

        if let Some(import_id) = find_import(&self.imports, &full_name) {
            return Ok(import_id);
        }

        let "std" = package else {
            return Err(ImportError::Package(
                "only the stdlib module 'std' is supported".to_string(),
            ));
        };

        let text = resolve_std_import(path)?;

        let file_info = new_file_info(path, text);

        let import_dir = get_parent(path);
    }
}

impl<'i> Importer<'i> for ImportHandler<'i> {
    fn read(&self, import_id: ImportId) -> Result<&'i FileInfo<'i>, ImportError> {
        get_import(&self.imports, import_id).map(|(_, _, file_info)| *file_info)
    }
}

fn run_input<'i>(
    file: &'i File<'i>,
    file_info_arena: &'i Arena<FileInfo<'i>>,
) -> Result<(String, String), CompilationError<'i>> {
    let pipeline = Pipeline::default();

    let initial = ImportId(0);
    let initial_path = file
        .path()
        .as_os_str()
        .to_str()
        .expect("path in File is a &str");
    let file_info = &*file_info_arena.alloc(new_file_info(
        initial_path,
        file.contents_utf8().expect("example file should be utf8"),
    ));

    let mut imports = HashMap::new();
    imports.insert(
        initial,
        (
            None,
            get_parent(Utf8PlatformPathBuf::from(initial_path)),
            file_info,
        ),
    );

    let mut importer = ImportHandler {
        imports,
        file_info_arena,
    };

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
            .map_err(info(format!("error evaluating {file_path}")))
            .unwrap_or_else(|e| panic!("{e}"));
        println!("{file_path} produced the value:\n{value}\nwith type:\n{ty}",);
    }
}
