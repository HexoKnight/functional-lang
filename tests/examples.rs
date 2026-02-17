use std::collections::HashMap;

use include_dir::{Dir, File, include_dir};
use typed_arena::Arena;
use typed_path::{Utf8Path, Utf8PlatformPathBuf, Utf8UnixPath};

use functional_lang::{
    error::CompilationError,
    evaluation,
    pipeline::Pipeline,
    reprs::common::{FileInfo, ImportId, ImportResolver, Importer},
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

fn get_import<'i, 'a>(
    imports: &'a HashMap<ImportId, (Utf8PlatformPathBuf, &'i FileInfo<'i>)>,
    import_id: ImportId,
) -> Result<&'a (Utf8PlatformPathBuf, &'i FileInfo<'i>), String> {
    imports
        .get(&import_id)
        .ok_or_else(|| "import from within an as yet unimported file".to_string())
}

fn new_file_info<'i>(path: &str, text: &'i str) -> FileInfo<'i> {
    FileInfo::new([EXAMPLES_DIR_PATH, path].join("/"), text)
}

struct ImportHandler<'i> {
    imports: HashMap<ImportId, (Utf8PlatformPathBuf, &'i FileInfo<'i>)>,
    file_info_arena: &'i Arena<FileInfo<'i>>,
}

impl<'i> ImportResolver for ImportHandler<'i> {
    fn resolve(&mut self, current: ImportId, path: &str) -> Result<ImportId, String> {
        let path = Utf8UnixPath::new(path);
        if !path.is_valid() {
            return Err(format!("path is not valid: '{path}'"));
        }
        if !path.is_relative() {
            return Err(format!("path is not relative: '{path}'"));
        }

        let path = path
            .with_platform_encoding_checked()
            .map_err(|err| err.to_string())?;

        let path = {
            let (current_dir, _) = get_import(&self.imports, current)?;

            current_dir
                .join_checked(path)
                .map_err(|err| err.to_string())?
                .normalize()
        };

        if let Some(import_id) = self.imports.iter().find_map(|(import_id, (_, file_info))| {
            (file_info.name() == path).then_some(*import_id)
        }) {
            return Ok(import_id);
        }

        let file = EXAMPLES_DIR
            .get_file(&path)
            .ok_or_else(|| format!("path not found: {}\n{:#?}", path, EXAMPLES_DIR.entries()))?;

        let file_info = new_file_info(
            path.as_str(),
            std::str::from_utf8(file.contents()).map_err(|err| err.to_string())?,
        );

        let import_dir = get_parent(path);

        let import_id = ImportId(self.imports.len());

        self.imports.insert(
            import_id,
            (import_dir, self.file_info_arena.alloc(file_info)),
        );

        Ok(import_id)
    }
}

impl<'i> Importer<'i> for ImportHandler<'i> {
    fn read(&self, import_id: ImportId) -> Result<&'i FileInfo<'i>, String> {
        get_import(&self.imports, import_id).map(|(_, file_info)| *file_info)
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
