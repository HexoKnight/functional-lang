use std::{collections::HashMap, iter::once};

use typed_arena::Arena;
use typed_path::{Utf8Path, Utf8UnixPath, Utf8UnixPathBuf};

use crate::reprs::common::FileInfo;

#[derive(Hash, Copy, Clone, Eq, PartialEq, Debug)]
pub struct ImportId(pub usize);

pub trait ImportResolver {
    fn resolve_relative(&mut self, current: ImportId, path: &str) -> Result<ImportId, ImportError>;
    fn resolve_package(&mut self, package: &str, path: &str) -> Result<ImportId, ImportError>;
}

pub trait Importer<'i>: ImportResolver {
    fn read(&self, import_id: ImportId) -> Result<&'i FileInfo<'i>, ImportError>;
}

pub enum ImportError {
    Path(String),
    Package(String),
    Other(String),
}
impl ImportError {
    pub fn into_msg(self) -> String {
        match self {
            ImportError::Path(msg) | ImportError::Package(msg) | ImportError::Other(msg) => msg,
        }
    }
}

struct ImportInfo<'i> {
    package: Option<&'i str>,
    full_path: Utf8UnixPathBuf,
    parent_dir: Utf8UnixPathBuf,
    file_info: &'i FileInfo<'i>,
}
type Imports<'i> = HashMap<ImportId, ImportInfo<'i>>;

fn get_parent(path: Utf8UnixPathBuf) -> Utf8UnixPathBuf {
    path.parent().map(Utf8Path::to_path_buf).unwrap_or(path)
}

fn find_import(imports: &Imports, path: &impl PartialEq<Utf8UnixPathBuf>) -> Option<ImportId> {
    imports
        .iter()
        .find_map(|(import_id, ImportInfo { full_path, .. })| {
            (path == full_path).then_some(*import_id)
        })
}

fn get_import<'i, 'a>(
    imports: &'a Imports<'i>,
    import_id: ImportId,
) -> Result<&'a ImportInfo<'i>, ImportError> {
    imports.get(&import_id).ok_or_else(|| {
        ImportError::Other("import from within an as yet unimported file".to_string())
    })
}

enum ImportType<'i> {
    Package(&'i str),
    Relative(ImportId),
}

pub trait ImportHandlerImpl<'i> {
    fn handle_import(
        &mut self,
        package: Option<&str>,
        path: &Utf8UnixPath,
        full_path: &Utf8UnixPath,
    ) -> Result<FileInfo<'i>, ImportError>;
}

pub struct GenericImportHandler<'i, I: ImportHandlerImpl<'i>> {
    import_handler: I,

    imports: Imports<'i>,
    file_info_arena: &'i Arena<FileInfo<'i>>,
}

impl<'i, I: ImportHandlerImpl<'i>> GenericImportHandler<'i, I> {
    pub fn new(
        import_handler: I,

        initial_full_path: impl Into<Utf8UnixPathBuf>,
        initial_file_info: FileInfo<'i>,
        file_info_arena: &'i Arena<FileInfo<'i>>,
    ) -> (ImportId, &'i FileInfo<'i>, Self) {
        let initial = ImportId(0);
        let file_info = &*file_info_arena.alloc(initial_file_info);
        let full_path = initial_full_path.into();

        (
            initial,
            file_info,
            GenericImportHandler {
                import_handler,
                imports: once((
                    initial,
                    ImportInfo {
                        package: None,
                        parent_dir: get_parent(full_path.clone()),
                        full_path,
                        file_info,
                    },
                ))
                .collect(),
                file_info_arena,
            },
        )
    }

    fn resolve_import(
        &mut self,
        import_type: ImportType<'_>,
        path: &str,
    ) -> Result<ImportId, ImportError> {
        let path = Utf8UnixPath::new(path);
        if !path.is_valid() {
            return Err(ImportError::Path(format!("path is not valid: '{path}'")));
        }
        if !path.is_relative() {
            return Err(ImportError::Path(format!("path is not relative: '{path}'")));
        }

        let (package, full_path) = {
            match import_type {
                ImportType::Package(package) => {
                    let mut full_name = Utf8UnixPathBuf::from(format!("@{package}"));
                    full_name
                        .push_checked(path.normalize())
                        .map_err(|err| ImportError::Path(format!("{err}: '{path}'")))?;
                    (Some(package), full_name)
                }
                ImportType::Relative(current_import_id) => {
                    let ImportInfo {
                        package: current_package,
                        parent_dir: current_dir,
                        ..
                    } = get_import(&self.imports, current_import_id)?;

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

        if let Some(import_id) = find_import(&self.imports, &full_path) {
            return Ok(import_id);
        }

        let file_info = self
            .import_handler
            .handle_import(package, path, &full_path)?;

        let import_dir = get_parent(full_path.clone());

        let import_id = ImportId(self.imports.len());

        self.imports.insert(
            import_id,
            ImportInfo {
                package: None,
                full_path,
                parent_dir: import_dir,
                file_info: self.file_info_arena.alloc(file_info),
            },
        );

        Ok(import_id)
    }
}

impl<'i, I: ImportHandlerImpl<'i>> ImportResolver for GenericImportHandler<'i, I> {
    fn resolve_relative(&mut self, current: ImportId, path: &str) -> Result<ImportId, ImportError> {
        self.resolve_import(ImportType::Relative(current), path)
    }

    fn resolve_package(&mut self, package: &str, path: &str) -> Result<ImportId, ImportError> {
        self.resolve_import(ImportType::Package(package), path)
    }
}

impl<'i, I: ImportHandlerImpl<'i>> Importer<'i> for GenericImportHandler<'i, I> {
    fn read(&self, import_id: ImportId) -> Result<&'i FileInfo<'i>, ImportError> {
        get_import(&self.imports, import_id).map(|ImportInfo { file_info, .. }| *file_info)
    }
}
