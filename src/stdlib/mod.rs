use std::path::Path;

use include_dir::{Dir, include_dir};

use crate::reprs::common::ImportError;

const STDLIB_DIR: Dir = include_dir!("$CARGO_MANIFEST_DIR/stdlib");

pub fn resolve_std_import(path: impl AsRef<Path>) -> Result<&'static str, ImportError> {
    let file = STDLIB_DIR
        .get_file(&path)
        .ok_or_else(|| ImportError::Path(format!("path not found: {:?}", path.as_ref())))?;

    Ok(file.contents_utf8().expect("std files should be utf8"))
}
