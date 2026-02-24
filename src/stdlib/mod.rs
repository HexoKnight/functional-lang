use include_dir::{Dir, include_dir};
use typed_path::Utf8UnixPath;

use crate::importing::ImportError;

const STDLIB_DIR: Dir = include_dir!("$CARGO_MANIFEST_DIR/stdlib");

pub fn resolve_std_import(path: impl AsRef<Utf8UnixPath>) -> Result<&'static str, ImportError> {
    let path = path.as_ref();

    let file = STDLIB_DIR
        .get_file(
            &path
                .with_platform_encoding_checked()
                .map_err(|err| ImportError::Path(format!("{err}: '{path}'")))?,
        )
        .ok_or_else(|| ImportError::Path(format!("std path not found: '{path}'")))?;

    Ok(file.contents_utf8().expect("std files should be utf8"))
}
