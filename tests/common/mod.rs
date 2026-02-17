use annotate_snippets::{Group, Level, Renderer};
use functional_lang::error::CompilationError;

pub fn render_error<'i>(error: impl Into<CompilationError<'i>>) -> String {
    let error = error.into();
    let err_type = match &error {
        CompilationError::Parse(_) => "parse",
        CompilationError::Validation(_) => "validation",
        CompilationError::TypeCheck(_) => "type-check",
        CompilationError::Evaluation(_) => "evaluation",
    };

    let mut groups = error.into_record();

    groups.insert(
        0,
        Group::with_title(Level::ERROR.primary_title(format!("aborting due to {err_type} error"))),
    );

    Renderer::styled().render(&groups)
}
