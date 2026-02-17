use annotate_snippets::{Group, Level, Renderer};

use functional_lang::error::RenderError;

pub fn render_error<'i>(error: impl RenderError<'i>) -> String {
    let mut groups = error.into_record();

    groups.insert(
        0,
        Group::with_title(Level::ERROR.primary_title("aborting due to unexpected error")),
    );

    Renderer::styled().render(&groups)
}
