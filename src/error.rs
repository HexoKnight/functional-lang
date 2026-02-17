use annotate_snippets::{Annotation, AnnotationKind, Group, Renderer, Snippet};

use crate::{
    evaluation::EvaluationError,
    parsing::ParseError,
    reprs::common::{FileInfo, Span},
    typing::TypeCheckError,
    validation::ValidationError,
};

pub enum CompilationError<'i> {
    Parse(ParseError<'i>),
    Validation(ValidationError<'i>),
    TypeCheck(TypeCheckError<'i>),
    Evaluation(EvaluationError),
}

impl<'i> From<ParseError<'i>> for CompilationError<'i> {
    fn from(value: ParseError<'i>) -> Self {
        Self::Parse(value)
    }
}

impl<'i> From<ValidationError<'i>> for CompilationError<'i> {
    fn from(value: ValidationError<'i>) -> Self {
        Self::Validation(value)
    }
}

impl<'i> From<TypeCheckError<'i>> for CompilationError<'i> {
    fn from(value: TypeCheckError<'i>) -> Self {
        Self::TypeCheck(value)
    }
}

impl From<EvaluationError> for CompilationError<'_> {
    fn from(value: EvaluationError) -> Self {
        Self::Evaluation(value)
    }
}

impl<'i> RenderError<'i> for CompilationError<'i> {
    fn push_groups(self, buf: &mut Vec<Group<'i>>) {
        match self {
            Self::Parse(err) => err.push_groups(buf),
            Self::Validation(err) => err.push_groups(buf),
            Self::TypeCheck(err) => err.push_groups(buf),
            Self::Evaluation(err) => err.push_groups(buf),
        }
    }
}

impl CompilationError<'_> {
    pub fn render_styled(self) -> String {
        Renderer::styled().render(&self.into_record())
    }
}

pub trait RenderError<'i>: Sized {
    /// push groups in reverse order (for simplicity)
    fn push_groups(self, buf: &mut Vec<Group<'i>>);

    fn into_record(self) -> Vec<Group<'i>> {
        let mut buf = Vec::new();
        self.push_groups(&mut buf);
        // we collect groups backwards so we reverse it here
        buf.reverse();
        buf
    }
}

impl<'i> FileInfo<'i> {
    pub(super) fn snippet<T: Clone>(&'i self) -> Snippet<'i, T> {
        Snippet::source(self.text()).path(self.name())
    }
}

impl<'i> Span<'i> {
    pub(super) fn annotation(self, kind: AnnotationKind) -> Annotation<'i> {
        kind.span(self.range())
    }

    pub(super) fn snippet<T: Clone>(self) -> Snippet<'i, T> {
        self.file_info().snippet()
    }
}
