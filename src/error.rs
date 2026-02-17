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

impl<'i> CompilationError<'i> {
    pub fn into_record(self) -> Vec<Group<'i>> {
        match self {
            Self::Parse(parse_error) => parse_error.into_record(),
            Self::Validation(validation_error) => validation_error.into_record(),
            Self::TypeCheck(type_check_error) => type_check_error.into_record(),
            Self::Evaluation(evaluation_error) => evaluation_error.into_record(),
        }
    }

    pub fn render_styled(self) -> String {
        Renderer::styled().render(&self.into_record())
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
