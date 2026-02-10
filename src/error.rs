use annotate_snippets::{Group, Renderer};

use crate::{
    evaluation::EvaluationError, parsing::ParseError, typing::TypeCheckError,
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
    pub fn into_record(self, source: &'i str, origin: &'i str) -> Vec<Group<'i>> {
        match self {
            Self::Parse(parse_error) => parse_error.into_record(source, origin),
            Self::Validation(validation_error) => validation_error.into_record(source, origin),
            Self::TypeCheck(type_check_error) => type_check_error.into_record(source, origin),
            Self::Evaluation(evaluation_error) => evaluation_error.into_record(),
        }
    }

    pub fn render_styled(self, source: &'i str, origin: &'i str) -> String {
        Renderer::styled().render(&self.into_record(source, origin))
    }
}
