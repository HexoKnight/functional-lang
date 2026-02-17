use std::{
    borrow::{Borrow, Cow},
    panic::Location,
};

use annotate_snippets::{AnnotationKind, Group, Level, Origin};

use crate::reprs::common::Span;

#[derive(Clone)]
pub enum TypeCheckError<'i> {
    Illegal(IllegalError<'i>),
    NonTerminalTypeInference,

    Spanned(SpannedError<'i>, Option<Box<ContextError<'i>>>),
}

#[derive(Clone)]
pub struct SpannedError<'i> {
    title: Cow<'i, str>,

    span: Span<'i>,
    span_label: Cow<'i, str>,

    context_spans: Vec<(Span<'i>, Cow<'i, str>)>,

    text: Cow<'i, str>,
}

#[derive(Clone)]
pub struct IllegalError<'i> {
    msg: Cow<'i, str>,
    span: Option<Span<'i>>,

    location: &'static Location<'static>,

    context: Option<Box<ContextError<'i>>>,
}

#[derive(Clone)]
pub enum ContextError<'i> {
    Illegal(IllegalError<'i>),
    NonTerminalTypeInference,

    PlainContext(PlainContextError, Option<Box<IllegalError<'i>>>),
}

#[derive(Clone)]
pub struct PlainContextError {
    text: String,
}

impl<'i> From<IllegalError<'i>> for TypeCheckError<'i> {
    fn from(value: IllegalError<'i>) -> Self {
        Self::Illegal(value)
    }
}
impl<'i> From<SpannedError<'i>> for TypeCheckError<'i> {
    fn from(value: SpannedError<'i>) -> Self {
        Self::Spanned(value, None)
    }
}

impl<'i> From<IllegalError<'i>> for ContextError<'i> {
    fn from(value: IllegalError<'i>) -> Self {
        Self::Illegal(value)
    }
}
impl From<PlainContextError> for ContextError<'_> {
    fn from(value: PlainContextError) -> Self {
        Self::PlainContext(value, None)
    }
}

impl<'i> IllegalError<'i> {
    #[track_caller]
    pub fn new(msg: impl Into<Cow<'i, str>>, span: Option<Span<'i>>) -> Self {
        Self {
            msg: msg.into(),
            span,
            location: Location::caller(),

            context: None,
        }
    }
}

impl<'i> SpannedError<'i> {
    pub fn ty_ty_mismatch(
        expected_ty: impl Into<Cow<'i, str>>,
        found_ty: impl Into<Cow<'i, str>>,
        span: Span<'i>,
    ) -> Self {
        let expected_ty = expected_ty.into();
        let found_ty = found_ty.into();
        Self {
            title: format!("type mismatch: expected `{expected_ty}`").into(),

            span,
            span_label: "".into(),
            context_spans: Vec::new(),

            text: format!(
                "expected: `{expected_ty}`\n\
                found:    `{found_ty}`"
            )
            .into(),
        }
    }

    pub fn ty_mismatch(
        expected_ty: impl Into<Cow<'i, str>>,
        text: impl Into<Cow<'i, str>>,
        span: Span<'i>,
    ) -> Self {
        let expected_ty = expected_ty.into();
        let text = text.into();
        Self {
            title: format!("type mismatch: expected `{expected_ty}`").into(),

            span,
            span_label: "".into(),
            context_spans: Vec::new(),

            text: format!(
                "expected: `{expected_ty}`\n\
                {text}"
            )
            .into(),
        }
    }

    pub fn type_inference(msg: impl Into<Cow<'i, str>>, span: Span<'i>) -> Self {
        let msg = msg.into();
        Self {
            title: format!("type inference error: {msg}").into(),
            span,
            span_label: "".into(),
            context_spans: Vec::new(),
            text: "".into(),
        }
    }

    pub fn new(
        title: impl Into<Cow<'i, str>>,
        text: impl Into<Cow<'i, str>>,
        span_label: impl Into<Cow<'i, str>>,
        span: Span<'i>,
    ) -> Self {
        Self {
            title: title.into(),
            span,
            span_label: span_label.into(),
            context_spans: Vec::new(),
            text: text.into(),
        }
    }

    pub fn with_context<C, L>(
        title: impl Into<Cow<'i, str>>,
        text: impl Into<Cow<'i, str>>,
        span_label: impl Into<Cow<'i, str>>,
        span: Span<'i>,
        context_spans: C,
    ) -> Self
    where
        C: IntoIterator<Item = (Span<'i>, L)>,
        L: Into<Cow<'i, str>>,
    {
        Self {
            title: title.into(),
            span,
            span_label: span_label.into(),
            context_spans: context_spans
                .into_iter()
                .map(|(span, l)| (span, l.into()))
                .collect(),
            text: text.into(),
        }
    }
}

impl PlainContextError {
    pub fn new(text: impl Into<String>) -> Self {
        Self { text: text.into() }
    }
}

impl ContextError<'_> {
    pub(super) fn into_type_inference_err(self) -> Self {
        match self {
            ContextError::Illegal(_) | ContextError::PlainContext(_, Some(_)) => self,
            ContextError::NonTerminalTypeInference | ContextError::PlainContext(_, None) => {
                ContextError::NonTerminalTypeInference
            }
        }
    }
}

impl<'i> IllegalError<'i> {
    fn push_groups(self, buf: &mut Vec<Group<'i>>) {
        let Self {
            msg,
            span,
            location,
            context,
        } = self;

        let group = Level::ERROR
            .primary_title("illegal error (bug)")
            .element(
                Origin::path(location.file())
                    .line(location.line().try_into().expect("not 16-bit arch"))
                    .char_column(location.column().try_into().expect("not 16-bit arch")),
            )
            .elements(span.map(|span| {
                span.snippet()
                    .annotation(span.annotation(AnnotationKind::Primary))
            }))
            .element(Level::ERROR.message(msg))
            .elements(context.map(|context| Level::INFO.message(context.into_context(buf))));
        buf.push(group);
    }
}

impl<'i> TypeCheckError<'i> {
    pub fn into_record(self) -> Vec<Group<'i>> {
        let mut buf = Vec::new();
        self.push_groups(&mut buf);
        // we collect groups backwards so we reverse it here
        buf.reverse();
        buf
    }

    fn push_groups(self, buf: &mut Vec<Group<'i>>) {
        fn if_nonempty<S: Borrow<str>>(str: S) -> Option<S> {
            if str.borrow().is_empty() {
                None
            } else {
                Some(str)
            }
        }

        match self {
            Self::Illegal(err) => err.push_groups(buf),
            Self::NonTerminalTypeInference => {
                IllegalError::new("non terminal type inference error escaped", None)
                    .push_groups(buf);
            }

            Self::Spanned(
                SpannedError {
                    title,
                    span,
                    span_label,
                    context_spans,
                    text,
                },
                context,
            ) => {
                let group = Level::ERROR
                    .primary_title(title)
                    .element(
                        span.snippet().annotation(
                            span.annotation(AnnotationKind::Primary)
                                .label(if_nonempty(span_label)),
                        ),
                    )
                    .elements(context_spans.into_iter().map(|(span, label)| {
                        span.snippet().annotation(
                            span.annotation(AnnotationKind::Context)
                                .label(if_nonempty(label)),
                        )
                    }))
                    .elements(if_nonempty(text).map(|text| Level::ERROR.message(text)))
                    .elements(context.map(|cause| Level::INFO.message(cause.into_context(buf))));
                buf.push(group);
            }
        }
    }
}

impl<'i> ContextError<'i> {
    fn into_context(self, buf: &mut Vec<Group<'i>>) -> String {
        let (context, cause) = match self {
            Self::Illegal(err) => (None, Some(err)),
            Self::NonTerminalTypeInference => (
                None,
                Some(IllegalError::new(
                    "non terminal type inference error escaped",
                    None,
                )),
            ),
            Self::PlainContext(context, cause) => (Some(context), cause.map(|b| *b)),
        };

        let mut context_buf = String::new();
        if let Some(PlainContextError { text }) = context {
            context_buf.push_str(&text);
        }
        if let Some(cause) = cause {
            context_buf.push_str("\nencountered illegal error: ");
            context_buf.push_str(&cause.msg);

            cause.push_groups(buf);
        }
        context_buf
    }
}

pub(super) trait TypeCheckResult<T, E>: Sized {
    fn to_result(self) -> Result<T, E>;

    fn try_wrap_error<F, EI>(self, f: F) -> Result<T, <E as WrapError<EI>>::Result>
    where
        E: WrapError<EI>,
        F: FnOnce() -> Result<EI, <E as WrapError<EI>>::Result>,
    {
        self.to_result()
            .or_else(|prev_err| Err(WrapError::wrap(prev_err, f()?)))
    }

    fn wrap_error<F, EI>(self, f: F) -> Result<T, <E as WrapError<EI>>::Result>
    where
        E: WrapError<EI>,
        F: FnOnce() -> EI,
    {
        self.to_result()
            .map_err(|prev_err| WrapError::wrap(prev_err, f()))
    }
}

impl<T, E> TypeCheckResult<T, E> for Result<T, E> {
    fn to_result(self) -> Result<T, E> {
        self
    }
}

pub trait WrapError<NewInner> {
    type Result;
    fn wrap(prev_err: Self, new_err: NewInner) -> Self::Result;
}

impl<'i> WrapError<SpannedError<'i>> for ContextError<'i> {
    type Result = TypeCheckError<'i>;
    fn wrap(prev_err: Self, new_err: SpannedError<'i>) -> Self::Result {
        if let Self::NonTerminalTypeInference = prev_err {
            Self::Result::NonTerminalTypeInference
        } else {
            Self::Result::Spanned(new_err, Some(Box::new(prev_err)))
        }
    }
}

impl<'i> WrapError<IllegalError<'i>> for ContextError<'i> {
    type Result = IllegalError<'i>;
    fn wrap(prev_err: Self, mut new_err: IllegalError<'i>) -> Self::Result {
        // new_err should be constructed in the `*wrap_error` closure so shouln't be set
        debug_assert!(new_err.context.is_none());
        new_err.context = Some(Box::new(prev_err));
        new_err
    }
}

impl<'i> WrapError<PlainContextError> for IllegalError<'i> {
    type Result = ContextError<'i>;
    fn wrap(prev_err: Self, new_err: PlainContextError) -> Self::Result {
        Self::Result::PlainContext(new_err, Some(Box::new(prev_err)))
    }
}

impl<'i> WrapError<PlainContextError> for ContextError<'i> {
    type Result = ContextError<'i>;
    fn wrap(prev_err: Self, new_err: PlainContextError) -> Self::Result {
        match prev_err {
            Self::Illegal(err) => WrapError::wrap(err, new_err),
            Self::NonTerminalTypeInference => prev_err,
            Self::PlainContext(PlainContextError { mut text }, cause) => {
                let PlainContextError { text: new_text } = new_err;

                text.insert(0, '\n');
                text.insert_str(0, &new_text);

                Self::Result::PlainContext(PlainContextError { text }, cause)
            }
        }
    }
}
