use std::collections::VecDeque;

use hashbrown::HashMap;
use itertools::Itertools;

use crate::{
    common::{WithInfo, toposort},
    error::CompilationError,
    evaluation::evaluate,
    parsing::{ParseError, Parser},
    reprs::{
        ast,
        common::{FileInfo, ImportId, Importer, Span},
        typed_ir, untyped_ir, value,
    },
    typing::type_check,
    validation::{ValidationError, validate},
};

#[derive(Default)]
pub struct Pipeline {
    parser: Parser,
}

impl Pipeline {
    pub fn parse_single<'i>(
        &self,
        file_info: &'i FileInfo<'i>,
    ) -> Result<ast::Term<'i>, ParseError<'i>> {
        self.parser.parse(file_info)
    }

    pub fn validate_rec<'i>(
        &self,
        initial: ImportId,
        initial_file_info: &'i FileInfo<'i>,
        importer: &mut impl Importer<'i>,
    ) -> Result<Vec<(ImportId, untyped_ir::Term<'i>)>, CompilationError<'i>> {
        let mut to_validate = VecDeque::new();
        let mut validated = HashMap::new();
        let mut dependency_graph = HashMap::new();

        let mut handle_source =
            |import_id, file_info, to_validate: &mut VecDeque<_>, importer: &mut _| {
                let ast = self.parse_single(file_info)?;

                let (untyped_ir, dependencies) = validate(import_id, &ast, importer)?;

                validated.insert(import_id, untyped_ir);
                // `VecDeque::extend` pushes to the back
                to_validate.extend(dependencies.iter().filter_map(|(import_id, (path, span))| {
                    (!validated.contains_key(import_id)).then_some((*import_id, (*path, *span)))
                }));

                dependency_graph.insert(
                    import_id,
                    dependencies
                        .into_iter()
                        .map(|(import_id, info)| WithInfo(info, import_id))
                        .collect_vec(),
                );
                Ok::<_, CompilationError>(())
            };

        handle_source(initial, initial_file_info, &mut to_validate, importer)?;

        while let Some((import_id, (path, span))) = to_validate.pop_front() {
            let source = importer
                .read(import_id)
                .map_err(|err| ValidationError::FailedImport {
                    path,
                    info: err.into(),
                    span,
                })?;

            handle_source(import_id, source, &mut to_validate, importer)?;
        }

        // we use `WithInfo` so nodes ignore the info when `Eq`
        // dummy span but this initial_node should never end up in the Err(cycle)
        let initial_node = WithInfo(("", Span::new(initial_file_info, 0..0)), initial);
        let sorted = match toposort(&initial_node, |WithInfo(_, import_id)| {
            dependency_graph
                .get(import_id)
                .expect("all `ImportId`s should be within the dependency graph")
                .iter()
        }) {
            Ok(sorted) => sorted,
            Err((cycle, WithInfo(last_info, _))) => Err(ValidationError::CyclicImport {
                cycle: cycle.into_iter().map(|WithInfo(info, _)| *info).collect(),
                last: *last_info,
            })?,
        };

        let sorted = sorted
            .into_iter()
            .map(|WithInfo(_, import_id)| {
                validated
                    .remove_entry(import_id)
                    .expect("toposorted result contains extra nodes")
            })
            .collect();
        debug_assert!(validated.is_empty());

        Ok(sorted)
    }

    pub fn type_check_rec<'i>(
        &self,
        initial: ImportId,
        initial_file_info: &'i FileInfo<'i>,
        importer: &mut impl Importer<'i>,
    ) -> Result<Vec<(ImportId, typed_ir::Term<'i>, String)>, CompilationError<'i>> {
        let untyped_irs = self.validate_rec(initial, initial_file_info, importer)?;

        let typed_irs = type_check(untyped_irs.iter().map(|(import_id, i)| (*import_id, i)))?;

        Ok(typed_irs)
    }

    pub fn evaluate_rec<'i>(
        &self,
        initial: ImportId,
        initial_file_info: &'i FileInfo<'i>,
        importer: &mut impl Importer<'i>,
    ) -> Result<(value::Value<'i>, String), CompilationError<'i>> {
        let mut imports = self.type_check_rec(initial, initial_file_info, importer)?;

        let (main_import_id, typed_ir, ty) =
            imports.pop().expect("at least one ir should be present");
        debug_assert_eq!(main_import_id, initial);

        let value = evaluate(
            &typed_ir,
            imports
                .iter()
                .map(|(import_id, typed_ir, _)| (*import_id, typed_ir)),
        )?;

        Ok((value, ty))
    }
}
