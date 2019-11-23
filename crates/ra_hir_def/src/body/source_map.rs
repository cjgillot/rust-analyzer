use hir_expand::{
    either::Either,
    Source,
};
use ra_arena::{map::ArenaMap, Arena};
use ra_syntax::{ast, AstPtr, SyntaxNodePtr};
use rustc_hash::FxHashMap;

use crate::{
    expr::{Expr, ExprId, Pat, PatId},
    body::Body,
};

pub type ExprPtr = Either<AstPtr<ast::Expr>, AstPtr<ast::RecordField>>;
pub type ExprSource = Source<ExprPtr>;

pub type PatPtr = Either<AstPtr<ast::Pat>, AstPtr<ast::SelfParam>>;
pub type PatSource = Source<PatPtr>;

pub type AstSource = Source<SyntaxNodePtr>;

/// An item body together with the mapping from syntax nodes to HIR expression
/// IDs. This is needed to go from e.g. a position in a file to the HIR
/// expression containing it; but for type inference etc., we want to operate on
/// a structure that is agnostic to the actual positions of expressions in the
/// file, so that we don't recompute types whenever some whitespace is typed.
///
/// One complication here is that, due to macro expansion, a single `Body` might
/// be spread across several files. So, for each ExprId and PatId, we record
/// both the HirFileId and the position inside the file. However, we only store
/// AST -> ExprId mapping for non-macro files, as it is not clear how to handle
/// this properly for macros.
#[derive(Debug, Eq, PartialEq)]
pub struct BodySourceMap {
    expr_map: FxHashMap<ExprSource, ExprId>,
    expr_map_back: ArenaMap<ExprId, AstSource>,
    pat_map: FxHashMap<PatSource, PatId>,
    pat_map_back: ArenaMap<PatId, AstSource>,
    field_map: FxHashMap<(ExprId, usize), AstPtr<ast::RecordField>>,
}

impl BodySourceMap {
    fn new() -> BodySourceMap {
        BodySourceMap {
            expr_map: FxHashMap::default(),
            expr_map_back: ArenaMap::default(),
            pat_map: FxHashMap::default(),
            pat_map_back: ArenaMap::default(),
            field_map: FxHashMap::default(),
        }
    }

    pub fn expr_syntax(&self, expr: ExprId) -> Option<AstSource> {
        self.expr_map_back.get(expr).copied()
    }

    pub fn node_expr(&self, node: Source<&ast::Expr>) -> Option<ExprId> {
        let src = node.map(|it| Either::A(AstPtr::new(it)));
        self.expr_map.get(&src).cloned()
    }

    pub fn pat_syntax(&self, pat: PatId) -> Option<AstSource> {
        self.pat_map_back.get(pat).copied()
    }

    pub fn node_pat(&self, node: Source<&ast::Pat>) -> Option<PatId> {
        let src = node.map(|it| Either::A(AstPtr::new(it)));
        self.pat_map.get(&src).cloned()
    }

    pub fn field_syntax(&self, expr: ExprId, field: usize) -> AstPtr<ast::RecordField> {
        self.field_map[&(expr, field)]
    }
}

/// This structure is used to enforce HIR nodes allocation discipline.
/// All allocated Ids must be associated to a source pointer.
pub(crate) struct BodyWithSourceMap {
    body: Body,
    source_map: BodySourceMap,
}

impl BodyWithSourceMap {
    pub fn new() -> BodyWithSourceMap {
        BodyWithSourceMap {
            body: Body {
                exprs: Arena::default(),
                pats: Arena::default(),
                params: Vec::new(),
                body_expr: ExprId::dummy(),
            },
            source_map: BodySourceMap::new(),
        }
    }

    pub fn split(self) -> (Body, BodySourceMap) {
        (self.body, self.source_map)
    }

    pub fn push_param(&mut self, pat: PatId) {
        self.body.params.push(pat)
    }

    // AST -> HIR mapping

    pub fn map_expr(&mut self, src: ExprSource, to: ExprId) {
        self.source_map.expr_map.insert(src, to);
    }

    pub fn map_pat(&mut self, src: PatSource, to: PatId) {
        self.source_map.pat_map.insert(src, to);
    }

    pub fn map_field(&mut self, i: usize, src: AstPtr<ast::RecordField>, res: ExprId) {
        self.source_map.field_map.insert((res, i), src);
    }

    // HIR -> AST mapping

    pub fn alloc_expr(&mut self, expr: Expr, src: AstSource) -> ExprId {
        let id = self.body.exprs.alloc(expr);
        self.source_map.expr_map_back.insert(id, src);
        id
    }

    pub fn alloc_pat(&mut self, pat: Pat, src: AstSource) -> PatId {
        let id = self.body.pats.alloc(pat);
        self.source_map.pat_map_back.insert(id, src);
        id
    }

    // Missing cases

    pub fn missing_expr(&mut self) -> ExprId {
        self.body.exprs.alloc(Expr::Missing)
    }

    pub fn missing_pat(&mut self) -> PatId {
        self.body.pats.alloc(Pat::Missing)
    }
}
