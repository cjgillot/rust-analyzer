//! FIXME: write short doc here

use hir_expand::{
    Source,
    either::Either,
    name::{self, AsName, Name},
};
use ra_syntax::{
    ast::{
        self, ArgListOwner, ArrayExprKind, LiteralKind, LoopBodyOwner, NameOwner,
        TypeAscriptionOwner,
    },
    AstNode, AstPtr, SyntaxNodePtr,
};
use test_utils::tested_by;
use crate::{HasModule, HasSource, Lookup};

use crate::{
    body::{Body, BodySourceMap, BodyWithSourceMap, Expander, PatPtr},
    builtin_type::{BuiltinFloat, BuiltinInt},
    db::DefDatabase,
    expr::{
        ArithOp, Array, BinaryOp, BindingAnnotation, CmpOp, Expr, ExprId, Literal, LogicOp,
        MatchArm, Ordering, Pat, PatId, RecordFieldPat, RecordLitField, Statement,
    },
    path::GenericArgs,
    path::Path,
    type_ref::{Mutability, TypeRef},
    DefWithBodyId, AstItemDef,
};

pub(super) fn lower(
    db: &impl DefDatabase,
    def: DefWithBodyId,
) -> (Body, BodySourceMap) {
    let mut params = None;

    let (file_id, module, syntax_ptr, body) = match def {
        DefWithBodyId::FunctionId(f) => {
            let f = f.lookup(db);
            let src = f.source(db);
            let ptr = AstPtr::new(&src.value);
            let ptr = src.with_value(ptr.syntax_node_ptr());
            params = src.value.param_list();
            (src.file_id, f.module(db), ptr, src.value.body().map(ast::Expr::from))
        }
        DefWithBodyId::ConstId(c) => {
            let c = c.lookup(db);
            let src = c.source(db);
            let ptr = AstPtr::new(&src.value);
            let ptr = src.with_value(ptr.syntax_node_ptr());
            (src.file_id, c.module(db), ptr, src.value.body())
        }
        DefWithBodyId::StaticId(s) => {
            let src = s.source(db);
            let ptr = AstPtr::new(&src.value);
            let ptr = src.with_value(ptr.syntax_node_ptr());
            (src.file_id, s.module(db), ptr, src.value.body())
        }
    };

    let expander = Expander::new(db, file_id, module);

    ExprCollector {
        expander,
        db,
        syntax_ptr,
        body: BodyWithSourceMap::new(),
    }
    .collect(params, body)
}

struct ExprCollector<DB> {
    db: DB,
    expander: Expander,

    body: BodyWithSourceMap,
    syntax_ptr: Source<SyntaxNodePtr>,
}

impl<'a, DB> ExprCollector<&'a DB>
where
    DB: DefDatabase,
{
    fn collect(
        mut self,
        param_list: Option<ast::ParamList>,
        body: Option<ast::Expr>,
    ) -> (Body, BodySourceMap) {
        if let Some(param_list) = param_list {
            if let Some(self_param) = param_list.self_param() {
                let ptr = AstPtr::new(&self_param);
                let param_pat = self.alloc_pat(
                    Pat::Bind {
                        name: name::SELF_PARAM,
                        mode: BindingAnnotation::Unannotated,
                        subpat: None,
                    },
                    Either::B(ptr),
                );
                self.body.push_param(param_pat);
            }

            for param in param_list.params() {
                let pat = match param.pat() {
                    None => continue,
                    Some(pat) => pat,
                };
                let param_pat = self.collect_pat(pat);
                self.body.push_param(param_pat);
            }
        };

        let body_expr = self.collect_expr_opt(body);

        let (mut body, source_map) = self.body.split();
        body.body_expr = body_expr;
        (body, source_map)
    }

    /// Allocate a new ExprId.
    fn alloc_expr(&mut self, expr: Expr, ptr: AstPtr<ast::Expr>) -> ExprId {
        let ptr = Either::A(ptr);
        let src = self.expander.to_source(ptr);
        let expr = self.body.alloc_expr(expr, src.map(|a| a.either(Into::into, Into::into)));
        self.body.map_expr(src, expr);
        expr
    }

    /// Allocate an ExprId for a node created by desugaring.
    /// It is not registered in the AST->HIR mapping.
    fn alloc_expr_desugared(&mut self, expr: Expr) -> ExprId {
        self.body.alloc_expr(expr, self.syntax_ptr)
    }

    /// Allocate ExprId for RecordField.
    fn alloc_expr_field_shorthand(&mut self, expr: Expr, ptr: AstPtr<ast::RecordField>) -> ExprId {
        let src = self.expander.to_source(ptr.syntax_node_ptr());
        self.body.alloc_expr(expr, src)
    }

    /// Allocate PatId.
    fn alloc_pat(&mut self, pat: Pat, ptr: PatPtr) -> PatId {
        let src = self.expander.to_source(ptr);
        let pat = self.body.alloc_pat(pat, src.map(|a| a.either(Into::into, Into::into)));
        self.body.map_pat(src, pat);
        pat
    }

    /// Allocate an ExprId for a node created by desugaring.
    /// It is not registered in the AST->HIR mapping.
    fn alloc_pat_desugared(&mut self, pat: Pat) -> PatId {
        self.body.alloc_pat(pat, self.syntax_ptr)
    }

    /// Allocate an empty block.
    fn empty_block(&mut self) -> ExprId {
        let block = Expr::Block { statements: Vec::new(), tail: None };
        self.body.alloc_expr(block, self.syntax_ptr)
    }

    /// Signal a missing expression.
    fn missing_expr(&mut self) -> ExprId {
        self.body.missing_expr()
    }

    /// Signal a missing pattern.
    fn missing_pat(&mut self) -> PatId {
        self.body.missing_pat()
    }

    fn do_collect_expr(&mut self, expr: ast::Expr, syntax_ptr: AstPtr<ast::Expr>) -> ExprId {
        let expr = match expr {
            ast::Expr::IfExpr(e) => self.collect_if(e),
            ast::Expr::TryBlockExpr(e) => {
                let body = self.collect_block_opt(e.body());
                Expr::TryBlock { body }
            }
            ast::Expr::BlockExpr(e) => self.do_collect_block(e),
            ast::Expr::LoopExpr(e) => {
                let body = self.collect_block_opt(e.loop_body());
                Expr::Loop { body }
            }
            ast::Expr::WhileExpr(e) => self.collect_while(e),
            ast::Expr::ForExpr(e) => {
                let iterable = self.collect_expr_opt(e.iterable());
                let pat = self.collect_pat_opt(e.pat());
                let body = self.collect_block_opt(e.loop_body());
                Expr::For { iterable, pat, body }
            }
            ast::Expr::CallExpr(e) => {
                let callee = self.collect_expr_opt(e.expr());
                let args = if let Some(arg_list) = e.arg_list() {
                    arg_list.args().map(|e| self.collect_expr(e)).collect()
                } else {
                    Vec::new()
                };
                Expr::Call { callee, args }
            }
            ast::Expr::MethodCallExpr(e) => {
                let receiver = self.collect_expr_opt(e.expr());
                let args = if let Some(arg_list) = e.arg_list() {
                    arg_list.args().map(|e| self.collect_expr(e)).collect()
                } else {
                    Vec::new()
                };
                let method_name = e.name_ref().map(|nr| nr.as_name()).unwrap_or_else(Name::missing);
                let generic_args = e.type_arg_list().and_then(GenericArgs::from_ast);
                Expr::MethodCall { receiver, method_name, args, generic_args }
            }
            ast::Expr::MatchExpr(e) => {
                let expr = self.collect_expr_opt(e.expr());
                let arms = if let Some(match_arm_list) = e.match_arm_list() {
                    match_arm_list
                        .arms()
                        .map(|arm| MatchArm {
                            pats: arm.pats().map(|p| self.collect_pat(p)).collect(),
                            expr: self.collect_expr_opt(arm.expr()),
                            guard: arm
                                .guard()
                                .and_then(|guard| guard.expr())
                                .map(|e| self.collect_expr(e)),
                        })
                        .collect()
                } else {
                    Vec::new()
                };
                Expr::Match { expr, arms }
            }
            ast::Expr::PathExpr(e) => {
                e.path()
                    .and_then(|path| self.expander.parse_path(path))
                    .map(Expr::Path)
                    .unwrap_or(Expr::Missing)
            }
            ast::Expr::ContinueExpr(_e) => {
                // FIXME: labels
                Expr::Continue
            }
            ast::Expr::BreakExpr(e) => {
                let expr = e.expr().map(|e| self.collect_expr(e));
                Expr::Break { expr }
            }
            ast::Expr::ParenExpr(e) => {
                // collect_expr makes the paren expr points to the inner expression
                return self.collect_expr_opt(e.expr())
            }
            ast::Expr::ReturnExpr(e) => {
                let expr = e.expr().map(|e| self.collect_expr(e));
                Expr::Return { expr }
            }
            ast::Expr::RecordLit(e) => {
                let path = e.path().and_then(|path| self.expander.parse_path(path));
                let mut field_ptrs = Vec::new();
                let record_lit = if let Some(nfl) = e.record_field_list() {
                    let fields = nfl
                        .fields()
                        .inspect(|field| field_ptrs.push(AstPtr::new(field)))
                        .map(|field| RecordLitField {
                            name: field
                                .name_ref()
                                .map(|nr| nr.as_name())
                                .unwrap_or_else(Name::missing),
                            expr: if let Some(e) = field.expr() {
                                self.collect_expr(e)
                            } else if let Some(nr) = field.name_ref() {
                                // field shorthand
                                self.alloc_expr_field_shorthand(
                                    Expr::Path(Path::from_name_ref(&nr)),
                                    AstPtr::new(&field),
                                )
                            } else {
                                self.missing_expr()
                            },
                        })
                        .collect();
                    let spread = nfl.spread().map(|s| self.collect_expr(s));
                    Expr::RecordLit { path, fields, spread }
                } else {
                    Expr::RecordLit { path, fields: Vec::new(), spread: None }
                };

                let res = self.alloc_expr(record_lit, syntax_ptr);
                for (i, ptr) in field_ptrs.into_iter().enumerate() {
                    self.body.map_field(i, ptr, res);
                }
                return res
            }
            ast::Expr::FieldExpr(e) => {
                let expr = self.collect_expr_opt(e.expr());
                let name = match e.field_access() {
                    Some(kind) => kind.as_name(),
                    _ => Name::missing(),
                };
                Expr::Field { expr, name }
            }
            ast::Expr::AwaitExpr(e) => {
                let expr = self.collect_expr_opt(e.expr());
                Expr::Await { expr }
            }
            ast::Expr::TryExpr(e) => {
                let expr = self.collect_expr_opt(e.expr());
                Expr::Try { expr }
            }
            ast::Expr::CastExpr(e) => {
                let expr = self.collect_expr_opt(e.expr());
                let type_ref = TypeRef::from_ast_opt(e.type_ref());
                Expr::Cast { expr, type_ref }
            }
            ast::Expr::RefExpr(e) => {
                let expr = self.collect_expr_opt(e.expr());
                let mutability = Mutability::from_mutable(e.is_mut());
                Expr::Ref { expr, mutability }
            }
            ast::Expr::PrefixExpr(e) => {
                let expr = self.collect_expr_opt(e.expr());
                if let Some(op) = e.op_kind() {
                    Expr::UnaryOp { expr, op }
                } else {
                    Expr::Missing
                }
            }
            ast::Expr::LambdaExpr(e) => {
                let mut args = Vec::new();
                let mut arg_types = Vec::new();
                if let Some(pl) = e.param_list() {
                    for param in pl.params() {
                        let pat = self.collect_pat_opt(param.pat());
                        let type_ref = param.ascribed_type().map(TypeRef::from_ast);
                        args.push(pat);
                        arg_types.push(type_ref);
                    }
                }
                let body = self.collect_expr_opt(e.body());
                Expr::Lambda { args, arg_types, body }
            }
            ast::Expr::BinExpr(e) => {
                let lhs = self.collect_expr_opt(e.lhs());
                let rhs = self.collect_expr_opt(e.rhs());
                let op = e.op_kind().map(BinaryOp::from);
                Expr::BinaryOp { lhs, rhs, op }
            }
            ast::Expr::TupleExpr(e) => {
                let exprs = e.exprs().map(|expr| self.collect_expr(expr)).collect();
                Expr::Tuple { exprs }
            }
            ast::Expr::BoxExpr(e) => {
                let expr = self.collect_expr_opt(e.expr());
                Expr::Box { expr }
            }

            ast::Expr::ArrayExpr(e) => {
                let kind = e.kind();

                match kind {
                    ArrayExprKind::ElementList(e) => {
                        let exprs = e.map(|expr| self.collect_expr(expr)).collect();
                        Expr::Array(Array::ElementList(exprs))
                    }
                    ArrayExprKind::Repeat { initializer, repeat } => {
                        let initializer = self.collect_expr_opt(initializer);
                        let repeat = self.collect_expr_opt(repeat);
                        Expr::Array(Array::Repeat { initializer, repeat })
                    }
                }
            }

            ast::Expr::Literal(e) => {
                let lit = match e.kind() {
                    LiteralKind::IntNumber { suffix } => {
                        let known_name = suffix.and_then(|it| BuiltinInt::from_suffix(&it));

                        Literal::Int(Default::default(), known_name)
                    }
                    LiteralKind::FloatNumber { suffix } => {
                        let known_name = suffix.and_then(|it| BuiltinFloat::from_suffix(&it));

                        Literal::Float(Default::default(), known_name)
                    }
                    LiteralKind::ByteString => Literal::ByteString(Default::default()),
                    LiteralKind::String => Literal::String(Default::default()),
                    LiteralKind::Byte => Literal::Int(Default::default(), Some(BuiltinInt::U8)),
                    LiteralKind::Bool => Literal::Bool(Default::default()),
                    LiteralKind::Char => Literal::Char(Default::default()),
                };
                Expr::Literal(lit)
            }
            ast::Expr::IndexExpr(e) => {
                let base = self.collect_expr_opt(e.base());
                let index = self.collect_expr_opt(e.index());
                Expr::Index { base, index }
            }

            // FIXME implement HIR for these:
            ast::Expr::Label(_e) => Expr::Missing,
            ast::Expr::RangeExpr(_e) => Expr::Missing,
            ast::Expr::MacroCall(e) => match self.expander.enter_expand(self.db, e) {
                Some((mark, expansion)) => {
                    let id = self.collect_expr(expansion);
                    self.expander.exit(self.db, mark);
                    return id
                }
                None => Expr::Missing,
            },
        };
        self.alloc_expr(expr, syntax_ptr)
    }

    fn collect_expr(&mut self, expr: ast::Expr) -> ExprId {
        let syntax_ptr = AstPtr::new(&expr);
        let src = self.expander.to_source(Either::A(syntax_ptr));
        let id = self.do_collect_expr(expr, syntax_ptr);
        self.body.map_expr(src, id);
        id
    }

    fn collect_expr_opt(&mut self, expr: Option<ast::Expr>) -> ExprId {
        if let Some(expr) = expr {
            self.collect_expr(expr)
        } else {
            self.missing_expr()
        }
    }

    fn collect_if(&mut self, expr: ast::IfExpr) -> Expr {
        let then_branch = self.collect_block_opt(expr.then_branch());

        let else_branch = expr.else_branch().map(|b| match b {
            ast::ElseBranch::Block(it) => self.collect_block(it),
            ast::ElseBranch::IfExpr(elif) => {
                let expr: ast::Expr = ast::Expr::cast(elif.syntax().clone()).unwrap();
                self.collect_expr(expr)
            }
        });

        let condition = match expr.condition() {
            None => self.missing_expr(),
            Some(condition) => match condition.pat() {
                None => self.collect_expr_opt(condition.expr()),
                // if let -- desugar to match
                Some(pat) => {
                    let pat = self.collect_pat(pat);
                    let match_expr = self.collect_expr_opt(condition.expr());
                    let placeholder_pat = self.alloc_pat_desugared(Pat::Wild);
                    let arms = vec![
                        MatchArm { pats: vec![pat], expr: then_branch, guard: None },
                        MatchArm {
                            pats: vec![placeholder_pat],
                            expr: else_branch.unwrap_or_else(|| self.empty_block()),
                            guard: None,
                        },
                    ];
                    return Expr::Match { expr: match_expr, arms };
                }
            },
        };

        Expr::If { condition, then_branch, else_branch }
    }

    fn collect_while(&mut self, expr: ast::WhileExpr) -> Expr {
        let body = self.collect_block_opt(expr.loop_body());

        let condition = match expr.condition() {
            None => self.missing_expr(),
            Some(condition) => match condition.pat() {
                None => self.collect_expr_opt(condition.expr()),
                // if let -- desugar to match
                Some(pat) => {
                    tested_by!(infer_resolve_while_let);
                    let pat = self.collect_pat(pat);
                    let match_expr = self.collect_expr_opt(condition.expr());
                    let placeholder_pat = self.alloc_pat_desugared(Pat::Wild);
                    let break_ = self.alloc_expr_desugared(Expr::Break { expr: None });
                    let arms = vec![
                        MatchArm { pats: vec![pat], expr: body, guard: None },
                        MatchArm { pats: vec![placeholder_pat], expr: break_, guard: None },
                    ];
                    let match_expr =
                        self.alloc_expr_desugared(Expr::Match { expr: match_expr, arms });
                    return Expr::Loop { body: match_expr };
                }
            },
        };

        Expr::While { condition, body }
    }

    fn do_collect_block(&mut self, expr: ast::BlockExpr) -> Expr {
        let block = match expr.block() {
            Some(block) => block,
            None => return Expr::Missing,
        };
        let statements = block
            .statements()
            .map(|s| match s {
                ast::Stmt::LetStmt(stmt) => {
                    let pat = self.collect_pat_opt(stmt.pat());
                    let type_ref = stmt.ascribed_type().map(TypeRef::from_ast);
                    let initializer = stmt.initializer().map(|e| self.collect_expr(e));
                    Statement::Let { pat, type_ref, initializer }
                }
                ast::Stmt::ExprStmt(stmt) => Statement::Expr(self.collect_expr_opt(stmt.expr())),
            })
            .collect();
        let tail = block.expr().map(|e| self.collect_expr(e));
        Expr::Block { statements, tail }
    }

    fn collect_block(&mut self, expr: ast::BlockExpr) -> ExprId {
        let syntax_node_ptr = AstPtr::new(&expr.clone().into());
        let expr = self.do_collect_block(expr);
        self.alloc_expr(expr, syntax_node_ptr)
    }

    fn collect_block_opt(&mut self, expr: Option<ast::BlockExpr>) -> ExprId {
        if let Some(block) = expr {
            self.collect_block(block)
        } else {
            self.missing_expr()
        }
    }

    fn collect_pat(&mut self, pat: ast::Pat) -> PatId {
        let pattern = match &pat {
            ast::Pat::BindPat(bp) => {
                let name = bp.name().map(|nr| nr.as_name()).unwrap_or_else(Name::missing);
                let annotation = BindingAnnotation::new(bp.is_mutable(), bp.is_ref());
                let subpat = bp.pat().map(|subpat| self.collect_pat(subpat));
                Pat::Bind { name, mode: annotation, subpat }
            }
            ast::Pat::TupleStructPat(p) => {
                let path = p.path().and_then(|path| self.expander.parse_path(path));
                let args = p.args().map(|p| self.collect_pat(p)).collect();
                Pat::TupleStruct { path, args }
            }
            ast::Pat::RefPat(p) => {
                let pat = self.collect_pat_opt(p.pat());
                let mutability = Mutability::from_mutable(p.is_mut());
                Pat::Ref { pat, mutability }
            }
            ast::Pat::PathPat(p) => {
                let path = p.path().and_then(|path| self.expander.parse_path(path));
                path.map(Pat::Path).unwrap_or(Pat::Missing)
            }
            ast::Pat::TuplePat(p) => {
                let args = p.args().map(|p| self.collect_pat(p)).collect();
                Pat::Tuple(args)
            }
            ast::Pat::PlaceholderPat(_) => Pat::Wild,
            ast::Pat::RecordPat(p) => {
                let path = p.path().and_then(|path| self.expander.parse_path(path));
                let record_field_pat_list =
                    p.record_field_pat_list().expect("every struct should have a field list");
                let mut fields: Vec<_> = record_field_pat_list
                    .bind_pats()
                    .filter_map(|bind_pat| {
                        let ast_pat =
                            ast::Pat::cast(bind_pat.syntax().clone()).expect("bind pat is a pat");
                        let pat = self.collect_pat(ast_pat);
                        let name = bind_pat.name()?.as_name();
                        Some(RecordFieldPat { name, pat })
                    })
                    .collect();
                let iter = record_field_pat_list.record_field_pats().filter_map(|f| {
                    let ast_pat = f.pat()?;
                    let pat = self.collect_pat(ast_pat);
                    let name = f.name()?.as_name();
                    Some(RecordFieldPat { name, pat })
                });
                fields.extend(iter);

                Pat::Record { path, args: fields }
            }

            // FIXME: implement
            ast::Pat::DotDotPat(_) => Pat::Missing,
            ast::Pat::BoxPat(_) => Pat::Missing,
            ast::Pat::LiteralPat(_) => Pat::Missing,
            ast::Pat::SlicePat(_) | ast::Pat::RangePat(_) => Pat::Missing,
        };
        let ptr = AstPtr::new(&pat);
        self.alloc_pat(pattern, Either::A(ptr))
    }

    fn collect_pat_opt(&mut self, pat: Option<ast::Pat>) -> PatId {
        if let Some(pat) = pat {
            self.collect_pat(pat)
        } else {
            self.missing_pat()
        }
    }
}

impl From<ast::BinOp> for BinaryOp {
    fn from(ast_op: ast::BinOp) -> Self {
        match ast_op {
            ast::BinOp::BooleanOr => BinaryOp::LogicOp(LogicOp::Or),
            ast::BinOp::BooleanAnd => BinaryOp::LogicOp(LogicOp::And),
            ast::BinOp::EqualityTest => BinaryOp::CmpOp(CmpOp::Eq { negated: false }),
            ast::BinOp::NegatedEqualityTest => BinaryOp::CmpOp(CmpOp::Eq { negated: true }),
            ast::BinOp::LesserEqualTest => {
                BinaryOp::CmpOp(CmpOp::Ord { ordering: Ordering::Less, strict: false })
            }
            ast::BinOp::GreaterEqualTest => {
                BinaryOp::CmpOp(CmpOp::Ord { ordering: Ordering::Greater, strict: false })
            }
            ast::BinOp::LesserTest => {
                BinaryOp::CmpOp(CmpOp::Ord { ordering: Ordering::Less, strict: true })
            }
            ast::BinOp::GreaterTest => {
                BinaryOp::CmpOp(CmpOp::Ord { ordering: Ordering::Greater, strict: true })
            }
            ast::BinOp::Addition => BinaryOp::ArithOp(ArithOp::Add),
            ast::BinOp::Multiplication => BinaryOp::ArithOp(ArithOp::Mul),
            ast::BinOp::Subtraction => BinaryOp::ArithOp(ArithOp::Sub),
            ast::BinOp::Division => BinaryOp::ArithOp(ArithOp::Div),
            ast::BinOp::Remainder => BinaryOp::ArithOp(ArithOp::Rem),
            ast::BinOp::LeftShift => BinaryOp::ArithOp(ArithOp::Shl),
            ast::BinOp::RightShift => BinaryOp::ArithOp(ArithOp::Shr),
            ast::BinOp::BitwiseXor => BinaryOp::ArithOp(ArithOp::BitXor),
            ast::BinOp::BitwiseOr => BinaryOp::ArithOp(ArithOp::BitOr),
            ast::BinOp::BitwiseAnd => BinaryOp::ArithOp(ArithOp::BitAnd),
            ast::BinOp::Assignment => BinaryOp::Assignment { op: None },
            ast::BinOp::AddAssign => BinaryOp::Assignment { op: Some(ArithOp::Add) },
            ast::BinOp::DivAssign => BinaryOp::Assignment { op: Some(ArithOp::Div) },
            ast::BinOp::MulAssign => BinaryOp::Assignment { op: Some(ArithOp::Mul) },
            ast::BinOp::RemAssign => BinaryOp::Assignment { op: Some(ArithOp::Rem) },
            ast::BinOp::ShlAssign => BinaryOp::Assignment { op: Some(ArithOp::Shl) },
            ast::BinOp::ShrAssign => BinaryOp::Assignment { op: Some(ArithOp::Shr) },
            ast::BinOp::SubAssign => BinaryOp::Assignment { op: Some(ArithOp::Sub) },
            ast::BinOp::BitOrAssign => BinaryOp::Assignment { op: Some(ArithOp::BitOr) },
            ast::BinOp::BitAndAssign => BinaryOp::Assignment { op: Some(ArithOp::BitAnd) },
            ast::BinOp::BitXorAssign => BinaryOp::Assignment { op: Some(ArithOp::BitXor) },
        }
    }
}
