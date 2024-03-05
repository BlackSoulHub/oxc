use crate::rule::Rule;
use crate::LintContext;
use itertools::{Itertools, MinMaxResult};
use oxc_ast::ast::{
    AssignmentTarget, Class, ClassElement, Expression, Function, MemberExpression,
    MethodDefinition, MethodDefinitionKind, PropertyDefinition, SimpleAssignmentTarget, Statement,
};
use oxc_ast::AstKind;
use oxc_diagnostics::miette::{self, Diagnostic};
use oxc_diagnostics::thiserror::Error;
use oxc_macros::declare_oxc_lint;
use oxc_semantic::BasicBlockElement;
use oxc_span::Span;
use std::collections::HashSet;

#[derive(Debug, Error, Diagnostic)]
#[error("eslint(no-unreachable): Disallow unreachable code")]
#[diagnostic(
    severity(warning),
    help("Because the return, throw, break, and continue statements unconditionally exit a block of code.\
    Unreachable statements are usually a mistake.")
)]
struct NoUnreachableDiagnostic(#[label] Span);

#[derive(Debug, Default, Clone)]
pub struct NoUnreachable;

declare_oxc_lint!(
    /// ### What it does
    ///
    /// Disallow unreachable code after return, throw, continue,
    /// and break statements
    ///
    /// ### Why is this bad?
    ///
    /// Because the return, throw, break, and continue statements unconditionally exit a block of code,
    /// any statements after them cannot be executed.
    /// Unreachable statements are usually a mistake.
    ///
    /// ### Example
    /// ```javascript
    /// function foo() {
    ///     return true;
    ///     console.log("done");
    /// }
    ///
    /// while(val) {
    ///     break;
    ///     console.log("done")
    /// }
    ///
    /// class C extends B {
    ///     #x; // unreachable
    ///     #y = 1; // unreachable
    ///     a; // unreachable
    ///     b = 1; // unreachable
    ///
    ///     constructor() {
    ///         return {};
    ///     }
    /// }
    /// ```
    NoUnreachable,
    correctness
);

impl Rule for NoUnreachable {
    fn run_once(&self, ctx: &LintContext) {
        let semantic = ctx.semantic();
        let cfg = semantic.cfg();

        for node in semantic.nodes().iter() {
            match node.kind() {
                AstKind::Function(function) => {
                    let Some(ref id) = function.id else { continue };
                    let function_name = id.name.as_str();

                    // We check constructor in class check
                    if function_name != "constructor" {
                        Self::diagnostic_function(function, ctx);
                    }
                }
                AstKind::Class(class) => Self::diagnostic_class(class, ctx),
                AstKind::BreakStatement(break_statement) => {
                    let Some(parent_node) = semantic.nodes().parent_node(node.id()) else {
                        continue;
                    };

                    let blocks = cfg.basic_block_by_index(parent_node.cfg_ix());

                    let block_contains_unreachable = blocks
                        .iter()
                        .any(|element| matches!(element, BasicBlockElement::Unreachable));

                    if block_contains_unreachable {
                        ctx.diagnostic(NoUnreachableDiagnostic(break_statement.span))
                    }
                }
                _ => {}
            }
        }
    }
}

impl NoUnreachable {
    fn diagnostic_function(func: &Function, ctx: &LintContext) {
        let cfg = ctx.semantic().cfg();

        for block in &cfg.basic_blocks {
            for element in block {
                // todo: fix tests
                if matches!(element, BasicBlockElement::Unreachable) {
                    ctx.diagnostic(NoUnreachableDiagnostic(func.span));
                }
            }
        }
    }

    fn diagnostic_class(class: &Class, ctx: &LintContext) {
        let has_base_class = class.has_base_class();
        let has_explicit_constructor = class.body.has_explicit_constructor();

        // If the constructor is not declared, the base class version is used.
        // The correctness of the basic constructor can be checked in isolation
        // todo: It from `no-unreachable` eslint rule.
        // todo: But this looks bad because class can declare new fields
        if !has_explicit_constructor && has_base_class {
            return;
        }

        let constructor = Self::get_constructor(class).expect("Constructor not found");
        let is_constructor_call_super = Self::check_constructor_call_super(constructor);

        // If class have base class and constructor calls `super`-constructor.
        // We don't require check this rule (from ESlint example)
        if has_base_class && is_constructor_call_super {
            return;
        }

        let required_initialize_property = Self::get_class_non_static_fields(class);
        if required_initialize_property.is_empty() {
            return;
        }

        let fields_span = match required_initialize_property.iter().map(|f| f.span).minmax() {
            MinMaxResult::NoElements => class.span,
            MinMaxResult::OneElement(field) => field,
            MinMaxResult::MinMax(first_field, last_field) => {
                Span::new(first_field.start, last_field.end)
            }
        };

        // If constructor body is empty and non-static fields exits - all fields are unreachable
        let Some(ref constructor) = constructor.value.body else {
            ctx.diagnostic(NoUnreachableDiagnostic(fields_span));
            return;
        };

        let mut initialized_property: HashSet<&str> = HashSet::new();

        // todo: fix this
        if constructor
            .statements
            .iter()
            .any(|statement| matches!(statement, Statement::ReturnStatement(_)))
        {
            return;
        }

        for statement in &constructor.statements {
            if let Statement::ExpressionStatement(expression_statement) = statement {
                if let Expression::AssignmentExpression(ref assignment) =
                    expression_statement.expression
                {
                    if let AssignmentTarget::SimpleAssignmentTarget(
                        SimpleAssignmentTarget::MemberAssignmentTarget(ref member_expression),
                    ) = assignment.left
                    {
                        if let MemberExpression::PrivateFieldExpression(private_field) =
                            &**member_expression
                        {
                            initialized_property.insert(private_field.field.name.as_str());
                        }
                    }
                }
            }
        }

        for property in required_initialize_property {
            if !initialized_property
                .iter()
                .any(|p| *p == property.key.static_name().expect("Name not set").as_str())
            {
                ctx.diagnostic(NoUnreachableDiagnostic(property.span));
            }
        }
    }

    fn get_constructor<'a, 'b>(class: &'a Class<'b>) -> Option<&'a MethodDefinition<'b>> {
        for element in &class.body.body {
            match element {
                ClassElement::MethodDefinition(ref method)
                    if method.kind == MethodDefinitionKind::Constructor =>
                {
                    return Some(method)
                }
                _ => {}
            }
        }

        None
    }

    fn check_constructor_call_super(constructor: &MethodDefinition) -> bool {
        let Some(ref body) = constructor.value.body else {
            return false;
        };

        for statement in &body.statements {
            if let Statement::ExpressionStatement(ref expression_statement) = statement {
                if let Expression::CallExpression(ref expression) = expression_statement.expression
                {
                    if let Expression::Super(_) = expression.callee {
                        return true;
                    }
                }
            }
        }

        false
    }

    fn get_class_non_static_fields<'a, 'b>(
        class: &'a Class<'b>,
    ) -> Vec<&'a oxc_allocator::Box<'b, PropertyDefinition<'b>>> {
        let mut fields = Vec::new();

        for class_element in &class.body.body {
            if let ClassElement::PropertyDefinition(property) = class_element {
                // We don't require to check static property initialization
                if !property.r#static {
                    fields.push(property);
                }
            }
        }

        fields
    }
}

#[test]
fn test() {
    use crate::tester::Tester;

    let pass = vec![
        (
            "class D extends B {
            #x;
            #y = 1;
            a;
            b = 1;

            constructor() {
                super();
            }
        }",
            None,
        ),
        (
            "class E extends B {
            #x;
            #y = 1;
            a;
            b = 1;

            // implicit constructor always calls `super()`
        }",
            None,
        ),
        (
            "class F extends B {
            static #x;
            static #y = 1;
            static a;
            static b = 1;

            constructor() {
                return {};
            }
        }",
            None,
        ),
    ];

    let fail = vec![
        // (
        //     "class C extends B {
        //     #x; // unreachable
        //     #y = 1; // unreachable
        //     a; // unreachable
        //     b = 1; // unreachable
        //
        //     constructor() {
        //         return {};
        //     }
        // }",
        //     None,
        // ),
        // (
        //     "function foo() {
        //     return true;
        //     console.log('done');
        // }",
        //     None,
        // ),
        // (
        //     "function bar() {
        //     throw new Error('Oops!');
        //     console.log('done');
        // }",
        //     None,
        // ),
        (
            "while(value) {
            break;
            console.log('done');
        }",
            None,
        ),
        // (
        //     "throw new Error('Oops!');
        // console.log('done');",
        //     None,
        // ),
        // (
        //     "function baz() {
        //     if (Math.random() < 0.5) {
        //         return;
        //     } else {
        //         throw new Error();
        //     }
        //     console.log('done');
        // }",
        //     None,
        // ),
        // (
        //     "for (;;) {}
        // console.log('done');",
        //     None,
        // ),
    ];

    Tester::new(NoUnreachable::NAME, pass, fail).test_and_snapshot();
}
