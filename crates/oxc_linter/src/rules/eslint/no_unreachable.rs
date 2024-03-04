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
use oxc_semantic::{AstNode, BasicBlockElement};
use oxc_span::Span;
use std::collections::HashSet;
use std::ops::Deref;

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
    fn run<'a>(&self, node: &AstNode<'a>, ctx: &LintContext<'a>) {
        match node.kind() {
            AstKind::Function(ref func) => {
                let func_name = match func.id {
                    None => return,
                    Some(ref func_name) => func_name.name.as_str(),
                };

                if func_name != "constructor" {
                    Self::diagnostic_function(func, ctx)
                }
            }
            AstKind::ArrowFunctionExpression(_) => {}
            AstKind::Class(class) => Self::diagnostic_class(class, ctx),
            // todo: Add more exactly error message
            AstKind::Program(program) => {
                for block in &ctx.semantic().cfg().basic_blocks {
                    for element in block {
                        if matches!(element, BasicBlockElement::Unreachable) {
                            ctx.diagnostic(NoUnreachableDiagnostic(program.span))
                        }
                    }
                }
            }
            _ => {}
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
                    ctx.diagnostic(NoUnreachableDiagnostic(func.span))
                }
            }
        }
    }

    fn diagnostic_class<'a>(class: &'a Class, ctx: &LintContext) {
        let has_base_class = class.has_base_class();
        let has_explicit_constructor = class.body.has_explicit_constructor();

        // If the constructor is not declared, the base class version is used.
        // The correctness of the basic constructor can be checked in isolation
        // todo: It from `no-unreachable` eslint rule.
        // todo: But this looks bad because class can declare new fields
        if !has_explicit_constructor && has_base_class {
            return;
        }

        let constructor = Self::get_constructor(&class).expect("Constructor not found");
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

        for statement in &constructor.statements {
            match statement {
                Statement::ExpressionStatement(expression_statement) => {
                    match expression_statement.expression {
                        Expression::AssignmentExpression(ref assignment) => match assignment.left {
                            AssignmentTarget::SimpleAssignmentTarget(ref target) => match target {
                                SimpleAssignmentTarget::MemberAssignmentTarget(
                                    ref member_expression,
                                ) => match member_expression.deref() {
                                    MemberExpression::PrivateFieldExpression(private_field) => {
                                        initialized_property
                                            .insert(private_field.field.name.as_str());
                                    }
                                    _ => {}
                                },
                                _ => {}
                            },
                            _ => {}
                        },
                        _ => {}
                    }
                }
                _ => {}
            }
        }

        for property in required_initialize_property {
            if !initialized_property
                .iter()
                .any(|p| *p == property.key.static_name().expect("Name not set").as_str())
            {
                ctx.diagnostic(NoUnreachableDiagnostic(property.span))
            }
        }
    }

    fn get_constructor<'a, 'b>(class: &'a Class<'b>) -> Option<&'a MethodDefinition<'b>> {
        for element in &class.body.body {
            match element {
                ClassElement::MethodDefinition(ref method) => match method.kind {
                    MethodDefinitionKind::Constructor => return Some(&method),
                    _ => {}
                },
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
            match statement {
                Statement::ExpressionStatement(ref expression_statement) => {
                    match expression_statement.expression {
                        Expression::CallExpression(ref expression) => match expression.callee {
                            Expression::Super(_) => return true,
                            _ => {}
                        },
                        _ => {}
                    }
                }
                _ => {}
            }
        }

        false
    }

    fn get_class_non_static_fields<'a, 'b>(
        class: &'a Class<'b>,
    ) -> Vec<&'a oxc_allocator::Box<'b, PropertyDefinition<'b>>> {
        let mut fields = Vec::new();

        for class_element in &class.body.body {
            match class_element {
                ClassElement::PropertyDefinition(property) => {
                    // We don't require to check static property initialization
                    if !property.r#static {
                        fields.push(property)
                    }
                }
                _ => {}
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
        (
            "class C extends B {
            #x; // unreachable
            #y = 1; // unreachable
            a; // unreachable
            b = 1; // unreachable

            constructor() {
                return {};
            }
        }",
            None,
        ),
        (
            "function foo() {
            return true;
            console.log('done');
        }",
            None,
        ),
        (
            "function bar() {
            throw new Error('Oops!');
            console.log('done');
        }",
            None,
        ),
        (
            "while(value) {
            break;
            console.log('done');
        }",
            None,
        ),
        (
            "throw new Error('Oops!');
        console.log('done');",
            None,
        ),
        (
            "function baz() {
            if (Math.random() < 0.5) {
                return;
            } else {
                throw new Error();
            }
            console.log('done');
        }",
            None,
        ),
        (
            "for (;;) {}
        console.log('done');",
            None,
        ),
    ];

    Tester::new(NoUnreachable::NAME, pass, fail).test_and_snapshot();
}
