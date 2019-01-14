use lark_debug_with::DebugWith;
use lark_entity::{Entity, EntityData, ItemKind, LangItem};
use lark_error::{Diagnostic, WithError};
use lark_hir as hir;
use lark_intern::{Intern, Untern};
use lark_parser::{ParserDatabase, ParserDatabaseExt};
use lark_query_system::LarkDatabase;
use lark_ty::Ty;
use lark_type_check::TypeCheckDatabase;

fn build_variable_type(
    db: &LarkDatabase,
    fn_types: &std::sync::Arc<
        lark_type_check::TypeCheckResults<lark_ty::full_inferred::FullInferred>,
    >,
    variable: lark_hir::Variable,
) -> String {
    build_expr_type(db, &fn_types.ty(lark_hir::MetaIndex::Variable(variable)))
}

fn build_variable_name(
    db: &LarkDatabase,
    fn_body: &std::sync::Arc<hir::FnBody>,
    variable: lark_hir::Variable,
) -> String {
    let variable_data = fn_body.tables[variable];
    let identifier = fn_body.tables[variable_data.name];
    identifier.text.untern(db).to_string()
}

fn build_entity_name(db: &LarkDatabase, entity: Entity) -> String {
    let entity_data = entity.untern(db);
    match entity_data {
        EntityData::LangItem(LangItem::False) => "false".into(),
        EntityData::LangItem(LangItem::True) => "true".into(),
        EntityData::LangItem(LangItem::Debug) => "printf".into(),
        EntityData::ItemName { id, .. } => format!("{}", id.untern(db).to_string()),
        x => unimplemented!("Unsupported entity name: {:#?}", x),
    }
}

pub fn build_place(
    db: &LarkDatabase,
    fn_body: &std::sync::Arc<hir::FnBody>,
    fn_types: &std::sync::Arc<
        lark_type_check::TypeCheckResults<lark_ty::full_inferred::FullInferred>,
    >,
    place: hir::Place,
) -> String {
    match &fn_body.tables[place] {
        hir::PlaceData::Variable(variable) => build_variable_name(db, fn_body, *variable),
        hir::PlaceData::Entity(entity) => build_entity_name(db, *entity),
        hir::PlaceData::Field { owner, name } => {
            let identifier = fn_body.tables[*name];

            format!(
                "{}.{}",
                build_place(db, fn_body, fn_types, *owner),
                identifier.text.untern(db).to_string()
            )
        }
        hir::PlaceData::Temporary(expression) => {
            build_expression(db, fn_body, fn_types, *expression)
        }
    }
}

fn build_format_for_type(
    db: &LarkDatabase,
    fn_body: &std::sync::Arc<hir::FnBody>,
    fn_types: &std::sync::Arc<
        lark_type_check::TypeCheckResults<lark_ty::full_inferred::FullInferred>,
    >,
    ty: &Ty<lark_ty::full_inferred::FullInferred>,
    expression: hir::Expression,
) -> (String, String) {
    let boolean_entity = EntityData::LangItem(LangItem::Boolean).intern(db);
    let uint_entity = EntityData::LangItem(LangItem::Uint).intern(db);
    let int_entity = EntityData::LangItem(LangItem::Int).intern(db);
    let string_entity = EntityData::LangItem(LangItem::String).intern(db);
    let void_entity = EntityData::LangItem(LangItem::Tuple(0)).intern(db);

    match ty.base.untern(db).kind {
        lark_ty::BaseKind::Named(entity) => match entity {
            x if x == boolean_entity => (
                "%s".to_string(),
                format!(
                    "({})?\"true\":\"false\"",
                    build_expression(db, fn_body, fn_types, expression)
                ),
            ),
            x if x == uint_entity => (
                "%u".into(),
                build_expression(db, fn_body, fn_types, expression),
            ),
            x if x == int_entity => (
                "%i".into(),
                build_expression(db, fn_body, fn_types, expression),
            ),
            x if x == string_entity => (
                "%s".into(),
                build_expression(db, fn_body, fn_types, expression),
            ),
            x if x == void_entity => ("%s".into(), "<void>".into()),
            _ => unimplemented!("Unknown type: {:#?}", entity),
        },
        _ => unimplemented!("Unknown base kind"),
    }
}

pub fn build_expr_type(db: &LarkDatabase, ty: &Ty<lark_ty::full_inferred::FullInferred>) -> String {
    let boolean_entity = EntityData::LangItem(LangItem::Boolean).intern(db);
    let uint_entity = EntityData::LangItem(LangItem::Uint).intern(db);
    let int_entity = EntityData::LangItem(LangItem::Int).intern(db);
    let string_entity = EntityData::LangItem(LangItem::String).intern(db);
    let void_entity = EntityData::LangItem(LangItem::Tuple(0)).intern(db);

    match ty.base.untern(db).kind {
        lark_ty::BaseKind::Named(entity) => match entity {
            x if x == boolean_entity => "bool".into(),
            x if x == uint_entity => "unsigned int".into(),
            x if x == int_entity => "int".into(),
            x if x == string_entity => "char*".into(),
            x if x == void_entity => "void".into(),
            _ => unimplemented!("Unknown type: {:#?}", entity),
        },
        _ => unimplemented!("Unknown base kind"),
    }
}

pub fn build_decl_type(db: &LarkDatabase, ty: &Ty<lark_ty::declaration::Declaration>) -> String {
    let boolean_entity = EntityData::LangItem(LangItem::Boolean).intern(db);
    let uint_entity = EntityData::LangItem(LangItem::Uint).intern(db);
    let int_entity = EntityData::LangItem(LangItem::Int).intern(db);
    let string_entity = EntityData::LangItem(LangItem::String).intern(db);
    let void_entity = EntityData::LangItem(LangItem::Tuple(0)).intern(db);

    match ty.base.untern(db) {
        lark_ty::BoundVarOr::BoundVar(_) => unimplemented!("Bound variables not yet supported"),
        lark_ty::BoundVarOr::Known(ty) => match ty.kind {
            lark_ty::BaseKind::Named(entity) => {
                if entity == boolean_entity {
                    "bool".into()
                } else if entity == uint_entity {
                    "unsigned int".into()
                } else if entity == int_entity {
                    "int".into()
                } else if entity == string_entity {
                    "char*".into()
                } else if entity == void_entity {
                    "void".into()
                } else {
                    unimplemented!("Unknown type: {:#?}", entity)
                }
            }
            _ => unimplemented!("Unknown base kind"),
        },
    }
}

pub fn codegen_struct(
    db: &LarkDatabase,
    entity: Entity,
    id: lark_string::GlobalIdentifier,
) -> WithError<String> {
    let name = id.untern(db);
    let members = db.members(entity).unwrap();
    let mut output = String::new();
    let mut errors: Vec<Diagnostic> = vec![];

    output.push_str(&format!("typedef struct {} {{\n", name));

    for member in members.iter() {
        let member_name = member.name.untern(db);
        let member_ty = db.ty(member.entity).accumulate_errors_into(&mut errors);
        output.push_str(&format!(
            "{} {},\n",
            build_decl_type(db, &member_ty),
            member_name,
        ));
    }

    output.push_str("};\n");

    WithError {
        value: output,
        errors,
    }
}

pub fn build_expression(
    db: &LarkDatabase,
    fn_body: &std::sync::Arc<hir::FnBody>,
    fn_types: &std::sync::Arc<
        lark_type_check::TypeCheckResults<lark_ty::full_inferred::FullInferred>,
    >,
    expression: hir::Expression,
) -> String {
    match fn_body.tables[expression] {
        hir::ExpressionData::Let {
            variable,
            initializer,
            body,
        } => match initializer {
            Some(init_expression) => format!(
                "{{\n{} {} = {};\n{};\n}}",
                build_variable_type(db, fn_types, variable),
                build_variable_name(db, fn_body, variable),
                build_expression(db, fn_body, fn_types, init_expression),
                build_expression(db, fn_body, fn_types, body),
            ),
            None => format!(
                "{} {};\n",
                build_variable_type(db, fn_types, variable),
                build_variable_name(db, fn_body, variable)
            ),
        },

        hir::ExpressionData::Place { place } => build_place(db, fn_body, fn_types, place),

        hir::ExpressionData::Assignment { place, value } => format!(
            "{} = {};\n",
            build_place(db, fn_body, fn_types, place),
            build_expression(db, fn_body, fn_types, value)
        ),

        hir::ExpressionData::MethodCall { method, arguments } => {
            let mut arguments = arguments.iter(fn_body);
            let mut output = String::new();

            output.push_str(&build_expression(
                db,
                fn_body,
                fn_types,
                arguments.next().unwrap(),
            ));

            let method_name = fn_body.tables[method].text.untern(db);
            output.push_str(&format!(".{}(", method_name));

            let mut first = true;
            for argument in arguments {
                if !first {
                    output.push_str(", ");
                } else {
                    first = false;
                }
                output.push_str(&build_expression(db, fn_body, fn_types, argument));
            }
            output.push_str(")");

            output
        }

        hir::ExpressionData::Call {
            function,
            arguments,
        } => {
            let mut output = String::new();

            output.push_str(&build_expression(db, fn_body, fn_types, function));

            output.push_str("(");

            match fn_body[function] {
                hir::ExpressionData::Place {
                    place: function_place,
                } => match fn_body[function_place] {
                    hir::PlaceData::Entity(entity) => match entity.untern(db) {
                        EntityData::LangItem(LangItem::Debug) => {
                            output.push_str("\"");

                            let mut argument_formats = vec![];
                            for argument in arguments.iter(fn_body) {
                                argument_formats.push(build_format_for_type(
                                    db,
                                    fn_body,
                                    fn_types,
                                    &fn_types.ty(hir::MetaIndex::Expression(argument)),
                                    argument,
                                ));
                            }

                            let mut first = true;
                            for (argument_format, _) in argument_formats.iter() {
                                if !first {
                                    output.push_str(", ");
                                } else {
                                    first = false;
                                }
                                output.push_str(argument_format);
                            }

                            output.push_str("\"");

                            for (_, argument) in argument_formats.iter() {
                                output.push_str(", ");
                                output.push_str(&argument);
                            }

                            output.push_str(")");

                            return output;
                        }
                        _ => {}
                    },
                    _ => {}
                },
                _ => {}
            }

            let mut first = true;
            for argument in arguments.iter(fn_body) {
                if !first {
                    output.push_str(", ");
                } else {
                    first = false;
                }
                let argument_type = fn_types.ty(hir::MetaIndex::Expression(argument));
                output.push_str(&build_expression(db, fn_body, fn_types, argument));
            }
            output.push_str(")");

            output
        }

        hir::ExpressionData::Sequence { first, second } => format!(
            "{};\n {}",
            build_expression(db, fn_body, fn_types, first),
            build_expression(db, fn_body, fn_types, second)
        ),

        hir::ExpressionData::If {
            condition,
            if_true,
            if_false,
        } => format!(
            "if ({}) {{\n {} \n}} else {{\n {} \n}}",
            build_expression(db, fn_body, fn_types, condition),
            build_expression(db, fn_body, fn_types, if_true),
            build_expression(db, fn_body, fn_types, if_false)
        ),

        hir::ExpressionData::Binary {
            operator,
            left,
            right,
        } => format!(
            "({} {} {})",
            build_expression(db, fn_body, fn_types, left),
            match operator {
                hir::BinaryOperator::Add => "+",
                hir::BinaryOperator::Subtract => "-",
                hir::BinaryOperator::Multiply => "*",
                hir::BinaryOperator::Divide => "/",
                hir::BinaryOperator::Equals => "==",
                hir::BinaryOperator::NotEquals => "!=",
            },
            build_expression(db, fn_body, fn_types, right),
        ),

        hir::ExpressionData::Unary { operator, value } => format!(
            "{}({})",
            match operator {
                hir::UnaryOperator::Not => "!",
            },
            build_expression(db, fn_body, fn_types, value)
        ),

        hir::ExpressionData::Literal { data } => match data {
            hir::LiteralData {
                kind: hir::LiteralKind::String,
                value,
            } => format!("\"{}\"", value.untern(db)),
            hir::LiteralData {
                kind: hir::LiteralKind::UnsignedInteger,
                value,
            } => format!("{}", value.untern(db)),
        },

        hir::ExpressionData::Unit {} => "()".to_string(),

        hir::ExpressionData::Aggregate { entity, fields } => {
            let mut output = String::new();

            output.push_str("_build_struct_");
            output.push_str(&build_entity_name(db, entity));
            output.push_str("(");
            let mut first = true;
            for field in fields.iter(fn_body) {
                if !first {
                    output.push_str(", ");
                } else {
                    first = false;
                }

                let identified_expression = fn_body.tables[field];
                output.push_str(&format!(
                    "{}",
                    build_expression(db, fn_body, fn_types, identified_expression.expression),
                ));
            }
            output.push_str(")");
            output
        }

        hir::ExpressionData::Error { .. } => {
            panic!("Can not codegen in the presence of errors");
        }
    }
}

pub fn codegen_function(
    db: &LarkDatabase,
    entity: Entity,
    id: lark_string::GlobalIdentifier,
) -> WithError<String> {
    let mut output = String::new();
    let mut errors: Vec<Diagnostic> = vec![];

    let fn_body = db.fn_body(entity).accumulate_errors_into(&mut errors);
    let fn_types = db
        .full_type_check(entity)
        .accumulate_errors_into(&mut errors);

    let signature = db
        .signature(entity)
        .accumulate_errors_into(&mut errors)
        .unwrap();

    let arguments = fn_body.arguments.unwrap();

    let name = id.untern(db);

    output.push_str(&format!("{} ", build_decl_type(db, &signature.output)));
    output.push_str(&format!("{}(", name));

    let mut first = true;
    for (argument, argument_type) in arguments.iter(&fn_body).zip(signature.inputs.iter()) {
        let variable_data = fn_body.tables[argument];
        let identifier = fn_body.tables[variable_data.name];

        let argument_name = identifier.text.untern(db);

        if !first {
            output.push_str(", ");
        } else {
            first = false;
        }

        output.push_str(&format!("{}", build_decl_type(db, argument_type)));
        output.push_str(&format!(" {}", argument_name));
    }

    output.push_str(")");
    output.push_str(&format!(
        " {{\n{};\n}}\n",
        build_expression(db, &fn_body, &fn_types, fn_body.root_expression)
    ));

    WithError {
        value: output,
        errors,
    }
}

/// Converts the MIR context of definitions into Rust source
pub fn codegen_c(db: &LarkDatabase) -> WithError<String> {
    let mut output = String::new();
    let input_files = db.file_names();
    let mut errors: Vec<Diagnostic> = vec![];

    output.push_str("#include <stdio.h>\n");
    output.push_str("#include <stdbool.h>\n");

    for &input_file in &*input_files {
        let entities = db.top_level_entities_in_file(input_file);

        for &entity in &*entities {
            match entity.untern(&db) {
                EntityData::ItemName {
                    kind: ItemKind::Function,
                    id,
                    ..
                } => {
                    let mut result = codegen_function(db, entity, id);
                    if result.errors.len() > 0 {
                        errors.append(&mut result.errors);
                    } else {
                        output.push_str(&result.value);
                    }
                }
                EntityData::ItemName {
                    kind: ItemKind::Struct,
                    id,
                    ..
                } => {
                    let mut result = codegen_struct(db, entity, id);
                    if result.errors.len() > 0 {
                        errors.append(&mut result.errors);
                    } else {
                        output.push_str(&result.value);
                    }
                }
                x => unimplemented!("Can not codegen {:#?}", x.debug_with(db)),
            }
        }
    }

    println!("{}", output);

    WithError {
        value: output,
        errors,
    }
}
