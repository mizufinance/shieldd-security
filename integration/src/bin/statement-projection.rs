//! A closed symbolic interpreter for the two deployed field-projection methods.
//!
//! This is a reviewed extraction boundary, not a Rust semantics proof. It treats
//! Clone on the deployed Scalar/Var field types as value-preserving. It rejects
//! unknown syntax instead of evaluating arbitrary Rust or guessing field order.
use serde_json::json;
use std::{collections::BTreeMap, fs, path::Path};
use syn::{Expr, Fields, GenericArgument, ImplItem, Item, Member, Pat, PathArguments, Stmt, Type};

type Result<T> = std::result::Result<T, String>;

#[derive(Clone, Debug)]
enum Value {
    Field(String),
    Record(String, BTreeMap<String, Value>),
    Sequence(Vec<Value>),
}

fn plain(attrs: &[syn::Attribute]) -> Result<()> {
    for attr in attrs {
        // Documentation and Clone derivation cannot conditionally select code.
        if attr.path().is_ident("doc") {
            continue;
        }
        if attr.path().is_ident("derive") {
            let parsed = attr.parse_args_with(
                syn::punctuated::Punctuated::<syn::Path, syn::Token![,]>::parse_terminated,
            );
            if parsed.is_ok_and(|ps| {
                ps.iter().all(|p| {
                    ["Clone", "Debug", "PartialEq", "Eq"]
                        .iter()
                        .any(|name| p.is_ident(name))
                })
            }) {
                continue;
            }
        }
        return Err("unsupported attribute on a projection declaration".into());
    }
    Ok(())
}

struct Source {
    files: BTreeMap<String, syn::File>,
    imports: BTreeMap<String, BTreeMap<String, Vec<String>>>,
}

fn imports(
    tree: &syn::UseTree,
    prefix: &[String],
    output: &mut BTreeMap<String, Vec<String>>,
) -> Result<()> {
    let (name, target) = match tree {
        syn::UseTree::Path(p) => {
            let mut next = prefix.to_vec();
            next.push(p.ident.to_string());
            return imports(&p.tree, &next, output);
        }
        syn::UseTree::Group(g) => {
            for item in &g.items {
                imports(item, prefix, output)?;
            }
            return Ok(());
        }
        syn::UseTree::Name(n) if n.ident == "self" => (
            prefix.last().ok_or("bare self import")?.clone(),
            prefix.to_vec(),
        ),
        syn::UseTree::Name(n) => {
            let mut target = prefix.to_vec();
            target.push(n.ident.to_string());
            (n.ident.to_string(), target)
        }
        syn::UseTree::Rename(n) => {
            let mut target = prefix.to_vec();
            target.push(n.ident.to_string());
            (n.rename.to_string(), target)
        }
        _ => return Err("glob import may change projection name resolution".into()),
    };
    if output.insert(name, target).is_some() {
        return Err("ambiguous import".into());
    }
    Ok(())
}

impl Source {
    fn read(root: &Path) -> Result<Self> {
        let lib =
            syn::parse_file(&fs::read_to_string(root.join("lib.rs")).map_err(|e| e.to_string())?)
                .map_err(|e| e.to_string())?;
        plain(&lib.attrs)?;
        if lib.items.iter().any(|i| matches!(i, Item::Macro(_))) {
            return Err("crate-level macro may change module dispatch".into());
        }
        for item in &lib.items {
            match item {
                Item::ExternCrate(_) => {
                    return Err("extern crate macro dispatch unsupported".into());
                }
                Item::Mod(module)
                    if module.attrs.iter().any(|a| a.path().is_ident("macro_use")) =>
                {
                    return Err("module macro imports unsupported".into());
                }
                Item::Use(item) => {
                    plain(&item.attrs)?;
                    let mut imported = BTreeMap::new();
                    imports(&item.tree, &[], &mut imported)?;
                    if imported
                        .keys()
                        .any(|n| ["vec", "Vec", "Clone"].contains(&n.as_str()))
                    {
                        return Err("crate import shadows standard projection operation".into());
                    }
                }
                _ => (),
            }
        }
        for name in ["transfer", "encryption", "audit", "group"] {
            let modules: Vec<_> = lib
                .items
                .iter()
                .filter_map(|i| match i {
                    Item::Mod(m) if m.ident == name => Some(m),
                    _ => None,
                })
                .collect();
            let [module] = modules.as_slice() else {
                return Err("ambiguous projection source module".into());
            };
            plain(&module.attrs)?;
            if module.content.is_some() {
                return Err("inline projection module unsupported".into());
            }
        }
        let mut files = BTreeMap::new();
        let mut resolved = BTreeMap::new();
        for module in ["transfer", "encryption", "audit", "group"] {
            let text =
                fs::read_to_string(root.join(format!("{module}.rs"))).map_err(|e| e.to_string())?;
            let parsed = syn::parse_file(&text).map_err(|e| e.to_string())?;
            plain(&parsed.attrs)?;
            let mut imported = BTreeMap::new();
            for item in &parsed.items {
                match item {
                    Item::Use(item) => {
                        plain(&item.attrs)?;
                        imports(&item.tree, &[], &mut imported)?;
                    }
                    Item::Macro(_) => {
                        return Err("top-level macro may alter projection declarations".into());
                    }
                    Item::ExternCrate(_) => {
                        return Err("extern crate macro dispatch unsupported".into());
                    }
                    Item::Mod(module)
                        if module.attrs.iter().any(|a| a.path().is_ident("macro_use")) =>
                    {
                        return Err("module macro imports unsupported".into());
                    }
                    _ => (),
                }
            }
            for reserved in ["Clone", "Vec", "vec"] {
                if imported.contains_key(reserved)
                    || parsed.items.iter().any(|i| match i {
                        Item::Struct(s) => s.ident == reserved,
                        Item::Type(t) => t.ident == reserved,
                        Item::Trait(t) => t.ident == reserved,
                        _ => false,
                    })
                {
                    return Err("shadowed standard projection operation".into());
                }
            }
            resolved.insert(module.into(), imported);
            files.insert(module.into(), parsed);
        }
        Ok(Self {
            files,
            imports: resolved,
        })
    }

    fn record(&self, module: &str, name: &str, prefix: &str, depth: usize) -> Result<Value> {
        if depth > 8 {
            return Err("recursive or unsupported projection type".into());
        }
        if self.imports[module].contains_key(name)
            || self.files[module]
                .items
                .iter()
                .any(|i| matches!(i, Item::Type(t) if t.ident == name))
        {
            return Err("ambiguous record/import/type alias".into());
        }
        let matches: Vec<_> = self.files[module]
            .items
            .iter()
            .filter_map(|item| match item {
                Item::Struct(s) if s.ident == name => Some(s),
                _ => None,
            })
            .collect();
        let [item] = matches.as_slice() else {
            return Err(format!("missing or ambiguous {module}::{name}"));
        };
        plain(&item.attrs)?;
        if item.generics.params.len() != 1 || item.generics.where_clause.is_some() {
            return Err("unsupported generic record".into());
        }
        let syn::GenericParam::Type(param) = &item.generics.params[0] else {
            return Err("non-type generic".into());
        };
        plain(&param.attrs)?;
        if param.ident != "F" || !param.bounds.is_empty() || param.default.is_some() {
            return Err("unexpected field type parameter".into());
        }
        let Fields::Named(fields) = &item.fields else {
            return Err("non-record type".into());
        };
        let mut result = BTreeMap::new();
        for field in &fields.named {
            plain(&field.attrs)?;
            let key = field.ident.as_ref().unwrap().to_string();
            let path = format!("{prefix}.{key}");
            result.insert(key, self.value(module, &field.ty, &path, depth + 1)?);
        }
        Ok(Value::Record(format!("{module}::{name}"), result))
    }

    fn value(&self, module: &str, ty: &Type, path: &str, depth: usize) -> Result<Value> {
        if let Type::Array(array) = ty {
            let Expr::Lit(lit) = &array.len else {
                return Err("array length must be a literal".into());
            };
            let syn::Lit::Int(n) = &lit.lit else {
                return Err("array length must be an integer".into());
            };
            let n: usize = n.base10_parse().map_err(|e| e.to_string())?;
            if n > 8 {
                return Err("unsupported array width".into());
            }
            return (0..n)
                .map(|i| self.value(module, &array.elem, &format!("{path}[{i}]"), depth + 1))
                .collect::<Result<Vec<_>>>()
                .map(Value::Sequence);
        }
        let Type::Path(p) = ty else {
            return Err("unsupported field type".into());
        };
        if p.qself.is_some() || p.path.leading_colon.is_some() {
            return Err("qualified type unsupported".into());
        }
        if p.path.is_ident("F") {
            return Ok(Value::Field(path.into()));
        }
        let names: Vec<_> = p
            .path
            .segments
            .iter()
            .map(|s| s.ident.to_string())
            .collect();
        if p.path
            .segments
            .iter()
            .take(p.path.segments.len() - 1)
            .any(|s| !matches!(s.arguments, PathArguments::None))
        {
            return Err("generic module path unsupported".into());
        }
        let last = p.path.segments.last().unwrap();
        let PathArguments::AngleBracketed(arguments) = &last.arguments else {
            return Err("type alias or unparameterized record".into());
        };
        if arguments.args.len() != 1
            || !matches!(&arguments.args[0], GenericArgument::Type(Type::Path(f)) if f.path.is_ident("F"))
        {
            return Err("non-field record instantiation".into());
        }
        let mut target = self.imports[module]
            .get(&names[0])
            .cloned()
            .unwrap_or_else(|| vec!["crate".into(), module.into(), names[0].clone()]);
        target.extend(names.iter().skip(1).cloned());
        let [krate, owner, name] = target.as_slice() else {
            return Err("unknown record type path".into());
        };
        if krate != "crate" || !self.files.contains_key(owner) {
            return Err("external record type unsupported".into());
        }
        self.record(owner, name, path, depth)
    }

    fn method(&self, module: &str, record: &str) -> Result<&syn::ImplItemFn> {
        let mut methods = Vec::new();
        for item in &self.files[module].items {
            let Item::Impl(implementation) = item else {
                continue;
            };
            let Type::Path(ty) = implementation.self_ty.as_ref() else {
                continue;
            };
            if ty.path.segments.last().is_none_or(|s| s.ident != record) {
                continue;
            }
            for item in &implementation.items {
                if let ImplItem::Fn(method) = item {
                    if method.sig.ident == "fields" {
                        plain(&implementation.attrs)?;
                        plain(&method.attrs)?;
                        if implementation.trait_.is_some()
                            || implementation.unsafety.is_some()
                            || method.sig.asyncness.is_some()
                            || method.sig.unsafety.is_some()
                            || method.sig.constness.is_some()
                            || method.sig.inputs.len() != 1
                            || !method.sig.generics.params.is_empty()
                            || method.sig.generics.where_clause.is_some()
                            || method.sig.abi.is_some()
                            || method.sig.variadic.is_some()
                        {
                            return Err("unsupported fields method dispatch".into());
                        }
                        if ty.path.segments.len() != 1
                            || implementation.generics.where_clause.is_some()
                            || implementation.generics.params.len() != 1
                        {
                            return Err("unsupported impl type".into());
                        }
                        let syn::GenericParam::Type(f) = &implementation.generics.params[0] else {
                            return Err("unsupported impl generic".into());
                        };
                        plain(&f.attrs)?;
                        let PathArguments::AngleBracketed(arguments) =
                            &ty.path.segments[0].arguments
                        else {
                            return Err("missing field type argument".into());
                        };
                        if arguments.args.len() != 1
                            || !matches!(&arguments.args[0], GenericArgument::Type(Type::Path(t)) if t.path.is_ident("F"))
                        {
                            return Err("wrong impl field type".into());
                        }
                        if f.ident != "F"
                            || f.default.is_some()
                            || f.bounds.len() != 1
                            || !matches!(&f.bounds[0], syn::TypeParamBound::Trait(bound) if bound.path.is_ident("Clone") && bound.lifetimes.is_none())
                        {
                            return Err("unexpected projection Clone bound".into());
                        }
                        let syn::FnArg::Receiver(receiver) = &method.sig.inputs[0] else {
                            return Err("projection needs self receiver".into());
                        };
                        plain(&receiver.attrs)?;
                        if receiver.reference.is_none()
                            || receiver.mutability.is_some()
                            || receiver.colon_token.is_some()
                        {
                            return Err("unsupported self receiver".into());
                        }
                        self.output_width(module, record, &method.sig.output)?;
                        methods.push(method);
                    }
                }
            }
        }
        let [method] = methods.as_slice() else {
            return Err("missing or ambiguous fields implementation".into());
        };
        Ok(method)
    }

    fn output_width(&self, module: &str, record: &str, output: &syn::ReturnType) -> Result<usize> {
        let syn::ReturnType::Type(_, ty) = output else {
            return Err("missing array return type".into());
        };
        let Type::Array(array) = ty.as_ref() else {
            return Err("projection must return fixed array".into());
        };
        if !matches!(array.elem.as_ref(), Type::Path(f) if f.path.is_ident("F")) {
            return Err("non-field output array".into());
        }
        let width = match (&array.len, module, record) {
            (Expr::Lit(lit), "audit", "Ciphertext") => match &lit.lit {
                syn::Lit::Int(n) => n.base10_parse::<usize>().map_err(|e| e.to_string())?,
                _ => return Err("invalid helper array width".into()),
            },
            (Expr::Path(p), "transfer", "Statement") if p.path.is_ident("STATEMENT_FIELDS") => {
                let constants: Vec<_> = self.files[module]
                    .items
                    .iter()
                    .filter_map(|i| match i {
                        Item::Const(c) if c.ident == "STATEMENT_FIELDS" => Some(c),
                        _ => None,
                    })
                    .collect();
                let [constant] = constants.as_slice() else {
                    return Err("missing or ambiguous statement width".into());
                };
                plain(&constant.attrs)?;
                if self.imports[module].contains_key("STATEMENT_FIELDS")
                    || !matches!(constant.ty.as_ref(), Type::Path(t) if t.path.is_ident("usize"))
                {
                    return Err("ambiguous statement width type".into());
                }
                let Expr::Lit(lit) = constant.expr.as_ref() else {
                    return Err("nonliteral statement width".into());
                };
                let syn::Lit::Int(n) = &lit.lit else {
                    return Err("noninteger statement width".into());
                };
                n.base10_parse::<usize>().map_err(|e| e.to_string())?
            }
            _ => return Err("unsupported projection output type".into()),
        };
        if width != if record == "Statement" { 64 } else { 4 } {
            return Err("changed projection width".into());
        }
        Ok(width)
    }
}

struct Interpreter<'a> {
    source: &'a Source,
    env: BTreeMap<String, Value>,
}

impl Interpreter<'_> {
    fn sequence(value: Value) -> Result<Vec<Value>> {
        match value {
            Value::Sequence(xs) => Ok(xs),
            _ => Err("expected fixed sequence".into()),
        }
    }

    fn expr(&self, expr: &Expr) -> Result<Value> {
        match expr {
            Expr::Path(p)
                if p.attrs.is_empty() && p.qself.is_none() && p.path.segments.len() == 1 =>
            {
                self.env
                    .get(&p.path.segments[0].ident.to_string())
                    .cloned()
                    .ok_or("unbound projection name".into())
            }
            Expr::Reference(r) if r.attrs.is_empty() && r.mutability.is_none() => {
                self.expr(&r.expr)
            }
            Expr::Field(f) if f.attrs.is_empty() => {
                let Value::Record(_, fields) = self.expr(&f.base)? else {
                    return Err("field projection on non-record".into());
                };
                let Member::Named(name) = &f.member else {
                    return Err("tuple field projection unsupported".into());
                };
                fields
                    .get(&name.to_string())
                    .cloned()
                    .ok_or("unknown field name".into())
            }
            Expr::Array(a) if a.attrs.is_empty() => a
                .elems
                .iter()
                .map(|e| self.expr(e))
                .collect::<Result<Vec<_>>>()
                .map(Value::Sequence),
            Expr::Tuple(a) if a.attrs.is_empty() => a
                .elems
                .iter()
                .map(|e| self.expr(e))
                .collect::<Result<Vec<_>>>()
                .map(Value::Sequence),
            Expr::Macro(m) if m.attrs.is_empty() && m.mac.path.is_ident("vec") => {
                use syn::parse::Parser;
                let expressions =
                    syn::punctuated::Punctuated::<Expr, syn::Token![,]>::parse_terminated
                        .parse2(m.mac.tokens.clone())
                        .map_err(|e| e.to_string())?;
                expressions
                    .iter()
                    .map(|e| self.expr(e))
                    .collect::<Result<Vec<_>>>()
                    .map(Value::Sequence)
            }
            Expr::MethodCall(call)
                if call.attrs.is_empty() && call.turbofish.is_none() && call.args.is_empty() =>
            {
                let value = self.expr(&call.receiver)?;
                if call.method == "clone" {
                    // Arrays in this method contain only field elements. Their
                    // standard Clone reduces to the same deployed field Clone.
                    if matches!(&value, Value::Field(_))
                        || matches!(&value, Value::Sequence(xs) if xs.iter().all(|x| matches!(x, Value::Field(_))))
                    {
                        return Ok(value);
                    }
                    return Err("record or nested aggregate Clone unsupported".into());
                }
                if call.method != "fields" {
                    return Err("unknown method call".into());
                }
                // This is the only helper dispatch admitted by this interpreter.
                let Value::Record(ref identity, _) = value else {
                    return Err("fields on non-record".into());
                };
                if identity != "audit::Ciphertext" {
                    return Err("helper must be audit::Ciphertext::fields".into());
                }
                let mut child = Interpreter {
                    source: self.source,
                    env: BTreeMap::from([("self".into(), value)]),
                };
                let result = child.block(&self.source.method("audit", "Ciphertext")?.block)?;
                if !matches!(&result, Value::Sequence(xs) if xs.len() == 4) {
                    return Err("helper projection width mismatch".into());
                }
                Ok(result)
            }
            _ => Err("unsupported projection expression".into()),
        }
    }

    fn bind(&mut self, pattern: &Pat, value: Value) -> Result<()> {
        match pattern {
            Pat::Ident(p) if p.attrs.is_empty() && p.by_ref.is_none() && p.subpat.is_none() => {
                let name = p.ident.to_string();
                if self.env.contains_key(&name) {
                    return Err("shadowed or duplicate projection binding".into());
                }
                self.env.insert(name, value);
                Ok(())
            }
            Pat::Tuple(p) if p.attrs.is_empty() => {
                let xs = Self::sequence(value)?;
                if xs.len() != p.elems.len() {
                    return Err("tuple pattern width mismatch".into());
                }
                for (p, x) in p.elems.iter().zip(xs) {
                    self.bind(p, x)?;
                }
                Ok(())
            }
            _ => Err("unsupported binding pattern".into()),
        }
    }

    fn statement(&mut self, statement: &Stmt) -> Result<()> {
        match statement {
            Stmt::Local(local) if local.attrs.is_empty() => {
                let init = local.init.as_ref().ok_or("uninitialized binding")?;
                if init.diverge.is_some() {
                    return Err("let-else unsupported".into());
                }
                self.bind(&local.pat, self.expr(&init.expr)?)
            }
            Stmt::Expr(Expr::ForLoop(loop_), None)
                if loop_.attrs.is_empty() && loop_.label.is_none() =>
            {
                for value in Self::sequence(self.expr(&loop_.expr)?)? {
                    let old = self.env.clone();
                    self.bind(&loop_.pat, value)?;
                    for statement in &loop_.body.stmts {
                        self.statement(statement)?;
                    }
                    // The sole mutated variable is the output accumulator.
                    let output = self.env.get("f").cloned().ok_or("missing accumulator")?;
                    self.env = old;
                    self.env.insert("f".into(), output);
                }
                Ok(())
            }
            Stmt::Expr(Expr::MethodCall(call), Some(_))
                if call.attrs.is_empty() && call.turbofish.is_none() && call.args.len() == 1 =>
            {
                let Expr::Path(receiver) = call.receiver.as_ref() else {
                    return Err("nonlocal mutation".into());
                };
                if !receiver.path.is_ident("f") {
                    return Err("only accumulator mutation allowed".into());
                }
                let arg = self.expr(&call.args[0])?;
                let values = if call.method == "extend" {
                    Self::sequence(arg)?
                } else if call.method == "push" {
                    vec![arg]
                } else {
                    return Err("unknown accumulator operation".into());
                };
                let Some(Value::Sequence(output)) = self.env.get_mut("f") else {
                    return Err("invalid accumulator".into());
                };
                output.extend(values);
                Ok(())
            }
            _ => Err("unsupported projection statement".into()),
        }
    }

    fn block(&mut self, block: &syn::Block) -> Result<Value> {
        let (last, prefix) = block.stmts.split_last().ok_or("empty projection")?;
        for statement in prefix {
            self.statement(statement)?;
        }
        let Stmt::Expr(tail, None) = last else {
            return Err("missing projection return".into());
        };
        if let Expr::MethodCall(unwrap) = tail {
            if unwrap.method == "unwrap_or_else"
                && unwrap.args.len() == 1
                && unwrap.attrs.is_empty()
                && unwrap.turbofish.is_none()
                && matches!(&unwrap.args[0], Expr::Closure(_))
            {
                let Expr::MethodCall(convert) = unwrap.receiver.as_ref() else {
                    return Err("unsupported conversion".into());
                };
                if convert.method != "try_into"
                    || !convert.args.is_empty()
                    || convert.turbofish.is_some()
                    || !convert.attrs.is_empty()
                {
                    return Err("unsupported final conversion".into());
                }
                // Caller checks exact output array width, proving this fallback
                // closure unreachable for the interpreted fixed projection.
                return self.expr(&convert.receiver);
            }
        }
        self.expr(tail)
    }
}

fn main() -> Result<()> {
    let root = std::env::args()
        .nth(1)
        .ok_or("expected exact runtime circuit-source directory")?;
    let source = Source::read(Path::new(&root))?;
    let method = source.method("transfer", "Statement")?;
    let value = source.record("transfer", "Statement", "self", 0)?;
    let mut interpreter = Interpreter {
        source: &source,
        env: BTreeMap::from([("self".into(), value)]),
    };
    let fields = Interpreter::sequence(interpreter.block(&method.block)?)?;
    let paths = fields
        .into_iter()
        .map(|value| match value {
            Value::Field(path) => Ok(path),
            _ => Err("non-field in final projection".into()),
        })
        .collect::<Result<Vec<_>>>()?;
    if paths.len() != 64 {
        return Err("Transfer projection width is not 64".into());
    }
    println!("{}", serde_json::to_string_pretty(&json!({
        "subject":"Transfer Rust structural field projection", "paths":paths,
        "source_files":["lib.rs","transfer.rs","encryption.rs","audit.rs","group.rs"],
        "trusted_boundary":"syn parsing; closed interpreter and checked module/import resolution; deployed Scalar/Var Clone preserves value",
        "excluded":"canonical bytes, curve membership, hash security, public input/VK binding and authorization"
    })).unwrap());
    Ok(())
}
