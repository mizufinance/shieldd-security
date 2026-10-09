"""Additive VALUE_BLINDING trace hooks for a fresh EPK/balance sibling.

No observer changes the ordinary Var sequence. The blinding trace has a genuine
distinct schema and permits zero; EPK/spend capture metadata is never converted.
"""
from .balance_variable_observer import _text


def _replace(text, old, new):
    if text.count(old) != 1:
        raise ValueError('balance blinding exact source anchor drift')
    return text.replace(old, new)


def instrument_group(data):
    text,newline=_text(data)
    if 'balance_blinding_fixed_inspection' in text:
        raise ValueError('balance blinding group already activated')
    for old,call in [
        ('pub mod fixed_inspection;', 'pub mod balance_blinding_fixed_inspection;'),
        ('    fixed_inspection::quotient([&observed_numerators.0, &observed_numerators.1,\n        &dx, &dy, &output.x, &output.y]);',
         '    balance_blinding_fixed_inspection::quotient([&observed_numerators.0, &observed_numerators.1,\n        &dx, &dy, &output.x, &output.y]);'),
        ('    fixed_inspection::arithmetic([&xx, &yy, &sum_product, &xy_product]);',
         '    balance_blinding_fixed_inspection::arithmetic([&xx, &yy, &sum_product, &xy_product]);'),
        ('    fixed_inspection::begin_loop(&base, bits);','    balance_blinding_fixed_inspection::begin_loop(&base, bits);'),
        ('        fixed_inspection::begin_window(_index);','        balance_blinding_fixed_inspection::begin_window(_index);'),
        ('        fixed_inspection::finish_window(&base, &twice, &triple, &next_base, &result, &selected, &next);',
         '        balance_blinding_fixed_inspection::finish_window(&base, &twice, &triple, &next_base, &result, &selected, &next);'),
        ('    fixed_inspection::finish_loop(&result);','    balance_blinding_fixed_inspection::finish_loop(&result);')]:
        indent=call[:len(call)-len(call.lstrip())]
        text=_replace(text,old,old+'\n'+indent+'#[cfg(feature = "formal-observer")]\n'+call)
    return text.replace('\n',newline).encode()


def instrument_balance(data):
    text,newline=_text(data)
    if 'balance_blinding_fixed_inspection' in text:
        raise ValueError('balance blinding balance already activated')
    old='    let blinded = generators\n        .blinding\n        .multiply_fixed(&scalar::canonical_bits(ctx, blinding));'
    new='''    let blinding_bits = scalar::canonical_bits(ctx, blinding);
    #[cfg(feature = "formal-observer")]
    let balance_blinding_scope = crate::group::balance_blinding_fixed_inspection::scope(
        &generators.blinding, blinding, &blinding_bits);
    let blinded = generators.blinding.multiply_fixed(&blinding_bits);
    #[cfg(feature = "formal-observer")]
    drop(balance_blinding_scope);'''
    text=_replace(text,old,new)
    return text.replace('\n',newline).encode()


def instrument_catalogue(data):
    text,newline=_text(data)
    if 'balance_blinding_fixed_catalogue.rs' in text:
        raise ValueError('balance blinding catalogue already activated')
    return (text+'\n#[cfg(feature = "formal-observer")]\ninclude!("balance_blinding_fixed_catalogue.rs");\n').replace('\n',newline).encode()


def instrument_exporter(data,fragment):
    text,newline=_text(data)
    if 'capture_balance_blinding_fixed_pages(' in text:
        raise ValueError('balance blinding exporter already activated')
    names=(b'fn capture_balance_blinding_fixed_pages(',b'fn qualify_balance_blinding_fixed_pages(',
           b'fn qualify_balance_blinding_fixed_page(',b'fn read_balance_blinding_fixed_page(')
    if not isinstance(fragment,bytes) or any(fragment.count(name)!=1 for name in names):
        raise ValueError('balance blinding complete exporter required')
    args='    let args: Vec<_> = std::env::args().skip(1).collect();'
    text=_replace(text,args,args+'\n    if args.len() == 2 && args[0] == "balance-blinding-fixed-pages-spool" {\n        return capture_balance_blinding_fixed_pages(&args[1]);\n    }')
    schema='        Some("shieldd-transfer-note-spend-v1") |'
    text=_replace(text,schema,schema+'\n        Some("shieldd-transfer-balance-blinding-fixed-pages-v1") |')
    flag='            pending["repeated_observations_equal"] = json!(true);'
    text=_replace(text,flag,'            if pending["schema"] == "shieldd-transfer-balance-blinding-fixed-pages-v1" {\n                ensure_balance_blinding_original_layout(&read_packet_json(first,"shape.json")?)?;\n                qualify_balance_blinding_fixed_pages(first,repeated,&pending)?;\n            }\n'+flag)
    return (text+'\n'+fragment.decode().replace('\r\n','\n')).replace('\n',newline).encode()
