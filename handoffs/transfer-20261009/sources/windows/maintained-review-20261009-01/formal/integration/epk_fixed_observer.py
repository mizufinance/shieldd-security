"""Fresh-only EPK fixed-loop hooks, preserving existing observers and Var order."""
from .balance_variable_observer import _text


def _replace(text, old, new):
    if text.count(old) != 1:
        raise ValueError('EPK fixed exact source anchor drift')
    return text.replace(old, new)


def instrument_group(data):
    text, newline = _text(data)
    if 'epk_fixed_inspection' in text:
        raise ValueError('EPK fixed group already activated')
    for old, call in [
        ('pub mod fixed_inspection;', 'pub mod epk_fixed_inspection;'),
        ('    fixed_inspection::quotient([&observed_numerators.0, &observed_numerators.1,\n        &dx, &dy, &output.x, &output.y]);',
         '    epk_fixed_inspection::quotient([&observed_numerators.0, &observed_numerators.1,\n        &dx, &dy, &output.x, &output.y]);'),
        ('    fixed_inspection::arithmetic([&xx, &yy, &sum_product, &xy_product]);',
         '    epk_fixed_inspection::arithmetic([&xx, &yy, &sum_product, &xy_product]);'),
        ('    fixed_inspection::begin_loop(&base, bits);', '    epk_fixed_inspection::begin_loop(&base, bits);'),
        ('        fixed_inspection::begin_window(_index);', '        epk_fixed_inspection::begin_window(_index);'),
        ('        fixed_inspection::finish_window(&base, &twice, &triple, &next_base, &result, &selected, &next);',
         '        epk_fixed_inspection::finish_window(&base, &twice, &triple, &next_base, &result, &selected, &next);'),
        ('    fixed_inspection::finish_loop(&result);', '    epk_fixed_inspection::finish_loop(&result);')]:
        indent = call[:len(call)-len(call.lstrip())]
        text = _replace(text, old, old+'\n'+indent+'#[cfg(feature = "formal-observer")]\n'+call)
    original='        ownership_inspection::nonidentity(&self.x, &_inverse);'
    replacement=original+'\n        #[cfg(feature = "formal-observer")]\n        epk_fixed_inspection::inverse(&_inverse);'
    text=_replace(text,original,replacement)
    return text.replace('\n',newline).encode()


def instrument_recovery(data):
    text, newline = _text(data)
    if 'epk_fixed_inspection' in text:
        raise ValueError('EPK recovery already activated')
    old = '    let computed_epk = group::generator().multiply_fixed(&bits);'
    new = '''    let epk_generator = group::generator();
    #[cfg(feature = "formal-observer")]
    let epk_fixed_scope = group::epk_fixed_inspection::scope(
        group::epk_fixed_inspection::Lane::Recovery, &epk_generator, &randomizer, &bits, &out.epk);
    let computed_epk = epk_generator.multiply_fixed(&bits);'''
    text=_replace(text,old,new)
    old='    let epk_inverse = out.epk.x.inv();'
    text=_replace(text,old,old+'''
    #[cfg(feature = "formal-observer")]
    group::epk_fixed_inspection::inverse(&epk_inverse);
    #[cfg(feature = "formal-observer")]
    drop(epk_fixed_scope);''')
    return text.replace('\n',newline).encode()


def instrument_encryption(data):
    text, newline = _text(data)
    if 'epk_fixed_inspection' in text:
        raise ValueError('EPK encryption already activated')
    old = '        let bits = scalar::canonical_bits(ctx, &var(&w.ephemeral[i]));'
    text = _replace(text,old,'        let epk_randomizer = var(&w.ephemeral[i]);\n        let bits = scalar::canonical_bits(ctx, &epk_randomizer);')
    old = '        generator.multiply_fixed(&bits).assert_equal(epks[i]);'
    new = '''        #[cfg(feature = "formal-observer")]
        let epk_fixed_scope = group::epk_fixed_inspection::scope(
            group::epk_fixed_inspection::Lane::Encryption, &generator, &epk_randomizer, &bits, epks[i]);
        generator.multiply_fixed(&bits).assert_equal(epks[i]);'''
    text=_replace(text,old,new)
    old='        epks[i].assert_non_identity();'
    text=_replace(text,old,old+'''
        #[cfg(feature = "formal-observer")]
        drop(epk_fixed_scope);''')
    return text.replace('\n',newline).encode()


def instrument_catalogue(data):
    text,newline = _text(data)
    if 'epk_fixed_catalogue.rs' in text:
        raise ValueError('EPK catalogue already activated')
    return (text+'\n#[cfg(feature = "formal-observer")]\ninclude!("epk_fixed_catalogue.rs");\n').replace('\n',newline).encode()


def instrument_exporter(data, fragment):
    text, newline = _text(data)
    if 'capture_epk_fixed_pages(' in text:
        raise ValueError('EPK fixed exporter already activated')
    if not isinstance(fragment, bytes) or any(fragment.count(name) != 1 for name in
        (b'fn capture_epk_fixed_pages(',b'fn qualify_epk_fixed_pages(',b'fn qualify_epk_fixed_page(',b'fn read_epk_fixed_page(',
         b'fn capture_epk_all_fixed_pages(',b'fn qualify_epk_all_fixed_pages(')):
        raise ValueError('EPK fixed complete exporter resource required')
    args='    let args: Vec<_> = std::env::args().skip(1).collect();'
    text=_replace(text,args,args+"\n    if args.len() == 4 && args[0] == \"epk-fixed-pages-spool\" {\n        return capture_epk_fixed_pages(&args[1],args[2].parse()?,&args[3]);\n    }")
    text=_replace(text,args,args+'\n    if args.len() == 2 && args[0] == "epk-all-fixed-pages-spool" {\n        return capture_epk_all_fixed_pages(&args[1]);\n    }')
    schema='        Some("shieldd-transfer-note-spend-v1") |'
    text=_replace(text,schema,schema+'\n        Some("shieldd-transfer-epk-fixed-pages-v1") |')
    text=_replace(text,schema,schema+'\n        Some("shieldd-transfer-epk-all-fixed-pages-v1") |')
    flag='            pending["repeated_observations_equal"] = json!(true);'
    text=_replace(text,flag,'            if pending["schema"] == "shieldd-transfer-epk-fixed-pages-v1" {\n                ensure_epk_fixed_original_layout(&read_packet_json(first,"shape.json")?)?;\n                qualify_epk_fixed_pages(first,repeated,&pending)?;\n            }\n'+flag)
    text=_replace(text,flag,'            if pending["schema"] == "shieldd-transfer-epk-all-fixed-pages-v1" {\n                ensure_epk_fixed_original_layout(&read_packet_json(first,"shape.json")?)?;\n                qualify_epk_all_fixed_pages(first,repeated,&pending)?;\n            }\n'+flag)
    return (text+'\n'+fragment.decode().replace('\r\n','\n')).replace('\n',newline).encode()
