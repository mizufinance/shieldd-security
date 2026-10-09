"""Future-only bounded 129-bit balance affine-variable source companion.

Exact reviewed operation bodies remain in place. The new calls only inspect
existing Vars; a later exporter must independently lower the selected LCs and
qualify the complete ordinary relation and repeat observation.
"""


def _text(data):
    if not isinstance(data,bytes):raise ValueError('balance variable source bytes required')
    newline='\r\n' if b'\r\n' in data else '\n'
    text=data.decode()
    if newline=='\r\n' and '\n' in text.replace('\r\n',''):
        raise ValueError('balance variable mixed line endings')
    return text.replace('\r\n','\n'),newline


def instrument_group(data):
    text,newline=_text(data)
    if 'balance_variable_inspection' in text:raise ValueError('balance variable group already activated')
    def insert(anchor,addition):
        nonlocal text
        if text.count(anchor)!=1:raise ValueError('balance variable reviewed group anchor drift')
        text=text.replace(anchor,anchor+addition)
    insert('pub mod ownership_inspection;', '\n#[cfg(feature = "formal-observer")]\npub mod balance_variable_inspection;')
    insert('''    fixed_inspection::quotient([&observed_numerators.0, &observed_numerators.1,
        &dx, &dy, &output.x, &output.y]);''','''
    #[cfg(feature = "formal-observer")]
    balance_variable_inspection::quotient([&observed_numerators.0, &observed_numerators.1,
        &dx, &dy, &output.x, &output.y]);''')
    start="fn affine_variable<'a>(";end="\nfn affine_fixed<'a>("
    if text.count(start)!=1 or text.count(end)!=1:raise ValueError('balance variable exact loop boundary drift')
    prefix,body=text.split(start);body,suffix=body.split(end)
    for operation in ('    let twice = double(base);','    let triple = add(&twice, base);',
                      '        let first = double(&result);','        let second = double(&first);',
                      '        let selected = select(base, &twice, &triple, pair);',
                      '        let next = add(&second, &selected);'):
        if body.count(operation)!=1:raise ValueError('balance variable reviewed arithmetic drift')
    replacements={
        '    let mut result = Point::identity();':'''    #[cfg(feature = "formal-observer")]
    balance_variable_inspection::begin_loop(base, bits, &twice, &triple);
    #[cfg(feature = "formal-observer")]
    let mut balance_window_index = 0;
    let mut result = Point::identity();''',
        '    for pair in bits.chunks(2).rev() {':'''    for pair in bits.chunks(2).rev() {
        #[cfg(feature = "formal-observer")]
        balance_variable_inspection::begin_window(balance_window_index);''',
        '        result = next;':'''        #[cfg(feature = "formal-observer")]
        {
            balance_variable_inspection::finish_window(balance_window_index, pair,
                [&result, &first, &second, &selected, &next]);
            balance_window_index += 1;
        }
        result = next;''',
        '    result\n}':'''    #[cfg(feature = "formal-observer")]
    balance_variable_inspection::finish_loop(&result);
    result
}'''}
    for old,new in replacements.items():
        if body.count(old)!=1:raise ValueError('balance variable operation body drift')
        body=body.replace(old,new)
    return (prefix+start+body+end+suffix).replace('\n',newline).encode()


def instrument_balance(data):
    text,newline=_text(data)
    if 'balance_variable_inspection' in text:raise ValueError('balance variable balance already activated')
    old='    let mut value = generator.multiply_bits(&magnitude_bits);'
    if text.count(old)!=1:raise ValueError('balance variable multiply boundary drift')
    new='''    #[cfg(feature = "formal-observer")]
    let balance_variable_scope = crate::group::balance_variable_inspection::scope(
        &generator, &negative, &magnitude, &magnitude_bits);
    let mut value = generator.multiply_bits(&magnitude_bits);
    #[cfg(feature = "formal-observer")]
    drop(balance_variable_scope);'''
    return text.replace(old,new).replace('\n',newline).encode()


def instrument_catalogue(data):
    text,newline=_text(data)
    if 'balance_variable_catalogue.rs' in text:raise ValueError('balance variable catalogue already activated')
    return (text+'\n#[cfg(feature = "formal-observer")]\ninclude!("balance_variable_catalogue.rs");\n').replace('\n',newline).encode()


def instrument_exporter(data,fragment):
    text,newline=_text(data)
    if 'capture_balance_variable(' in text:raise ValueError('balance variable exporter already activated')
    if not isinstance(fragment,bytes):raise ValueError('balance variable exporter fragment bytes required')
    for definition in (b'fn capture_balance_variable(',b'fn qualify_balance_variable(',
                       b'fn capture_balance_variable_pages(',b'fn qualify_balance_variable_pages('):
        if fragment.count(definition)!=1:raise ValueError('balance variable complete single/paged exporter definitions required')
    args='    let args: Vec<_> = std::env::args().skip(1).collect();'
    schema='        Some("shieldd-transfer-note-spend-v1") |'
    flag='            pending["repeated_observations_equal"] = json!(true);'
    for anchor in (args,schema,flag):
        if text.count(anchor)!=1:raise ValueError('balance variable exporter dispatch/qualification drift')
    text=text.replace(args,args+'''\n    if args.len() == 4 && args[0] == "balance-variable-spool" {
        return capture_balance_variable(args[1].parse()?, args[2].parse()?, &args[3]);
    }
    if args.len() == 2 && args[0] == "balance-variable-pages-spool" {
        return capture_balance_variable_pages(&args[1]);
    }''')
    text=text.replace(schema,schema+'\n        Some("shieldd-transfer-balance-variable-v1") |\n        Some("shieldd-transfer-balance-variable-pages-v1") |')
    text=text.replace(flag,'''            if pending["schema"] == "shieldd-transfer-balance-variable-v1" {
                qualify_balance_variable(&pending)?;
            }
            if pending["schema"] == "shieldd-transfer-balance-variable-pages-v1" {
                qualify_balance_variable_pages(first,repeated,&pending)?;
            }
'''+flag)
    return (text+'\n'+fragment.decode().replace('\r\n','\n')).replace('\n',newline).encode()
