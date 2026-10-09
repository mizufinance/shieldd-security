"""Exact output hook recipe for a NEW diagnostic source stage only.

The runtime output operations are retained in their original order. Root must
copy observers/note_output.rs into note/output_inspection.rs, activate the note
module in a fresh stage, and later connect a bounded LC page/row qualifier.
No active runtime, exporter or previously frozen stage is modified here.
"""


def instrument_note(data):
    if not isinstance(data,bytes):raise ValueError('output observer source bytes required')
    newline='\r\n' if b'\r\n' in data else '\n';text=data.decode()
    if newline=='\r\n' and '\n' in text.replace('\r\n',''):
        raise ValueError('output observer mixed source line endings')
    text=text.replace('\r\n','\n')
    if 'pub mod output_inspection;' in text:raise ValueError('output observer already activated')
    start='pub fn constrain_output<';end='\n#[cfg(test)]\nmod tests;'
    if text.count(start)!=1 or text.count(end)!=1:raise ValueError('output observer exact source boundary drift')
    before,body=text.split(start);body,after=body.split(end)
    def replace(old,new):
        nonlocal body
        if body.count(old)!=1:raise ValueError('output observer operation anchor drift/duplicate')
        body=body.replace(old,new)
    replace('''    decompose(ctx, &note.amount, 128);
    if receiver {
        let _ = note.amount.inv();
    }''','''    let amount_bits = decompose(ctx, &note.amount, 128);
    let receiver_inverse = if receiver {
        Some(note.amount.inv())
    } else {
        None
    };''')
    replace('''    params
        .circuit(NOTE, &note.fields(asset, address))
        .assert_eq(&commitment);''','''    let computed_commitment = params.circuit(NOTE, &note.fields(asset, address));
    computed_commitment.assert_eq(&commitment);''')
    replace('''    capsule.commitment.assert_eq(&note.recovery);
    Output {''','''    capsule.commitment.assert_eq(&note.recovery);
    #[cfg(feature = "formal-observer")]
    output_inspection::record(receiver, &note, asset, address, payload_key,
        &amount_bits, receiver_inverse.as_ref(), &computed_commitment, &commitment, &capsule);
    Output {''')
    result='#[cfg(feature = "formal-observer")]\npub mod output_inspection;\n'+before+start+body+end+after
    return result.replace('\n',newline).encode()


def instrument_catalogue(data):
    if not isinstance(data,bytes) or b'note_output_catalogue.rs' in data:
        raise ValueError('fresh output catalogue source required')
    return data+b'\n#[cfg(feature = "formal-observer")]\ninclude!("note_output_catalogue.rs");\n'


def instrument_exporter(data,fragment):
    """Keep the maintained spill/ordinary2/repeat qualifier in a fresh copy."""
    if not isinstance(data,bytes) or not isinstance(fragment,bytes) or b'fn capture_note_outputs(' in data:
        raise ValueError('fresh output exporter source/fragment required')
    newline='\r\n' if b'\r\n' in data else '\n';text=data.decode().replace('\r\n','\n')
    main='    let args: Vec<_> = std::env::args().skip(1).collect();'
    schema='        Some("shieldd-transfer-note-spend-v1") |'
    if text.count(main)!=1 or text.count(schema)!=1:raise ValueError('output exporter dispatch/qualifier anchor drift')
    text=text.replace(main,main+'\n    if args.len() == 2 && args[0] == "note-output-spool" {\n        return capture_note_outputs(&args[1]);\n    }')
    text=text.replace(schema,schema+'\n        Some("shieldd-transfer-note-output-v1") |')
    return (text+'\n'+fragment.decode().replace('\r\n','\n')).replace('\n',newline).encode()


def instrument_output_hash_note(data):
    """Scope the two existing output hashes; no arithmetic operation changes."""
    if not isinstance(data,bytes):raise ValueError('output hash source bytes required')
    newline='\r\n' if b'\r\n' in data else '\n';text=data.decode().replace('\r\n','\n')
    if 'pub mod output_inspection;' not in text or 'pub mod output_hash_inspection;' in text:
        raise ValueError('fresh activated output source required')
    anchor="pub fn constrain_output<'ctx>(";end=") -> Output<'ctx> {"
    if text.count(anchor)!=1 or text.count(end)!=1:raise ValueError('output hash exact scope anchor drift')
    position=text.index(end,text.index(anchor))+len(end)
    text=text[:position]+'''\n    #[cfg(feature = "formal-observer")]
    let _output_hash_scope = output_hash_inspection::output();'''+text[position:]
    return ('#[cfg(feature = "formal-observer")]\npub mod output_hash_inspection;\n'+text).replace('\n',newline).encode()


def instrument_output_hash_hash(data):
    """Append an independent read-only sink after existing note hash hooks."""
    if not isinstance(data,bytes):raise ValueError('output hash source bytes required')
    newline='\r\n' if b'\r\n' in data else '\n';text=data.decode().replace('\r\n','\n')
    if 'output_hash_inspection::' in text:raise ValueError('output hash sink already activated')
    anchors={
        '            let note_call = note_inspection::start(domain, inputs);':
        '            let note_call = note_inspection::start(domain, inputs);\n            let output_call = crate::note::output_hash_inspection::start(domain, inputs);',
        '                note_inspection::state(&note_call, block, after, state);':
        '                note_inspection::state(&note_call, block, after, state);\n                crate::note::output_hash_inspection::state(&output_call, block, after, state);',
        '            note_inspection::finish(note_call, &output);':
        '            note_inspection::finish(note_call, &output);\n            crate::note::output_hash_inspection::finish(output_call, &output);'}
    for old,new in anchors.items():
        if text.count(old)!=1:raise ValueError('output hash existing sink source anchor drift')
        text=text.replace(old,new)
    return text.replace('\n',newline).encode()
