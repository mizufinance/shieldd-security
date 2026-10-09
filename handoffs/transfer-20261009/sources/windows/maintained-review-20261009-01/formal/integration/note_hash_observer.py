"""Pure hook recipes for a NEW diagnostic stage; active runtime is untouched."""

def _source(data):
    if not isinstance(data,bytes):raise ValueError('fresh source bytes required')
    newline='\r\n' if b'\r\n' in data else '\n'
    text=data.decode('utf-8')
    if '\n' in text.replace('\r\n','') and newline=='\r\n':raise ValueError('mixed source line endings')
    return text.replace('\r\n','\n'),newline


def instrument_note(data):
    text,newline=_source(data)
    anchor="pub fn constrain_spend<'ctx>("
    if text.count(anchor)!=1 or 'note_inspection::spend()' in text:
        raise ValueError('note hash scope anchor drift/duplicate')
    start=text.index(anchor);body=text.index(') -> Spend<\'ctx> {',start)+len(') -> Spend<\'ctx> {')
    text=text[:body]+'''\n    #[cfg(feature = "formal-observer")]
    let _note_hash_scope = crate::hash::note_inspection::spend();'''+text[body:]
    return text.replace('\n',newline).encode()


def instrument_hash(data):
    """Requires the existing observed generic hash path, adds a second read-only sink."""
    text,newline=_source(data)
    anchors={
        '            let call = inspection::start(domain, inputs);':
        '            let call = inspection::start(domain, inputs);\n            let note_call = note_inspection::start(domain, inputs);',
        '                inspection::state(&call, block, after, state);':
        '                inspection::state(&call, block, after, state);\n                note_inspection::state(&note_call, block, after, state);',
        '            inspection::finish(call, &output);':
        '            inspection::finish(call, &output);\n            note_inspection::finish(note_call, &output);'}
    if 'pub mod note_inspection;' in text:raise ValueError('note hash observer already activated')
    for old,new in anchors.items():
        if text.count(old)!=1:raise ValueError('existing hash observation anchor drift')
        text=text.replace(old,new)
    text='#[cfg(feature = "formal-observer")]\npub mod note_inspection;\n'+text
    return text.replace('\n',newline).encode()


def instrument_catalogue(data):
    if not isinstance(data,bytes) or b'note_hash_catalogue.rs' in data:
        raise ValueError('fresh catalogue source bytes required')
    return data+b'\n#[cfg(feature = "formal-observer")]\ninclude!("note_hash_catalogue.rs");\n'


def instrument_exporter(data,fragment):
    text,newline=_source(data)
    if not isinstance(fragment,bytes) or 'fn capture_note_hash(' in text:
        raise ValueError('fresh note hash exporter source required')
    main='    let args: Vec<_> = std::env::args().skip(1).collect();'
    schema='        Some("shieldd-transfer-note-spend-v1") => {'
    if text.count(main)!=1 or text.count(schema)!=1:
        raise ValueError('existing note spool dispatch/qualifier anchor drift')
    text=text.replace(main,main+'''\n    if args.len() == 6 && args[0] == "note-hash-spool" {
        return capture_note_hash(&args[1],args[2].parse()?,&args[3],args[4].parse()?,args[5].parse()?);
    }''')
    text=text.replace(schema,'''        Some("shieldd-transfer-note-spend-v1") |
        Some("shieldd-transfer-note-hash-block-v1") => {''')
    return (text+'\n'+fragment.decode().replace('\r\n','\n')).replace('\n',newline).encode()


def instrument_pages_catalogue(data):
    if not isinstance(data,bytes) or b'note_hash_catalogue.rs' not in data or b'note_hash_pages_catalogue.rs' in data:
        raise ValueError('fresh single-note-hash catalogue source required')
    return data+b'\n#[cfg(feature = "formal-observer")]\ninclude!("note_hash_pages_catalogue.rs");\n'


def instrument_pages_exporter(data,fragment):
    text,newline=_source(data)
    if not isinstance(fragment,bytes) or 'fn capture_note_hash_pages(' in text:
        raise ValueError('fresh single-note-hash exporter source required')
    main='    let args: Vec<_> = std::env::args().skip(1).collect();'
    schema='        Some("shieldd-transfer-note-hash-block-v1") => {'
    if text.count(main)!=1 or text.count(schema)!=1 or 'fn capture_note_hash(' not in text:
        raise ValueError('single hash spool dispatch/qualifier anchor drift')
    text=text.replace(main,main+'''\n    if args.len() == 2 && args[0] == "note-hash-pages-spool" {
        return capture_note_hash_pages(&args[1]);
    }''')
    text=text.replace(schema,'''        Some("shieldd-transfer-note-hash-block-v1") |
        Some("shieldd-transfer-note-hash-pages-v1") => {
            if pending["schema"] == "shieldd-transfer-note-hash-pages-v1" {
                qualify_note_hash_pages(first,repeated,&pending)?;
            }''')
    return (text+'\n'+fragment.decode().replace('\r\n','\n')).replace('\n',newline).encode()
