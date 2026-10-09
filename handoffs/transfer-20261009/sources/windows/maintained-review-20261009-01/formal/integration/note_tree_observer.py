"""Pure future tree hook: retain exact six products and source operation order."""
from .note_hash_observer import _source


def instrument_tree(data):
    text,newline=_source(data)
    anchor='        node = params.circuit(kind as u8, &inputs);'
    if text.count(anchor)!=1 or 'pub mod note_inspection;' in text:
        raise ValueError('fresh owned tree hook anchor drift/duplicate')
    replacement='''        let next = params.circuit(kind as u8, &inputs);
        #[cfg(feature = "formal-observer")]
        note_inspection::record(kind,level,&node,low.var(),high.var(),siblings,
            [&left_swap,&right_swap],&inputs,&next);
        node = next;'''
    text=text.replace(anchor,replacement)
    text='#[cfg(feature = "formal-observer")]\npub mod note_inspection;\n'+text
    return text.replace('\n',newline).encode()


def instrument_catalogue(data):
    if (not isinstance(data,bytes) or data.count(b'include!("note_hash_pages_catalogue.rs");')!=1 or
        b'note_t4_pages_catalogue.rs' in data or b'note_tree_catalogue.rs' in data):
        raise ValueError('fresh paged catalogue source required')
    # Previous include recipes append LF to an owned CRLF prefix. Retain that
    # whole prefix byte-for-byte; append-only activation needs no normalization.
    return data+b'''
#[cfg(feature = "formal-observer")]
include!("note_tree_catalogue.rs");
#[cfg(feature = "formal-observer")]
include!("note_t4_pages_catalogue.rs");
'''


def instrument_exporter(data,fragment):
    text,newline=_source(data)
    main='    let args: Vec<_> = std::env::args().skip(1).collect();'
    schema='        Some("shieldd-transfer-note-hash-pages-v1") => {'
    qualifier='                qualify_note_hash_pages(first,repeated,&pending)?;\n            }'
    if (not isinstance(fragment,bytes) or 'fn capture_note_t4_pages(' in text or
        text.count(main)!=1 or text.count(schema)!=1 or text.count(qualifier)!=1):
        raise ValueError('fresh paged exporter dispatch/qualifier anchor drift/duplicate')
    text=text.replace(main,main+'''
    if args.len() == 2 && args[0] == "note-t4-pages-spool" {
        return capture_note_t4_pages(&args[1]);
    }''')
    text=text.replace(schema,'''        Some("shieldd-transfer-note-hash-pages-v1") |
        Some("shieldd-transfer-note-t4-pages-v1") => {''')
    text=text.replace(qualifier,qualifier+'''
            if pending["schema"] == "shieldd-transfer-note-t4-pages-v1" {
                qualify_note_t4_pages(first,repeated,&pending)?;
            }''')
    return (text+'\n'+fragment.decode().replace('\r\n','\n')).replace('\n',newline).encode()
