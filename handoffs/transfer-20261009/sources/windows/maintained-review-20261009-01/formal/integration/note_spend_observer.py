"""Pure fresh-stage hook recipe; never rewrites active runtime/staged files.

Root must copy observers/note_spend.rs to src/note/spend_inspection.rs and
observers/note_spend_catalogue.rs to src/note_spend_catalogue.rs, then write the
returned source bytes into a NEW disposable stage. Full ordinary-row parity
and repeated capture are mandatory before any metadata is accepted.
"""

def instrument_note(data):
    if not isinstance(data, bytes):
        raise ValueError('note observer source bytes required')
    newline = '\r\n' if b'\r\n' in data else '\n'
    text = data.decode('utf-8')
    if newline == '\r\n' and '\n' in text.replace('\r\n',''):
        raise ValueError('note observer mixed line endings')
    text = text.replace('\r\n','\n')
    start = text.index('pub fn constrain_spend<')
    end = text.index('\n#[derive(Clone)]\npub struct OutputWitness', start)
    body = text[start:end]

    def replace(old, new):
        nonlocal body
        if body.count(old) != 1:
            raise ValueError('note observer hook anchor changed/duplicate')
        body = body.replace(old, new)

    replace('    decompose(ctx, &note.amount, 128);',
            '    let amount_bits = decompose(ctx, &note.amount, 128);')
    replace('Tree::State, commitment, &path, &positions);',
            'Tree::State, commitment.clone(), &path, &positions);')
    replace('''            BoolVar::constant(false)
        }
        Some((optional, padding))''', '''            let dummy = BoolVar::constant(false);
            #[cfg(feature = "formal-observer")]
            spend_inspection::record(shared, &note, &commitment, &path.position,
                &amount_bits, &positions, &real_nullifier, &anchor, &nullifier, &dummy, None);
            dummy
        }
        Some((optional, padding))''')
    replace('''            let synthetic = params.circuit(
                domain,''', '''            let padding_seed = var(&optional.seed);
            let synthetic = params.circuit(
                domain,''')
    replace('                    var(&optional.seed),', '                    padding_seed.clone(),')
    replace('''            dummy
                .select(&synthetic, &real_nullifier)
                .assert_eq(&nullifier);
            let real = !dummy.clone();
            (real.var().clone() * &(anchor - &shared.anchor)).assert_eq(&Var::zero());
            (dummy.var().clone() * &note.amount).assert_eq(&Var::zero());
            dummy''', '''            let selector_delta = synthetic.clone() - &real_nullifier;
            let selector_product = dummy.var().clone() * &selector_delta;
            let selected = real_nullifier.clone() + &selector_product;
            selected.assert_eq(&nullifier);
            let real = !dummy.clone();
            let anchor_delta = anchor.clone() - &shared.anchor;
            let anchor_product = real.var().clone() * &anchor_delta;
            anchor_product.assert_eq(&Var::zero());
            let amount_product = dummy.var().clone() * &note.amount;
            amount_product.assert_eq(&Var::zero());
            #[cfg(feature = "formal-observer")]
            spend_inspection::record(shared, &note, &commitment, &path.position,
                &amount_bits, &positions, &real_nullifier, &anchor, &nullifier, &dummy,
                spend_inspection::optional(domain, slot, &padding_seed, &synthetic, &selected,
                    [[dummy.var(), &selector_delta, &selector_product],
                     [real.var(), &anchor_delta, &anchor_product],
                     [dummy.var(), &note.amount, &amount_product]]));
            dummy''')
    if 'pub mod spend_inspection;' in text:
        raise ValueError('note observer already activated')
    return ('#[cfg(feature = "formal-observer")]\npub mod spend_inspection;\n' +
            text[:start] + body + text[end:]).replace('\n',newline).encode('utf-8')


def instrument_catalogue(data):
    if not isinstance(data, bytes) or b'note_spend_catalogue.rs' in data:
        raise ValueError('fresh catalogue source bytes required')
    return data + b'\n#[cfg(feature = "formal-observer")]\ninclude!("note_spend_catalogue.rs");\n'


def instrument_exporter(data, fragment):
    """Extend the existing spool runner/qualifier in a fresh source stage only."""
    if not isinstance(data,bytes) or not isinstance(fragment,bytes):
        raise ValueError('fresh exporter/fragment source bytes required')
    if b'fn capture_note_spend(' in data:
        raise ValueError('note-spend exporter already activated')
    newline = '\r\n' if b'\r\n' in data else '\n'
    text = data.decode('utf-8').replace('\r\n','\n')
    main = '    let args: Vec<_> = std::env::args().skip(1).collect();'
    schema = '        Some("shieldd-transfer-fixed-spend-v1") => {'
    if text.count(main) != 1 or text.count(schema) != 1:
        raise ValueError('note-spend spool dispatch/qualifier anchor drift')
    text = text.replace(main, main+'''\n    if args.len() == 2 && args[0] == "note-spend-spool" {
        return capture_note_spend(&args[1]);
    }''')
    text = text.replace(schema,'''        Some("shieldd-transfer-fixed-spend-v1") |
        Some("shieldd-transfer-note-spend-v1") => {''')
    return (text+'\n'+fragment.decode('utf-8').replace('\r\n','\n')).replace('\n',newline).encode('utf-8')
