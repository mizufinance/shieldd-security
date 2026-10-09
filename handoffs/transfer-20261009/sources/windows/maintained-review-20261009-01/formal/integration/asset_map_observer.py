"""Strict pure hooks for a fresh asset-map observer stage.

Never mutates a runtime checkout. Existing circuit operations are retained in
their original order; complete ordinary-row parity and repeat capture are still
required before accepting the retained source handles.
"""


def _source(data):
    if not isinstance(data, bytes):
        raise ValueError('asset-map source bytes required')
    newline = '\r\n' if b'\r\n' in data else '\n'
    text = data.decode('utf8')
    if newline == '\r\n' and '\n' in text.replace('\r\n', ''):
        raise ValueError('asset-map mixed line endings')
    return text.replace('\r\n', '\n'), newline


def instrument_map(data):
    text, newline = _source(data)
    if 'asset_inspection' in text:
        raise ValueError('asset-map already instrumented')
    start = text.index("pub fn circuit<'ctx>(")
    end = text.index('\npub fn asset(', start)
    body = text[start:end]

    def replace(old, new):
        nonlocal body
        if body.count(old) != 1:
            raise ValueError('asset-map arithmetic hook changed/duplicate')
        body = body.replace(old, new)

    replace('''    let (x1, gx1, x2, gx2) = x_coordinates(
        u,
        &Var::native(c1),
        &Var::native(c2),
        &Var::native(Scalar::from(5)),
    );''', '''    let c1 = Var::native(c1);
    let c2 = Var::native(c2);
    let z = Var::native(Scalar::from(5));
    let tv = z.clone() * u * u;
    let first_denominator = Var::one() + &tv;
    let first_inverse = first_denominator.inv();
    let x1 = -c1.clone() * &first_inverse;
    let gx1 = ((x1.clone() + &c1) * &x1 + &c2) * &x1;
    let x2 = -x1.clone() - &c1;
    let gx2 = tv.clone() * &gx1;''')
    replace('    encoding::canonical_bits(ctx, &y)[0].assert_eq(&square);',
            '    let y_bits = encoding::canonical_bits(ctx, &y);\n    y_bits[0].assert_eq(&square);')
    replace('    (y.clone() * &y).assert_eq(&y_squared);',
            '    let y_square = y.clone() * &y;\n    y_square.assert_eq(&y_squared);')
    replace('    let s = x * &k;', '    let s = x.clone() * &k;')
    replace('    let t = y * &k;', '    let t = y.clone() * &k;')
    replace('    (denominator.clone() * &inverse).assert_eq(&(Var::one() - zero.var()));',
            '    let inverse_product = denominator.clone() * &inverse;\n    inverse_product.assert_eq(&(Var::one() - zero.var()));')
    replace('    (denominator * zero.var()).assert_eq(&Var::zero());',
            '    let denominator_zero = denominator.clone() * zero.var();\n    denominator_zero.assert_eq(&Var::zero());')
    replace('    (inverse.clone() * zero.var()).assert_eq(&Var::zero());',
            '    let inverse_zero = inverse.clone() * zero.var();\n    inverse_zero.assert_eq(&Var::zero());')
    replace('''        y: inverse * &t * &(s - &Var::one()) + zero.var(),
    };
    for _ in 0..3 {
        point = point.add(&point, &Var::native(coefficient_d()));
    }
    point''', '''        y: inverse.clone() * &t * &(s.clone() - &Var::one()) + zero.var(),
    };
    #[cfg(feature = "formal-observer")]
    let mut cofactor = vec![point.clone()];
    #[cfg(feature = "formal-observer")]
    let mut cofactor_aux = Vec::new();
    for _ in 0..3 {
        let xx = point.x.clone() * &point.x;
        let yy = point.y.clone() * &point.y;
        let dt = xx.clone() * &yy * &Var::native(coefficient_d());
        let plus = Var::one() + &dt;
        let minus = Var::one() - &dt;
        let divisor = plus.clone() * &minus;
        let double_inverse = divisor.inv();
        point = Point {
            x: (point.x.clone() * &point.y + &(point.y.clone() * &point.x)) * &minus * &double_inverse,
            y: (yy.clone() + &xx) * &plus * &double_inverse,
        };
        #[cfg(feature = "formal-observer")]
        cofactor_aux.push([xx, yy, dt, plus, minus, divisor, double_inverse]);
        #[cfg(feature = "formal-observer")]
        cofactor.push(point.clone());
    }
    #[cfg(feature = "formal-observer")]
    asset_inspection::record(
        [u, &tv, &first_denominator, &first_inverse, &x1, &gx1, &x2, &gx2,
         square.var(), &qr_root, &x, &y_squared, &y, &s, &t, &plus,
         &denominator, zero.var(), &inverse], &y_bits, &cofactor,
         [&y_square, &inverse_product, &denominator_zero, &inverse_zero], &cofactor_aux);
    point''')
    prefix = text[:start]
    qr = '    (root.clone() * root).assert_eq(&square.select(gx1, &(z * gx1)));'
    if prefix.count(qr) != 1:
        raise ValueError('asset QR constraint hook changed')
    prefix = prefix.replace(qr, '''    let squared = root.clone() * root;
    let selected = square.select(gx1, &(z * gx1));
    squared.assert_eq(&selected);
    #[cfg(feature = "formal-observer")]
    asset_inspection::qr(&squared, &selected);''')
    return ('#[cfg(feature = "formal-observer")]\npub mod asset_inspection;\n' +
            prefix + body + text[end:]).replace('\n', newline).encode('utf8')


def instrument_encoding(data):
    text, newline = _source(data)
    if 'asset_inspection::canonical' in text:
        raise ValueError('asset canonical observer already active')
    anchor = '    less_or_equal(bits, &maximum).assert_eq(&BoolVar::constant(true));'
    if text.count(anchor) != 1:
        raise ValueError('asset canonical bound hook changed')
    replacement = '''    let bounded = less_or_equal(bits, &maximum);
    bounded.assert_eq(&BoolVar::constant(true));
    #[cfg(feature = "formal-observer")]
    crate::map::asset_inspection::canonical(value, bits, &sum, &bounded);'''
    return text.replace(anchor, replacement).replace('\n', newline).encode('utf8')


def instrument_balance(data):
    text, newline = _source(data)
    if 'asset_inspection' in text:
        raise ValueError('asset balance already instrumented')
    anchor = '''    let hash = params.circuit(map::ASSET_GENERATOR, &[asset.clone()]);
    let generator = map::circuit(ctx, &hash);'''
    if text.count(anchor) != 1:
        raise ValueError('asset balance source/hash hook changed')
    replacement = '''    let hash = params.circuit(map::ASSET_GENERATOR, &[asset.clone()]);
    #[cfg(feature = "formal-observer")]
    let asset_scope = map::asset_inspection::scope(asset, &hash);
    let generator = map::circuit(ctx, &hash);
    #[cfg(feature = "formal-observer")]
    drop(asset_scope);'''
    return text.replace(anchor, replacement).replace('\n', newline).encode('utf8')


def instrument_catalogue(data):
    if not isinstance(data, bytes) or b'asset_map_catalogue.rs' in data:
        raise ValueError('fresh asset catalogue required')
    return data + b'\n#[cfg(feature = "formal-observer")]\ninclude!("asset_map_catalogue.rs");\n'


def instrument_exporter(data, fragment):
    text, newline = _source(data)
    if not isinstance(fragment, bytes) or 'fn capture_asset_map(' in text:
        raise ValueError('fresh asset exporter/fragment required')
    main = '    let args: Vec<_> = std::env::args().skip(1).collect();'
    schema = 'Some("shieldd-transfer-fixed-spend-v1")'
    if text.count(main) != 1 or text.count(schema) != 1:
        raise ValueError('asset spool dispatch/qualifier drift')
    text = text.replace(main, main + '''\n    if args.len() == 2 && args[0] == "asset-map-spool" {
        return capture_asset_map(&args[1]);
    }''')
    text = text.replace(schema, 'Some("shieldd-transfer-asset-map-v1") |\n        ' + schema)
    return (text + '\n' + fragment.decode('utf8').replace('\r\n', '\n')).replace('\n', newline).encode('utf8')
