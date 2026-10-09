"""Pure append recipe over the retained merged runtime; no stage mutation.

The existing assert_non_identity call and both existing observers stay intact.
The new scope selects only its actual inverse, rather than a recreated witness.
"""
from .asset_map_observer import _source
from .recovery_hash_observer import replace_once


def instrument_balance(data):
    text, newline = _source(data)
    if 'asset_nonidentity_inspection' in text:
        raise ValueError('asset nonidentity balance already instrumented')
    if 'pub mod inspection {' not in text or 'inspection::record("signed",' not in text:
        raise ValueError('retained balance source observers required')
    anchor = '    drop(asset_scope);\n    generator.assert_non_identity();'
    text = replace_once(text, anchor, '''    drop(asset_scope);
    #[cfg(feature = "formal-observer")]
    let nonidentity_scope = asset_nonidentity_inspection::scope(asset, &hash, &generator);
    generator.assert_non_identity();
    #[cfg(feature = "formal-observer")]
    drop(nonidentity_scope);''')
    return ('#[cfg(feature = "formal-observer")]\npub mod asset_nonidentity_inspection;\n' + text).replace('\n', newline).encode()


def instrument_group(data):
    text, newline = _source(data)
    if 'asset_nonidentity_inspection::record' in text:
        raise ValueError('asset nonidentity group already instrumented')
    anchor = '''    pub fn assert_non_identity(&self) {
        // A prime-subgroup point has x=0 only at identity (the other x=0 point has order 2).
        let _inverse = self.x.inv();
        #[cfg(feature = "formal-observer")]
        inspection::record_nonidentity(&self.x, &_inverse);
        #[cfg(feature = "formal-observer")]
        ownership_inspection::nonidentity(&self.x, &_inverse);
    }'''
    replacement = anchor[:-6] + '''
        #[cfg(feature = "formal-observer")]
        crate::balance::asset_nonidentity_inspection::record(&self.x, &_inverse);
    }'''
    return replace_once(text, anchor, replacement).replace('\n', newline).encode()


def catalogue(resource):
    text, _ = _source(resource)
    for old, new in [('AssetMapInspection', 'AssetNonidentityInspection'),
                     ('inspect_transfer_asset_map', 'inspect_transfer_asset_nonidentity')]:
        text = text.replace(old, new)
    text = replace_once(text, '    pub report: crate::map::asset_inspection::Report,',
        '    pub report: crate::map::asset_inspection::Report,\n    pub nonidentity: crate::balance::asset_nonidentity_inspection::Report,')
    text = replace_once(text, '    let _capture = crate::map::asset_inspection::begin()?;',
        '    let _capture = crate::map::asset_inspection::begin()?;\n    let _nonidentity = crate::balance::asset_nonidentity_inspection::begin()?;')
    text = replace_once(text, '    let report = crate::map::asset_inspection::take()?;',
        '''    let report = crate::map::asset_inspection::take()?;
    let nonidentity = crate::balance::asset_nonidentity_inspection::take()?;
    anyhow::ensure!(nonidentity.asset == report.asset && nonidentity.hash == report.hash &&
        nonidentity.generator == report.cofactor[3], "actual asset nonidentity/map roots changed");''')
    text = replace_once(text, '    let mut selected: BTreeSet<_> = report.selected().into_iter().collect();',
        '    let mut selected: BTreeSet<_> = report.selected().into_iter().chain(nonidentity.selected()).collect();')
    text = replace_once(text, '        report, selected, expressions, constant_copy, nodes })',
        '        report, nonidentity, selected, expressions, constant_copy, nodes })')
    return text.encode()


def exporter(resource):
    text, _ = _source(resource)
    for old, new in [('capture_asset_map', 'capture_asset_nonidentity'),
                     ('AssetMapInspection', 'AssetNonidentityInspection'),
                     ('inspect_transfer_asset_map', 'inspect_transfer_asset_nonidentity'),
                     ('shieldd-transfer-asset-map-v1', 'shieldd-transfer-asset-nonidentity-v1')]:
        text = text.replace(old, new)
    text = replace_once(text, 'compiled, report, selected,', 'compiled, report, nonidentity, selected,')
    text = replace_once(text, '"values":report.values.iter()',
        '''"nonidentity":{"asset":observed(&nonidentity.asset),"hash":observed(&nonidentity.hash),
            "generator":pair(&nonidentity.generator),"inverse":observed(&nonidentity.inverse)},
        "values":report.values.iter()''')
    return text.encode()


def instrument_catalogue(data):
    if not isinstance(data, bytes) or b'asset_nonidentity_catalogue.rs' in data:
        raise ValueError('fresh asset nonidentity catalogue required')
    return data + b'\n#[cfg(feature = "formal-observer")]\ninclude!("asset_nonidentity_catalogue.rs");\n'


def instrument_exporter(data, fragment, qualifier):
    text, newline = _source(data)
    if 'capture_asset_nonidentity' in text:
        raise ValueError('fresh asset nonidentity exporter required')
    text = replace_once(text, '    let args: Vec<_> = std::env::args().skip(1).collect();',
        '''    let args: Vec<_> = std::env::args().skip(1).collect();
    if args.len()==2 && args[0]=="asset-nonidentity-spool" {return capture_asset_nonidentity(&args[1]);}''')
    text = replace_once(text, '        Some("shieldd-transfer-asset-map-v1") |',
        '        Some("shieldd-transfer-asset-nonidentity-v1") |\n        Some("shieldd-transfer-asset-map-v1") |')
    text = replace_once(text, '            if pending["schema"] == "shieldd-transfer-t4-pages-v1" {',
        '''            if pending["schema"] == "shieldd-transfer-asset-nonidentity-v1" {
                qualify_asset_nonidentity(&pending)?;
            }
            if pending["schema"] == "shieldd-transfer-t4-pages-v1" {''')
    return (text + '\n' + fragment.decode() + '\n' + qualifier.decode()).replace('\n', newline).encode()
