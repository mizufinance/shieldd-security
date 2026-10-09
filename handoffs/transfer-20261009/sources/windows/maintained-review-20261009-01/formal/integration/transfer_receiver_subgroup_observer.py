"""Pure fresh-stage overlay for three receiver subgroup operations.

It reuses the existing bounded group recorder and spool qualifier. This writes
no SDK/stage file, changes no circuit expression/witness closure, and confers
no runtime/qualification/proof credit before a root-owned fresh build/capture.
"""
from pathlib import Path

ROOT=Path(__file__).resolve().parent
SCHEMA='shieldd-transfer-receiver-subgroups-v1'
SCOPE='three receiver cofactor/on-curve/nonidentity source observations; row and native joins open'

def once(source,old,new):
    if source.count(old)!=1:raise ValueError('receiver subgroup exact source hook absent/duplicated')
    return source.replace(old,new)

def compose(compliance,catalogue,exporter,group_recorder,rk_catalogue,rk_exporter):
    if any('receiver_subgroup' in source for source in (compliance,catalogue,exporter)):
        raise ValueError('receiver subgroup observer already composed')
    for text in ('pub fn begin()', 'pub(crate) fn scope()', 'pub fn take()', 'pub struct Report',
                 'building.doubles.len() == 3', 'end - start <= 128'):
        if text not in group_recorder:raise ValueError('exact existing bounded subgroup recorder required')
    prefix='#[cfg(feature = "formal-observer")]\n#[path = "compliance/receiver_subgroup_inspection.rs"]\npub mod receiver_subgroup_inspection;\n'
    compliance=prefix+once(compliance,'    let point = |p: &Point<Scalar>| {',
        '    #[cfg(feature = "formal-observer")]\n    let _receiver_call = receiver_subgroup_inspection::enter();\n    let point = |p: &Point<Scalar>| {\n        #[cfg(feature = "formal-observer")]\n        let _receiver_point = receiver_subgroup_inspection::point_scope();')
    catalogue += '\n#[cfg(feature = "formal-observer")]\ninclude!("catalogue/receiver_subgroup_inspection.rs");\n'
    selected_start='    let mut selected: BTreeSet<_> = report.inputs.into_iter().chain(report.curve)'
    selected_end='    let mut pending: Vec<_> = selected.iter().copied().collect();'
    begin=rk_catalogue.find(selected_start);end=rk_catalogue.find(selected_end)
    if begin<0 or end<begin:raise ValueError('existing RK catalogue source selection changed')
    selected='''    let mut selected: BTreeSet<_> = BTreeSet::new();
    for report in &reports {
        selected.extend(report.inputs.into_iter().chain(report.curve).chain(report.nonidentity)
            .chain(report.doubles.iter().flatten().copied()));
        for [start, end] in &report.spans {
            for node in *start..*end { selected.insert(CircuitIdx::Node(u32::try_from(node)?)); }
        }
        let CircuitIdx::Node(node) = report.nonidentity_product else {
            anyhow::bail!("receiver nonidentity product must be a source node");
        };
        anyhow::ensure!(c.inspect_node(node) == Some((true, report.nonidentity[1], report.nonidentity[0])),
            "receiver nonidentity product source boundary changed");
        selected.insert(report.nonidentity_product);
    }
'''
    receiver_catalogue=rk_catalogue[:begin]+selected+rk_catalogue[end:]
    receiver_catalogue=receiver_catalogue.replace('RkSubgroupInspection','ReceiverSubgroupInspection').replace('inspect_transfer_rk_subgroup','inspect_transfer_receiver_subgroups')
    receiver_catalogue=once(receiver_catalogue,'pub report: crate::group::inspection::Report,','pub reports: Vec<crate::group::inspection::Report>,')
    receiver_catalogue=once(receiver_catalogue,'crate::group::rk_inspection::begin()?','crate::compliance::receiver_subgroup_inspection::begin()?')
    receiver_catalogue=once(receiver_catalogue,'let report = crate::group::rk_inspection::take()?;','let reports = crate::compliance::receiver_subgroup_inspection::take()?;')
    receiver_catalogue=once(receiver_catalogue,'        report, selected, expressions, constant_copy, nodes })','        reports, selected, expressions, constant_copy, nodes })')
    receiver_catalogue=receiver_catalogue.replace('RK subgroup','receiver subgroup').replace('RK bounded','receiver bounded')
    old_start='        "inputs":report.inputs.iter().map(index).collect::<Vec<_>>(),'
    old_end='        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({'
    start=rk_exporter.find(old_start);end=rk_exporter.find(old_end)
    if start<0 or end<start:raise ValueError('existing RK exporter role mapping changed')
    reports='''        "points":reports.iter().enumerate().map(|(ordinal,report)|json!({
            "ordinal":ordinal,"inputs":report.inputs.iter().map(index).collect::<Vec<_>>(),
            "curve":report.curve.iter().map(index).collect::<Vec<_>>(),
            "doubles":report.doubles.iter().map(|p|p.iter().map(index).collect::<Vec<_>>()).collect::<Vec<_>>(),
            "spans":report.spans,"nonidentity":report.nonidentity.iter().map(index).collect::<Vec<_>>(),
            "nonidentity_product":index(&report.nonidentity_product)
        })).collect::<Vec<_>>(),
'''
    receiver_export=rk_exporter[:start]+reports+rk_exporter[end:]
    receiver_export=receiver_export.replace('capture_rk_subgroup','capture_receiver_subgroups').replace('RkSubgroupInspection { compiled, report,','ReceiverSubgroupInspection { compiled, reports,').replace('inspect_transfer_rk_subgroup','inspect_transfer_receiver_subgroups').replace('shieldd-transfer-rk-subgroup-v1',SCHEMA)
    receiver_export=once(receiver_export,'bounded RK cofactor/on-curve/nonidentity source observation; row and native joins open',SCOPE)
    receiver_export=receiver_export.replace('RK original constant-copy shape','receiver original constant-copy shape')
    exporter=once(exporter,'        Some("shieldd-transfer-rk-subgroup-v1") |',
        '        Some("shieldd-transfer-rk-subgroup-v1") |\n        Some("'+SCHEMA+'") |')
    hook='    if args.len() == 2 && args[0] == "rk-subgroup-spool" { return capture_rk_subgroup(&args[1]); }'
    exporter=once(exporter,hook,hook+'\n    if args.len() == 2 && args[0] == "receiver-subgroups-spool" { return capture_receiver_subgroups(&args[1]); }')
    exporter+='\ninclude!("../src/receiver_subgroup_export.rs");\n'
    return {'crates/crypto/circuits/src/compliance.rs':compliance,
        'crates/crypto/circuits/src/catalogue.rs':catalogue,
        'crates/crypto/circuits/examples/transfer-ownership-inspection.rs':exporter,
        'crates/crypto/circuits/src/compliance/receiver_subgroup_inspection.rs':(ROOT/'observers/receiver_subgroup_scope.rs').read_text(),
        'crates/crypto/circuits/src/catalogue/receiver_subgroup_inspection.rs':receiver_catalogue,
        'crates/crypto/circuits/src/receiver_subgroup_export.rs':receiver_export}
