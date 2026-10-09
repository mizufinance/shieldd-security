import unittest
from integration import transfer_receiver_subgroup_observer as observer

class ReceiverSubgroupObserverTests(unittest.TestCase):
    def fixture(self):
        compliance='fn constrain() {\n    let point = |p: &Point<Scalar>| {\n        let result = witness_subgroup(p);\n        result.assert_non_identity();\n        result\n    };\n}\n'
        catalogue='// existing catalogue\n'
        exporter='''fn main() {
    if args.len() == 2 && args[0] == "rk-subgroup-spool" { return capture_rk_subgroup(&args[1]); }
    match schema {
        Some("shieldd-transfer-rk-subgroup-v1") |
        Some("other") => qualify_same_four_spools(),
    }
}
'''
        recorder='pub fn begin() pub(crate) fn scope() pub fn take() pub struct Report building.doubles.len() == 3 end - start <= 128'
        rk_catalogue='''pub struct RkSubgroupInspection {
    pub report: crate::group::inspection::Report,
}
pub fn inspect_transfer_rk_subgroup() {
    let _capture = crate::group::rk_inspection::begin()?;
    let report = crate::group::rk_inspection::take()?;
    let mut selected: BTreeSet<_> = report.inputs.into_iter().chain(report.curve)
        .chain(report.nonidentity).collect();
    let mut pending: Vec<_> = selected.iter().copied().collect();
    compile_same_relation();
    Ok(RkSubgroupInspection { compiled: same_compiled,
        report, selected, expressions, constant_copy, nodes })
}
'''
        rk_export='''fn capture_rk_subgroup() {
    let catalogue::RkSubgroupInspection { compiled, report, selected, expressions, constant_copy, nodes } = catalogue::inspect_transfer_rk_subgroup()?;
    let metadata=json!({"schema":"shieldd-transfer-rk-subgroup-v1",
        "scope":"bounded RK cofactor/on-curve/nonidentity source observation; row and native joins open",
        "inputs":report.inputs.iter().map(index).collect::<Vec<_>>(),
        "curve":report.curve.iter().map(index).collect::<Vec<_>>(),
        "expressions":selected.iter().zip(&expressions).map(|(source,terms)|json!({
        }))});
}
'''
        return compliance,catalogue,exporter,recorder,rk_catalogue,rk_export

    def test_hooks_preserve_source_point_body_and_qualifier(self):
        values=self.fixture();overlay=observer.compose(*values)
        self.assertEqual(len(overlay),6)
        compliance=overlay['crates/crypto/circuits/src/compliance.rs']
        self.assertIn('let result = witness_subgroup(p);\n        result.assert_non_identity();\n        result',compliance)
        exporter=overlay['crates/crypto/circuits/examples/transfer-ownership-inspection.rs']
        self.assertIn('qualify_same_four_spools()',exporter)
        self.assertEqual(exporter.count('receiver-subgroups-spool'),1)
        cat=overlay['crates/crypto/circuits/src/catalogue/receiver_subgroup_inspection.rs']
        self.assertIn('for report in &reports',cat)
        self.assertIn('compile_same_relation()',cat)
        export=overlay['crates/crypto/circuits/src/receiver_subgroup_export.rs']
        self.assertIn('"points":reports.iter().enumerate()',export)
        self.assertIn(observer.SCHEMA,export)

    def test_duplicate_missing_or_changed_source_hooks_refuse(self):
        fixture=list(self.fixture())
        for index,replacement in ((0,'no point closure'),(3,'different unbounded recorder'),(4,'no RK selection'),(5,'no RK role mapping')):
            changed=fixture.copy();changed[index]=replacement
            with self.assertRaises(ValueError):observer.compose(*changed)
        changed=fixture.copy();changed[0]+='// receiver_subgroup already present'
        with self.assertRaises(ValueError):observer.compose(*changed)

if __name__=='__main__':unittest.main()
