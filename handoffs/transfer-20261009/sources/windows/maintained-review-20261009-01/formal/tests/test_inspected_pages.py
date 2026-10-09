"""Source recipe qualification only; Rust semantic tests are staged, not run."""
import unittest
from pathlib import Path
from integration.inspected_pages import instrument_compiler, replace_owned_pages


class InspectedPageRecipeTests(unittest.TestCase):
    def setUp(self):
        self.resource=Path('integration/observers/compile_inspected_pages.rs').read_bytes()
        self.tests=Path('integration/observers/compile_inspected_pages_tests.rs').read_bytes()
        self.source=b'''impl Relation {
    pub fn compile_inspected() { ordinary_inspected_body(); }
    /// Compile a generic arithmetic circuit into a canonical square relation.
    pub fn compile() { ordinary_body(); }
}
'''

    def test_original_ordinary_and_single_page_paths_remain_exact_bytes(self):
        result=instrument_compiler(self.source,self.resource,self.tests)
        indented=b'\n'.join(b'    '+line if line else line for line in self.resource.split(b'\n'))
        self.assertEqual(result.replace(indented+b'\n',b'').removesuffix(b'\n'+self.tests),self.source)
        self.assertEqual(result.count(b'ordinary_inspected_body()'),1)
        self.assertEqual(result.count(b'ordinary_body()'),1)

    def test_fresh_activation_and_anchor_drift_fail_closed(self):
        activated=instrument_compiler(self.source,self.resource,self.tests)
        for bad in (activated,self.source.replace(b'pub fn compile_inspected(',b'pub fn moved('),
                    self.source+self.source,self.source.replace(b'generic arithmetic circuit',b'changed circuit')):
            with self.assertRaises(ValueError):instrument_compiler(bad,self.resource,self.tests)

    def test_exact_owned_adapter_replacement_preserves_other_source_and_refuses_drift(self):
        prior_resource = self.resource.replace(b'1..=74', b'1..=56').replace(b'1..74', b'1..56')
        prior_tests = b'// exact retained prior lifecycle tests\n'
        prior = instrument_compiler(self.source, prior_resource, prior_tests)
        upgraded = replace_owned_pages(prior, prior_resource, prior_tests, self.resource, self.tests)
        self.assertEqual(upgraded, instrument_compiler(self.source, self.resource, self.tests))
        for bad in (prior.replace(b'1..=56', b'1..=55'), prior + b'// drift\n'):
            with self.assertRaises(ValueError):
                replace_owned_pages(bad, prior_resource, prior_tests, self.resource, self.tests)

    def test_line_endings_and_staged_lifecycle_controls(self):
        result=instrument_compiler(self.source.replace(b'\n',b'\r\n'),self.resource,self.tests)
        self.assertNotIn(b'\n',result.replace(b'\r\n',b''))
        text=self.resource.decode()
        operations=['Compiler::new','compiler.compile_nodes()','compiler.compile_assertions()',
            'compiler.link_inputs()','for (ordinal, selected)','consume(ordinal','count != expected_pages',
            'compiler.outline_constant()','compiler.finish()']
        self.assertEqual([text.index(step) for step in operations],sorted(text.index(step) for step in operations))
        self.assertIn(b'pages_match_single_inspection_and_full_ordinary_rows',self.tests)
        self.assertIn(b'sink_failure_stops_before_the_next_page',self.tests)
        self.assertIn(b'truncated_overflow_empty_duplicate_and_oversize_pages_are_refused',self.tests)


if __name__=='__main__':unittest.main()
