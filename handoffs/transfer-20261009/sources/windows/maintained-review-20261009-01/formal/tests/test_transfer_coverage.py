import copy
import hashlib
import json
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch
import security
import transfer_coverage as coverage


class TransferCoverageTests(unittest.TestCase):
    def setUp(self):
        self.register = security.read_json(security.ROOT / 'assurance.json')

    def check(self):
        return coverage.check(self.register, security.ROOT, security.locked_sha(),
                              security.read_json, security.CheckError)

    def test_runtime_execution_metadata_reviews_do_not_adopt_results(self):
        entries = coverage.MATRIX_RUNTIME_TEST_EXECUTION_METADATA_REVIEWS
        self.assertEqual(len(entries), 55)
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        selected = {r['selector']['member']: r for r in reviews.values()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in {e[0] for e in entries}}
        self.assertEqual(len(selected), 55)
        self.assertTrue(all('referenced test body/result is not established' in r['reason']
                            and r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        self.assertEqual(selected['/runtime_policy_contract/tests/34']['applicability'],
                         'separate_note_reshape_milestone')
        self.assertEqual(selected['/runtime_policy_contract/tests/36']['applicability'],
                         'separate_withdrawal_milestone')
        self.assertEqual(selected['/runtime_policy_contract/tests/37']['obligation'], 'current:state')
        self.assertIn('actual prover', selected['/runtime_policy_contract/tests/37']['reason'])
        self.assertIn('genuine Pari', selected['/runtime_policy_contract/tests/44']['reason'])
        self.assertIn('Old SnarkPack', selected['/runtime_policy_contract/tests/9']['reason'])

    def test_runtime_execution_metadata_identity_and_duplication_fail_closed(self):
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        entries = coverage.MATRIX_RUNTIME_TEST_EXECUTION_METADATA_REVIEWS
        for index in range(len(entries)):
            changed = list(entries)
            value = list(changed[index]); value[3] = '0' * 64; changed[index] = tuple(value)
            with patch.object(coverage, 'MATRIX_RUNTIME_TEST_EXECUTION_METADATA_REVIEWS', tuple(changed)):
                with self.assertRaises(ValueError): coverage.source_occurrence_reviews(universe)
        with patch.object(coverage, 'MATRIX_RUNTIME_TEST_EXECUTION_METADATA_REVIEWS', entries + entries[:1]):
            with self.assertRaises(ValueError): coverage.source_occurrence_reviews(universe)

    def metadata_review_groups(self):
        return (
            ('MATRIX_PROPERTY_EXECUTION_METADATA_CIRCUIT_CRYPTO_REVIEWS', 119, 'circuit-crypto'),
            ('MATRIX_PROPERTY_EXECUTION_METADATA_STATE_INTEGRATION_REVIEWS', 122, 'state-integration'),
            ('MATRIX_PROPERTY_EXECUTION_METADATA_PROTOCOL_REVIEWS', 4, 'protocol'),
            ('MATRIX_ARTIFACT_EXECUTION_METADATA_STATE_INTEGRATION_REVIEWS', 109, 'state-integration'),
            ('MATRIX_ARTIFACT_EXECUTION_METADATA_CIRCUIT_CRYPTO_REVIEWS', 179, 'circuit-crypto'),
            ('MATRIX_COMPLETE_CENSUS_METADATA_REVIEWS', 3, 'circuit-crypto'),
        )

    def test_complete_metadata_reviews_keep_identity_and_recommended_owner_separate(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        selected = {r['selector']['member']: r for r in reviews.values()
                    if r['review'] in {'execution_metadata_reviewed_applicability_only',
                                       'complete_metadata_structure_reviewed_applicability_only'}}
        self.assertEqual(len(selected), 536)
        for name, count, owner in self.metadata_review_groups():
            entries = getattr(coverage, name)
            self.assertEqual(len(entries), count)
            for entry in entries:
                review = selected[entry[0]]
                self.assertEqual(review['selector']['member_sha256'], entry[3])
                self.assertEqual(review['reason'], entry[5])
                self.assertEqual(review['owner'], owner)
                self.assertEqual(review['status'], 'open')
                self.assertEqual(review['evidence'], [])
        state = selected['/property_test_contract/tests/9']
        self.assertEqual(state['selector']['owner'], 'circuit-crypto')
        self.assertEqual(state['owner'], 'state-integration')
        self.assertEqual(selected['/property_test_contract/tests/6']['selector']['owner'], 'state-integration')

    def test_complete_metadata_selectors_refuse_hash_drift_or_duplicate(self):
        # The maintained register supplies exact historical selectors, not a dirty runtime body.
        universe = {key: r['selector'] for key, r in
                    self.register['transfer_assurance']['source_occurrence_reviews'].items()}
        for name, count, owner in self.metadata_review_groups():
            original = getattr(coverage, name)
            changed = list(original[0]); changed[3] = '0' * 64
            with self.subTest(group=name):
                with patch.object(coverage, name, (tuple(changed),) + original[1:]):
                    with self.assertRaisesRegex(ValueError, 'selector changed'):
                        coverage.source_occurrence_reviews(universe)
                with patch.object(coverage, name, original + original[:1]):
                    with self.assertRaisesRegex(ValueError, 'duplicate reviewed'):
                        coverage.source_occurrence_reviews(universe)

    def test_execution_metadata_does_not_adopt_test_results_or_other_families(self):
        names = {e[0] for name, count, owner in self.metadata_review_groups()[:-1]
                 for e in getattr(coverage, name)}
        selected = [r for r in self.register['transfer_assurance']['source_occurrence_reviews'].values()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in names]
        self.assertEqual(len(selected), 533)
        self.assertEqual(sum(r['applicability'] == 'transfer_shared' for r in selected), 493)
        self.assertEqual(sum(r['applicability'] == 'separate_note_reshape_milestone' for r in selected), 21)
        self.assertEqual(sum(r['applicability'] == 'separate_withdrawal_milestone' for r in selected), 19)
        for review in selected:
            self.assertIn('Referenced test body, assertions, intended failure cause, resource use and execution result are not established', review['reason'])
            self.assertIn('prover_required=false is a historical scheduling flag', review['reason'])
            self.assertIn('No current semantic-control, theorem or certification credit', review['reason'])
            self.assertEqual(review['status'], 'open')
            self.assertEqual(review['evidence'], [])
            if review['applicability'] != 'transfer_shared':
                self.assertEqual(review['obligation'], 'current:migration-review')

    def test_complete_aggregate_metadata_keeps_declared_evidence_unadopted(self):
        selected = {r['selector']['member']: r for r in
                    self.register['transfer_assurance']['source_occurrence_reviews'].values()
                    if r['review'] == 'complete_metadata_structure_reviewed_applicability_only'}
        self.assertEqual(set(selected), {'/reviewed_test_census', '/tests', '/evidence_sets'})
        census = selected['/reviewed_test_census']
        self.assertIn('260 unique source path strings,908 unique selected(path,symbol) records and468', census['reason'])
        self.assertIn('no exclusion is adopted as current retirement', census['reason'])
        self.assertIn('All15 full execution variants were inspected', selected['/tests']['reason'])
        self.assertIn('no body/fixture/intended cause/execution is established', selected['/tests']['reason'])
        evidence = selected['/evidence_sets']
        self.assertIn('Every trace record/args/type/ID/operation/profile/count', evidence['reason'])
        self.assertIn('do not establish row semantics', evidence['reason'])
        self.assertIn('cannot replace those current obligations', evidence['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))

    def test_scope_and_fingerprint_metadata_preserve_all_exact_occurrences(self):
        selected = [r for r in self.register['transfer_assurance']['source_occurrence_reviews'].values()
                    if r['review'] in {'complete_scope_membership_metadata_reviewed_applicability_only',
                                       'complete_fingerprint_array_metadata_reviewed_applicability_only'}]
        self.assertEqual(len(selected), 17)
        scopes = [r for r in selected if r['selector']['source'].startswith('@scope/')]
        self.assertEqual(len(scopes), 15)
        self.assertTrue(all(r['selector']['member'] == 'whole-group' for r in scopes))
        self.assertTrue(all('not referenced source bodies' in r['reason'] and
                            'No blanket retirement' in r['reason'] for r in scopes))
        arrays = {r['selector']['member']: r for r in selected if r not in scopes}
        self.assertEqual(set(arrays), {'/lean_declaration_fingerprints', '/test_source_fingerprints'})
        self.assertIn('Complete 215-record array covers19', arrays['/lean_declaration_fingerprints']['reason'])
        self.assertIn('Complete 940-record array covers175', arrays['/test_source_fingerprints']['reason'])
        self.assertTrue(all(r['selector']['owner'] == 'circuit-crypto' and
                            r['applicability'] == 'transfer_shared' and
                            r['status'] == 'open' and r['evidence'] == [] for r in selected))

    def test_scope_and_fingerprint_metadata_drift_and_unconsumed_extra_refused(self):
        universe = {key: r['selector'] for key, r in
                    self.register['transfer_assurance']['source_occurrence_reviews'].items()}
        for name in ('HISTORICAL_COMPLETE_SCOPE_MEMBERSHIP_METADATA_REVIEWS',
                     'HISTORICAL_COMPLETE_FINGERPRINT_ARRAY_METADATA_REVIEWS'):
            original = getattr(coverage, name)
            changed = list(original[0]); changed[3] = '0' * 64
            with patch.object(coverage, name, (tuple(changed),) + original[1:]):
                with self.assertRaisesRegex(ValueError, 'selector changed'):
                    coverage.source_occurrence_reviews(universe)
            with patch.object(coverage, name, original + original[:1]):
                with self.assertRaisesRegex(ValueError, 'metadata review membership changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_fingerprint_metadata_keeps_unresolved_raw_body_and_no_result_adoption(self):
        arrays = {r['selector']['member']: r for r in
                  self.register['transfer_assurance']['source_occurrence_reviews'].values()
                  if r['review'] == 'complete_fingerprint_array_metadata_reviewed_applicability_only'}
        tests = arrays['/test_source_fingerprints']
        self.assertIn('23 raw matches and112 mismatches, plus40 absent paths', tests['reason'])
        self.assertIn('LF/CRLF variants did not resolve those112', tests['reason'])
        self.assertIn('not a test body/assertion/intended cause/result', tests['reason'])
        self.assertIn('No historical execution result or semantic-control credit is adopted', tests['reason'])
        declarations = arrays['/lean_declaration_fingerprints']
        self.assertIn('do not contain full theorem bodies', declarations['reason'])
        self.assertIn('No old theorem or generated gnark relation is adopted', declarations['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in arrays.values()))

    def test_profile_expansion_and_pending_source_accounting(self):
        result = self.check()
        self.assertEqual(result['requirements'], 97)
        self.assertEqual(result['reviewed_migration_occurrences'], 3462)
        self.assertEqual(result['pending_migration_review'], 0)
        self.assertEqual(result['status'], 'open')

    def test_exact_member_reviews_keep_all_occurrences_and_open_targets(self):
        section = self.register['transfer_assurance']
        reviews = section['source_occurrence_reviews']
        self.assertEqual(len(reviews), 3462)
        self.assertEqual(sum(r['applicability'] == 'transfer_shared' for r in reviews.values()), 2819)
        self.assertEqual(sum('note_reshape' in r['applicability'] for r in reviews.values()), 339)
        self.assertEqual(sum('withdrawal' in r['applicability'] for r in reviews.values()), 301)
        self.assertEqual(sum(r['applicability'] == 'retired_history' for r in reviews.values()), 3)
        self.assertTrue(all(r['status'] == 'open' and not r['evidence'] for r in reviews.values()))
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        self.assertEqual(sum(g['count'] for g in section['occurrence_groups'].values()), len(universe))
        transfer = next(r for r in reviews.values()
                        if r['selector']['name'] == 'lemma_transfer_field_count_injective')
        self.assertIn('<= 1', transfer['reason'])
        self.assertEqual(transfer['obligation'], 'current:statement')

    def test_decoder_reviews_keep_imported_predicate_and_native_codec_gap(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        decoder = [r for r in reviews.values()
                   if r['selector']['source'] == '@history/decoder/CanonicalEncodingProofs.fst']
        self.assertEqual(len(decoder), 5)
        self.assertTrue(all(r['obligation'] == 'current:admission' for r in decoder))
        accepted = next(r for r in decoder if r['selector']['name'] == 'accepted_bytes_are_canonical')
        self.assertIn('only under imported canonical_encoding_matches', accepted['reason'])
        self.assertIn('absent', accepted['reason'])
        reflexive = next(r for r in decoder if r['selector']['name'] == 'canonical_bytes_are_accepted')
        self.assertIn('no premise that these bytes decode', reflexive['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in decoder))

    def test_wrapper_reviews_preserve_current_parser_contract(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        wrapper = [r for r in reviews.values()
                   if r['selector']['source'] == '@history/decoder/WrapperBoundaryProofs.fst']
        self.assertEqual(len(wrapper), 4)
        truncated = next(r for r in wrapper if r['selector']['name'] == 'truncated_header_is_rejected')
        self.assertIn('historical 73-byte', truncated['reason'])
        self.assertIn('exact 244-byte', truncated['reason'])
        unsupported = next(r for r in wrapper if r['selector']['name'] == 'unsupported_domain_is_rejected')
        self.assertIn('SUITE and a known Family byte', unsupported['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in wrapper))

    def test_decaf_exact_bodies_preserve_live_contracts_and_changed_instance(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {entry[0] for entry in coverage.DECAF_COMMON_REVIEWS}
        decaf = [r for r in reviews.values() if r['selector']['source'] == 'lean/Common.lean'
                 and r['selector']['member'] in members]
        self.assertEqual(len(decaf), 17)
        self.assertTrue(all(r['selector']['owner'] == 'circuit-crypto' for r in decaf))
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in decaf))
        by_name = {r['selector']['name']: r for r in decaf}
        self.assertIn('(0,-1)', by_name['nonIdentity']['reason'])
        self.assertIn('subgroup', by_name['nonIdentity']['reason'])
        self.assertEqual(by_name['generator']['obligation'], 'current:action-key')
        self.assertEqual(by_name['valueBlindingGenerator']['obligation'], 'current:balance')
        self.assertEqual(by_name['incomingViewingKeyNonzero']['obligation'], 'current:ownership')
        self.assertIn('252', by_name['scalarMulLE']['reason'])
        self.assertIn('255', by_name['scalarMulLE']['reason'])
        # Its independent family review cannot supply Transfer evidence.
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        remaining = [key for key, selector in universe.items()
                     if selector.get('source') == 'lean/NoteReshape/Concrete.lean'
                     and selector.get('name') == 'noteCommitment']
        self.assertEqual(len(remaining), 1)
        dependent = reviews[remaining[0]]
        self.assertEqual(dependent['applicability'], 'separate_note_reshape_milestone')
        self.assertEqual(dependent['status'], 'open')
        self.assertEqual(dependent['evidence'], [])
        self.assertIn('Old hash5', dependent['reason'])
        self.assertIn('current NOTE hash8 and recovery/address4 differ', dependent['reason'])
        original = copy.deepcopy(by_name['nonIdentity'])
        key = coverage.identity(original['selector'])
        for field, value in [('obligation', 'current:upstream-contract'),
                             ('reason', 'upstream assumed; algorithm retired'),
                             ('status', 'proved'), ('evidence', ['old-native-test'])]:
            reviews[key] = {**copy.deepcopy(original), field: value}
            with self.subTest(field=field), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                self.check()
        reviews[key] = original

    def test_complete_concrete_review_preserves_each_exact_body_and_live_obligation(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        concrete = {key: r for key, r in reviews.items()
                    if r['selector']['source'] == 'lean/Transfer/Concrete.lean'}
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        self.assertEqual(len(concrete), 73)
        self.assertEqual(set(concrete), {key for key, selector in universe.items()
                                       if selector.get('source') == 'lean/Transfer/Concrete.lean'})
        self.assertTrue(all(r['selector'] == universe[key] for key, r in concrete.items()))
        self.assertTrue(all(r['disposition'] == 'replaced' and r['applicability'] == 'transfer_shared'
                            and r['status'] == 'open' and r['evidence'] == []
                            for r in concrete.values()))
        names = {r['selector']['name']: r for r in concrete.values()}
        expected = {'canonicalSender': 'ownership', 'realSpend': 'spends',
                    '.dummy spend =>': 'spends', 'assetRegistry': 'registry',
                    'complianceMembership': 'compliance', 'thresholdFlag': 'volume',
                    'sharedSecrets': 'disclosure', 'balanceComputedAndCompressed': 'balance',
                    'statementFields': 'statement', 'circuitPrimitives': 'full-relation'}
        for name, obligation in expected.items():
            self.assertEqual(names[name]['obligation'], 'current:' + obligation)
        self.assertIn('no AK/RK relation', names['.dummy spend =>']['reason'])
        self.assertIn('permanent replay', names['realSpend']['reason'])
        self.assertIn('global registry uniqueness', names['assetRegistry']['reason'])
        self.assertIn('unconditional131-bit lifecycle', names['complianceMembership']['reason'])
        self.assertIn('no nonzero esk premise', names['sharedSecrets']['reason'])
        self.assertIn('Per-action net may be nonzero', names['balanceComputedAndCompressed']['reason'])
        self.assertIn('length45', names['statementFields_length']['reason'])
        self.assertIn('no proof that arbitrary compiled rows', names['circuitPrimitives']['reason'])

    def test_concrete_body_drift_fails_before_register_mapping(self):
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        original = coverage.TRANSFER_CONCRETE_REVIEWS
        changed = original[0][:3] + ('f' * 64,) + original[0][4:]
        with patch.object(coverage, 'TRANSFER_CONCRETE_REVIEWS', (changed,) + original[1:]):
            with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                coverage.source_occurrence_reviews(universe)

    def test_concrete_mixed_history_body_cannot_be_bulk_retired_or_promoted(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        key = next(key for key, review in reviews.items()
                   if review['selector']['source'] == 'lean/Transfer/Concrete.lean'
                   and review['selector']['name'] == 'realSpend')
        original = copy.deepcopy(reviews[key])
        for changes in [dict(applicability='retired_history', disposition='retired',
                             obligation='current:migration-review'),
                        dict(obligation='current:upstream-contract'),
                        dict(status='proved', evidence=['old-Concrete-definition']),
                        dict(reason='All Decaf and history bodies are retired')]:
            reviews[key] = {**copy.deepcopy(original), **changes}
            with self.subTest(changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                self.check()
        reviews[key] = original
        del reviews[key]
        with self.assertRaisesRegex(security.CheckError, 'applicability review'):
            self.check()

    def test_complete_sponge_and_history_modules_keep_current_instances_and_premises(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        for source, count in [('lean/StatementSponge.lean', 6),
                              ('lean/NullifierHistory/Semantics.lean', 26),
                              ('lean/NullifierHistory/Security.lean', 14)]:
            selected = {key: r for key, r in reviews.items() if r['selector']['source'] == source}
            self.assertEqual(len(selected), count)
            self.assertEqual(set(selected), {key for key, s in universe.items() if s.get('source') == source})
            self.assertTrue(all(r['selector'] == universe[key] and r['status'] == 'open'
                                and r['evidence'] == [] and r['disposition'] == 'replaced'
                                for key, r in selected.items()))
        sponge = {r['selector']['name']: r for r in reviews.values()
                  if r['selector']['source'] == 'lean/StatementSponge.lean'}
        self.assertIn('persistent width6/rate5', sponge['statementTail_six']['reason'])
        self.assertIn('pad1,pad0,pad1', sponge['statementTail_one']['reason'])
        self.assertIn('thirteen absorptions', sponge['statementTail_twentyFive']['reason'])
        history = {r['selector']['name']: r for r in reviews.values()
                   if r['selector']['source'] == 'lean/NullifierHistory/Semantics.lean'}
        self.assertIn('unconditional permanent replay', history['expectedHistoryRequired']['reason'])
        self.assertIn('ASSUMES authenticatedGapExcludes', history['IndexedTreeSound']['reason'])
        self.assertIn('no separate32-bit next_index range', history['LeafCanonical']['reason'])
        self.assertIn('native u64 encoding/link invariant', history['LeafCanonical']['reason'])
        self.assertIn('not a recursive verifier proof', history['ChunkRelation']['reason'])
        proof = {r['selector']['name']: r for r in reviews.values()
                 if r['selector']['source'] == 'lean/NullifierHistory/Security.lean'}
        self.assertEqual(proof['generation_relation_proves_nonmembership']['obligation'], 'current:registry')
        self.assertIn('desired global indexed-tree soundness premise',
                      proof['generation_relation_proves_nonmembership']['reason'])
        self.assertIn('Both base-proof soundness',
                      proof['chunk_proves_each_generation_nonmembership']['reason'])
        self.assertIn('opaque assumed predicate', proof['chunk_verifies_every_base_proof']['reason'])
        self.assertIn('not Groth16 or Pari zero knowledge',
                      proof['chunk_disclosure_depends_only_on_public_claim']['reason'])

    def test_history_nonmembership_and_public_projection_cannot_promote_global_soundness_or_zk(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        for name in ['IndexedTreeSound', 'chunk_proves_each_generation_nonmembership',
                     'chunk_disclosure_depends_only_on_public_claim', 'expectedHistoryRequired']:
            key = next(key for key, r in reviews.items() if r['selector']['name'] == name
                       and r['selector']['source'].startswith('lean/NullifierHistory/'))
            original = copy.deepcopy(reviews[key])
            for changes in [dict(status='proved', evidence=['historical-proof']),
                            dict(applicability='retired_history', disposition='retired'),
                            dict(obligation='current:upstream-contract')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=name, changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original

    def test_complete_alloy_review_retains_bounded_scopes_and_assumed_security_conclusions(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        for source, count in [('alloy/transfer-statement-sufficiency.als', 91),
                              ('alloy/value-conservation.als', 22)]:
            selected = {key: r for key, r in reviews.items() if r['selector']['source'] == source}
            self.assertEqual(len(selected), count)
            self.assertEqual(set(selected), {key for key, s in universe.items() if s.get('source') == source})
            self.assertTrue(all(r['selector'] == universe[key] and r['status'] == 'open'
                                and r['evidence'] == [] and r['disposition'] == 'replaced'
                                for key, r in selected.items()))
        transfer = {r['selector']['member']: r for r in reviews.values()
                    if r['selector']['source'] == 'alloy/transfer-statement-sufficiency.als'}
        self.assertIn('ASSUMES each Accepted', transfer['L179-L185']['reason'])
        self.assertIn('Finite current hashes cannot be globally injective', transfer['L150-L161']['reason'])
        self.assertIn('actual valid Transfer actions'.lower(), transfer['L258-L262']['reason'].lower())
        self.assertIn('not global AK-from-RK injectivity', transfer['L298-L303']['reason'])
        self.assertEqual(transfer['L283-L288']['selector']['owner'], 'state-integration')
        self.assertEqual(transfer['L322-L322']['selector']['owner'], 'state-integration')
        self.assertIn('4-bit Int', transfer['L322-L322']['reason'])
        self.assertIn('no observed solver result', transfer['L322-L322']['reason'])
        value = {r['selector']['member']: r for r in reviews.values()
                 if r['selector']['source'] == 'alloy/value-conservation.als'}
        self.assertIn('SET of Action', value['L38-L39']['reason'])
        self.assertIn('DEFIN', value['L53-L56']['reason'])
        self.assertIn('desired value-part conclusion', value['L53-L56']['reason'])
        self.assertIn('not mathematical independence', value['L63-L66']['reason'])
        self.assertIn('no cryptographic signature or actual group theorem', value['L67-L70']['reason'])
        self.assertIn('6-bit Int', value['L71-L72']['reason'])

    def test_alloy_fact_or_check_identity_cannot_be_current_proof_or_native_test(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        for source, member in [('alloy/transfer-statement-sufficiency.als', 'L258-L262'),
                               ('alloy/transfer-statement-sufficiency.als', 'L322-L322'),
                               ('alloy/value-conservation.als', 'L53-L56'),
                               ('alloy/value-conservation.als', 'L71-L72')]:
            key = next(key for key, r in reviews.items()
                       if r['selector']['source'] == source and r['selector']['member'] == member)
            original = copy.deepcopy(reviews[key])
            for changes in [dict(status='bounded_verified', evidence=['check-command-hash']),
                            dict(status='proved', evidence=['assumed-fact']),
                            dict(evidence=['current-runtime-test']),
                            dict(disposition='retired', applicability='retired_history')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(source=source, member=member, changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original

    def test_complete_historical_ledgers_preserve_current_primitive_and_external_boundaries(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        for source, count in [('shielded-pool/circuit-gadget-proofs.md', 17),
                              ('shielded-pool/circuit-soundness-properties.md', 24)]:
            selected = {key: r for key, r in reviews.items() if r['selector']['source'] == source}
            self.assertEqual(len(selected), count)
            self.assertEqual(set(selected), {key for key, s in universe.items() if s.get('source') == source})
            self.assertTrue(all(r['selector'] == universe[key] and r['status'] == 'open'
                                and r['evidence'] == [] for key, r in selected.items()))
        gadget = {r['selector']['name']: r for r in reviews.values()
                  if r['selector']['source'] == 'shielded-pool/circuit-gadget-proofs.md'}
        self.assertIn('actual same-assignment equations', gadget['gadget-iszero']['reason'])
        self.assertIn('effective RNK/nk', gadget['gadget-nullifier']['reason'])
        self.assertIn('volume deliberately uses raw nk', gadget['gadget-nullifier']['reason'])
        self.assertIn('127/128-bit bounded limb comparisons', gadget['gadget-imt-gap']['reason'])
        props = {r['selector']['name']: r for r in reviews.values()
                 if r['selector']['source'] == 'shielded-pool/circuit-soundness-properties.md'}
        self.assertIn('<=253', props['ZK-PROP-AMOUNT-RANGE-128']['reason'])
        self.assertIn('255 bits and modulus bound', props['ZK-PROP-AMOUNT-RANGE-128']['reason'])
        self.assertIn('131-bit lifecycle', props['REGULATED-STATUS-SOUNDNESS']['reason'])
        self.assertIn('independently authorized/current roots', props['REGULATED-STATUS-SOUNDNESS']['reason'])
        self.assertIn('core confirmations', props['CIPHERTEXT-CORRECTNESS']['reason'])
        self.assertIn('Nonzero current ephemerals are constrained', props['CIPHERTEXT-CORRECTNESS']['reason'])
        self.assertIn('live issuer DLEQ', props['SYMBOLIC-LEMMA-CLOSURE']['reason'])
        self.assertEqual(props['NOTE-RESHAPE-LEAN-SOUNDNESS']['applicability'], 'separate_note_reshape_milestone')
        self.assertEqual(props['WITHDRAWAL-LEAN-SOUNDNESS']['applicability'], 'separate_withdrawal_milestone')
        self.assertEqual(props['ZK-PROP-NOTE-RESHAPE-STATEMENT-SEAM']['applicability'], 'separate_note_reshape_milestone')
        self.assertIn('family-specific contract', props['WITHDRAWAL-LEAN-SOUNDNESS']['contract'])

    def test_old_gadget_proved_label_and_other_family_seam_cannot_certify_transfer(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        for name in ['gadget-poseidon2', 'gadget-nullifier', 'ZK-PROP-AMOUNT-RANGE-128',
                     'ZK-PROP-NOTE-RESHAPE-STATEMENT-SEAM']:
            key = next(key for key, r in reviews.items() if r['selector']['name'] == name
                       and r['selector']['source'].startswith('shielded-pool/'))
            original = copy.deepcopy(reviews[key])
            changes = [dict(status='proved', evidence=['old-ACL2-artifact']),
                       dict(evidence=['same-row-count-parity']),
                       dict(obligation='current:upstream-contract')]
            if name == 'ZK-PROP-NOTE-RESHAPE-STATEMENT-SEAM':
                changes.append(dict(applicability='transfer_shared', obligation='current:statement'))
            for change in changes:
                reviews[key] = {**copy.deepcopy(original), **change}
                with self.subTest(name=name, change=change), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original

    def test_matrix_range_reviews_preserve_current_scalar_volume_and_native_source_deltas(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_RANGE_REVIEWS}
        selected = {key: r for key, r in reviews.items()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members}
        self.assertEqual(len(selected), 14)
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        self.assertTrue(all(r['selector'] == universe[key] and r['status'] == 'open'
                            and r['evidence'] == [] for key, r in selected.items()))
        names = {r['selector']['name']: r for r in selected.values()}
        self.assertEqual(names['FIELD-AUTH-RANDOMIZER-RANGE']['obligation'], 'current:action-key')
        self.assertIn('one shared action randomizer', names['FIELD-AUTH-RANDOMIZER-RANGE']['reason'])
        self.assertIn('all126 fixed windows', names['FIELD-AUTH-RANDOMIZER-RANGE']['reason'])
        self.assertIn('nonzero is absent', names['FIELD-EPHEMERAL-SCALAR-RANGE']['reason'])
        self.assertIn('ledger-evidence NR-CONSTRUCTION label',
                      names['EXT-HONEST-COMPLIANCE-TIER-SCALAR-NONZERO']['reason'])
        self.assertEqual(names['EXT-HONEST-COMPLIANCE-TIER-SCALAR-NONZERO']['obligation'], 'current:privacy')
        self.assertIn('no longer carries d', names['FIELD-USER-DERIVATION-RANGE']['reason'])
        self.assertIn('131-bit lifecycle', names['FIELD-USER-DERIVATION-RANGE']['reason'])
        self.assertIn('does not imply a32-bit registry next_index range',
                      names['FIELD-USER-POSITION-RANGE']['reason'])
        self.assertEqual(names['COMPLIANCE-THRESHOLD-FLAG']['obligation'], 'current:volume')
        self.assertIn('inclusive cumulative prior+outbound128<=dailyLimit',
                      names['COMPLIANCE-THRESHOLD-FLAG']['reason'])
        self.assertIn('unconditional even on padding/fee', names['VALUE-AMOUNT-128-RANGE']['reason'])
        self.assertIn('day/raw-nk replay', names['VALUE-THRESHOLD-128-RANGE']['reason'])

    def test_matrix_role_reference_or_old_range_theorem_cannot_promote_current_qualification(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        for name in ['ASSET-REGISTRY-GAP-ORDERING', 'FIELD-AUTH-RANDOMIZER-RANGE',
                     'FIELD-EPHEMERAL-SCALAR-RANGE', 'COMPLIANCE-THRESHOLD-FLAG']:
            key = next(key for key, r in reviews.items()
                       if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                       and r['selector']['name'] == name)
            original = copy.deepcopy(reviews[key])
            for changes in [dict(status='proved', evidence=['old-SpecificationConsequences']),
                            dict(evidence=['matching-trace-name']),
                            dict(obligation='current:upstream-contract'),
                            dict(disposition='retired', applicability='retired_history')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=name, changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        original = coverage.MATRIX_RANGE_REVIEWS
        changed = original[0][:3] + ('f' * 64,) + original[0][4:]
        with patch.object(coverage, 'MATRIX_RANGE_REVIEWS', (changed,) + original[1:]):
            with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                coverage.source_occurrence_reviews(universe)

    def test_registry_matrix_reviews_preserve_actual_conclusions_and_current_snapshot_semantics(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_REGISTRY_REVIEWS + coverage.MATRIX_REGISTRY_STATE_REVIEWS}
        selected = [r for r in reviews.values()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members]
        self.assertEqual(len(selected), 16)
        names = {r['selector']['name']: r for r in selected}
        self.assertIn('two rfl hash5 unfoldings', names['USER-LEAF-CANONICAL-DERIVATION-BINDING']['reason'])
        self.assertIn('does not include Active status', names['USER-COMPLIANCE-MEMBERSHIP-GATE']['reason'])
        self.assertIn('does not itself assert nonidentity', names['ASSET-POLICY-KEY-ENCODING']['reason'])
        self.assertIn('combined ring/audit hashes', names['ASSET-LEAF-HASH']['reason'])
        self.assertIn('hash2', names['ASSET-RING-HASH']['reason'])
        self.assertIn('current-pair fast-path', names['EXT-COMPLIANCE-ANCHOR-LIVE']['reason'])
        self.assertIn('nonfuture inclusive max age', names['EXT-ASSET-ANCHOR-CURRENT']['reason'])
        self.assertIn('FQ_MAX', names['EXT-REGISTRY-WELL-FORMED']['reason'])
        self.assertIn('chain-bound capability certificate', names['EXT-USER-REGISTRY-AUTHORIZED']['reason'])
        self.assertEqual(names['EXT-ASSET-ANCHOR-CURRENT']['obligation'], 'current:state')
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected))
        self.assertEqual(sum(r['selector']['owner'] == 'state-integration' for r in selected), 6)

    def test_registry_metadata_cannot_prove_canonical_derivation_or_current_root_admission(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        for name in ['USER-LEAF-CANONICAL-DERIVATION-BINDING', 'EXT-REGISTRY-WELL-FORMED',
                     'EXT-COMPLIANCE-ANCHOR-LIVE', 'EXT-ASSET-REGISTRY-KEY-VALIDITY']:
            key = next(k for k, r in reviews.items()
                       if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                       and r['selector']['name'] == name)
            original = copy.deepcopy(reviews[key])
            for changes in [dict(status='proved', evidence=['old-export-name']),
                            dict(evidence=['native-source-read']),
                            dict(obligation='current:upstream-contract'),
                            dict(reason='Accept every independently live root and assume canonical derivation.')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=name, changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        original = coverage.MATRIX_REGISTRY_STATE_REVIEWS
        changed = original[0][:3] + ('0' * 64,) + original[0][4:]
        with patch.object(coverage, 'MATRIX_REGISTRY_STATE_REVIEWS', (changed,) + original[1:]):
            with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                coverage.source_occurrence_reviews(universe)

    def test_encryption_matrix_reviews_preserve_plaintext_roles_and_separate_entropy(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_ENCRYPTION_REVIEWS}
        selected = [r for r in reviews.values()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members]
        self.assertEqual(len(selected), 10)
        names = {r['selector']['name']: r for r in selected}
        self.assertIn('receiver address in senderExt', names['COMPLIANCE-ADDRESS-ENCRYPTION']['reason'])
        self.assertIn('independent confirmation hash4', names['COMPLIANCE-AMOUNT-ENCRYPTION']['reason'])
        self.assertIn('regardless of payload-key selection', names['COMPLIANCE-DETECTION-ENCRYPTION']['reason'])
        self.assertIn('two ordered ownership ciphertexts', names['COMPLIANCE-METADATA-BINDING']['reason'])
        self.assertIn('six rfl definition unfoldings', names['COMPLIANCE-POLICY-SELECTION']['reason'])
        self.assertIn('does not prove fresh unpredictable nonces', names['COMPLIANCE-SALT-DERIVATION']['reason'])
        self.assertIn('distinct audit.checking', names['COMPLIANCE-SHARED-SECRET-SELECTION']['reason'])
        self.assertIn('two rfl scalarMulWindow2', names['DEC-ACK-DERIVATION']['reason'])
        self.assertIn('does not claim ciphertext3 is zero', names['FIELD-DETECTION-RESERVED-ZERO']['reason'])
        self.assertEqual(names['COMPLIANCE-SALT-DERIVATION']['obligation'], 'current:privacy')
        self.assertEqual(names['COMPLIANCE-FLAG-BOOLEAN']['obligation'], 'current:volume')
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected))

    def test_old_encryption_roles_or_source_read_cannot_supply_current_crypto_qualification(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        for name in ['COMPLIANCE-ADDRESS-ENCRYPTION', 'COMPLIANCE-SALT-DERIVATION',
                     'DEC-ACK-DERIVATION', 'FIELD-DETECTION-RESERVED-ZERO']:
            key = next(k for k, r in reviews.items()
                       if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                       and r['selector']['name'] == name)
            original = copy.deepcopy(reviews[key])
            for changes in [dict(status='proved', evidence=['old-transcript-provider']),
                            dict(evidence=['current-encryption-source']),
                            dict(obligation='current:upstream-contract')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=name, changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        original = coverage.MATRIX_ENCRYPTION_REVIEWS
        changed = original[0][:3] + ('0' * 64,) + original[0][4:]
        with patch.object(coverage, 'MATRIX_ENCRYPTION_REVIEWS', (changed,) + original[1:]):
            with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                coverage.source_occurrence_reviews(universe)

    def test_auth_balance_matrix_keeps_cofactor_and_aggregate_contracts_open(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_AUTH_BALANCE_REVIEWS}
        selected = {k: r for k, r in reviews.items()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members}
        self.assertEqual(len(selected), 4)
        names = {r['selector']['name']: r for r in selected.values()}
        self.assertIn('on-curve cofactor8 preimage', names['DEC-AUTHORIZATION-KEY-ENCODING']['reason'])
        self.assertIn('exact captured LC', names['DEC-AUTHORIZATION-KEY-NONIDENTITY']['reason'])
        self.assertIn('not zero net value', names['DEC-BALANCE-COMMITMENT-DERIVATION']['reason'])
        self.assertIn('transaction body+fee multiplicity', names['DEC-BALANCE-COMMITMENT-DERIVATION']['reason'])
        self.assertIn('two affine balance coordinates', names['DEC-BALANCE-COMMITMENT-ENCODING']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, review in selected.items():
            original = copy.deepcopy(review)
            for changes in [dict(evidence=['old-deployed-theorem']), dict(status='proved'),
                            dict(obligation='current:conservation'),
                            dict(applicability='retired_history', disposition='retired')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=review['selector']['name'], changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original

    def test_address_epk_matrix_preserves_native_codec_and_reduction_security_boundary(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_ADDRESS_EPK_REVIEWS}
        selected = {k: r for k, r in reviews.items()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members}
        self.assertEqual(len(selected), 5)
        names = {r['selector']['name']: r for r in selected.values()}
        self.assertIn('canonical y plus x parity', names['DEC-DIVERSIFIED-GENERATOR-ENCODING']['reason'])
        self.assertIn('including unregulated branches', names['DEC-DIVERSIFIED-GENERATOR-NONIDENTITY']['reason'])
        self.assertIn('twelve existential points', names['DEC-EPHEMERAL-PUBLIC-KEY-DERIVATION']['reason'])
        self.assertIn('all four ordered tier', names['DEC-EPHEMERAL-PUBLIC-KEY-ENCODING']['reason'])
        self.assertIn('q=8 remainder<=P-1-8R', names['DEC-INCOMING-VIEWING-KEY-DERIVATION']['reason'])
        self.assertIn('does not imply hash preimage injectivity', names['DEC-INCOMING-VIEWING-KEY-DERIVATION']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, review in selected.items():
            original = copy.deepcopy(review)
            for changes in [dict(evidence=['retired-compression-parity']), dict(status='proved'),
                            dict(obligation='current:upstream-contract')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=review['selector']['name'], changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original

    def test_key_matrix_reviews_keep_shared_rk_and_native_signature_scope(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_KEY_JOIN_REVIEWS}
        selected = {k: r for k, r in reviews.items()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members}
        self.assertEqual(len(selected), 7)
        names = {r['selector']['name']: r for r in selected.values()}
        self.assertIn('one shared native body.rk', names['DEC-RANDOMIZED-VERIFICATION-KEY-NONIDENTITY']['reason'])
        self.assertIn('nonidentity before verifying', names['DEC-RANDOMIZED-VERIFICATION-KEY-NONIDENTITY']['reason'])
        self.assertIn('has no specification_dec_spend_rk_derivation export', names['DEC-SPEND-RK-DERIVATION']['reason'])
        self.assertIn('dummy optionalSpend omits derivation', names['DEC-SPEND-RK-DERIVATION']['reason'])
        self.assertIn('has no specification_dec_spend_rk_encoding export', names['DEC-SPEND-RK-ENCODING']['reason'])
        self.assertIn('does not prove receiver ownership', names['DEC-TRANSMISSION-KEY-DERIVATION']['reason'])
        self.assertIn('unregulated address points remain subgroup', names['DEC-TRANSMISSION-KEY-ENCODING']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, review in selected.items():
            original = copy.deepcopy(review)
            for changes in [dict(evidence=['generic-refinement-export']), dict(status='proved'),
                            dict(obligation='current:upstream-contract')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=review['selector']['name'], changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original

    def test_padding_matrix_preserves_unconditional_rows_and_fixed_source_slot(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_PADDING_REVIEWS}
        selected = {k: r for k, r in reviews.items()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members}
        self.assertEqual(len(selected), 3)
        names = {r['selector']['name']: r for r in selected.values()}
        self.assertIn('computation remain unconditional', names['DUMMY-AMOUNT-ZERO']['reason'])
        self.assertIn('both persisted slots', names['DUMMY-AMOUNT-ZERO']['reason'])
        self.assertIn('shared action randomizer', names['DUMMY-NULLIFIER-DOMAIN-BINDING']['reason'])
        self.assertIn('same dummy hash equality', names['DUMMY-SLOT-POSITION-BINDING']['reason'])
        self.assertIn('compiled source', names['DUMMY-SLOT-POSITION-BINDING']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, review in selected.items():
            original = copy.deepcopy(review)
            for changes in [dict(status='proved'), dict(evidence=['old-dummy-export']),
                            dict(reason='Ignore padding slots after zero amount.'),
                            dict(obligation='current:upstream-contract')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=review['selector']['name'], changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original

    def test_output_matrix_preserves_recovery_and_independent_receiver_roles(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_OUTPUT_REVIEWS}
        selected = {k: r for k, r in reviews.items()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members}
        self.assertEqual(len(selected), 3)
        names = {r['selector']['name']: r for r in selected.values()}
        self.assertIn('identical action asset LC', names['NOTE-OUTPUT-ASSET-BINDING']['reason'])
        self.assertIn('has no specification_note_output_commitment export', names['NOTE-OUTPUT-COMMITMENT']['reason'])
        self.assertIn('capsule equations for both outputs', names['NOTE-OUTPUT-COMMITMENT']['reason'])
        self.assertIn('no receiver secret-ownership theorem', names['NOTE-OUTPUT-OWNER-BINDING']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, review in selected.items():
            original = copy.deepcopy(review)
            for changes in [dict(status='proved'), dict(evidence=['old-note-parity']),
                            dict(obligation='current:upstream-contract')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=review['selector']['name'], changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original

    def test_spend_preimage_review_does_not_promote_membership_to_state_freshness(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_SPEND_PREIMAGE_REVIEWS}
        selected = {k: r for k, r in reviews.items()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members}
        self.assertEqual(len(selected), 2)
        names = {r['selector']['name']: r for r in selected.values()}
        self.assertIn('unconditionally,including padding', names['NOTE-SPEND-ASSET-BINDING']['reason'])
        self.assertIn('adds recovery commitment', names['NOTE-SPEND-COMMITMENT']['reason'])
        self.assertIn('does not establish anchor liveness', names['NOTE-SPEND-COMMITMENT']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, review in selected.items():
            original = copy.deepcopy(review)
            for changes in [dict(status='proved'), dict(evidence=['old-input-note-export']),
                            dict(obligation='current:state')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=review['selector']['name'], changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original

    def test_spend_membership_reviews_keep_effective_key_and_state_boundaries(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_SPEND_MEMBERSHIP_REVIEWS}
        selected = {k: r for k, r in reviews.items()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members}
        self.assertEqual(len(selected), 3)
        names = {r['selector']['name']: r for r in selected.values()}
        self.assertIn('volume nullifiers instead use raw nk', names['NOTE-SPEND-NULLIFIER-DERIVATION']['reason'])
        self.assertIn('does not assert secret ownership', names['NOTE-SPEND-OWNER-BINDING']['reason'])
        self.assertIn('has no specification_sct_spend_membership export', names['SCT-SPEND-MEMBERSHIP']['reason'])
        self.assertIn('reuses exact Boolean48-bit position', names['SCT-SPEND-MEMBERSHIP']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, review in selected.items():
            original = copy.deepcopy(review)
            for changes in [dict(status='proved'), dict(evidence=['old-realSpend-fact']),
                            dict(obligation='current:state')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(name=review['selector']['name'], changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original

    def test_complete_nullifier_imt_model_review_preserves_weak_insertion_statement(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        selected = {k: r for k, r in reviews.items()
                    if r['selector']['source'] == 'alloy/nullifier-imt.als'}
        self.assertEqual(len(selected), 31)
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        expected = {k for k, selector in universe.items()
                    if selector.get('source') == 'alloy/nullifier-imt.als'}
        self.assertEqual(set(selected), expected)
        members = {r['selector']['member']: r for r in selected.values()}
        self.assertIn('same block collapse', members['L37-L39']['reason'])
        self.assertIn('already assumes cross-block no-respend', members['L42-L46']['reason'])
        self.assertIn('terminal index0 uses reserved FQ_MAX', members['L62-L64']['reason'])
        self.assertIn('one connected walk visiting all leaves', members['L72-L79']['reason'])
        self.assertIn('no after-tree mutation', members['L99-L108']['reason'])
        self.assertIn('omits nu not in leaves', members['L99-L108']['reason'])
        self.assertIn('no gap/new-leaf witness', members['L115-L121']['reason'])
        self.assertTrue(all(r['selector']['owner'] == 'state-integration'
                            and r['status'] == 'open' and r['evidence'] == []
                            for r in selected.values()))

    def test_model_commands_and_insertion_name_cannot_promote_current_state_guarantees(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        for member in ['L42-L46', 'L52-L53', 'L99-L108', 'L109-L110', 'L122-L122']:
            key = next(k for k, r in reviews.items()
                       if r['selector']['source'] == 'alloy/nullifier-imt.als'
                       and r['selector']['member'] == member)
            original = copy.deepcopy(reviews[key])
            for changes in [dict(status='proved'), dict(evidence=['historical-Alloy-check']),
                            dict(obligation='current:upstream-contract'),
                            dict(reason='The assertion name proves current native insertion and durable no-respend.')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(member=member, changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        original = coverage.NULLIFIER_IMT_ALLOY_REVIEWS
        changed = original[0][:3] + ('0' * 64,) + original[0][4:]
        with patch.object(coverage, 'NULLIFIER_IMT_ALLOY_REVIEWS', (changed,) + original[1:]):
            with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                coverage.source_occurrence_reviews(universe)

    def test_complete_compliance_tiers_review_preserves_replay_and_reachability_limits(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        selected = {k: r for k, r in reviews.items()
                    if r['selector']['source'] == 'alloy/compliance-tiers.als'}
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        expected = {k for k, selector in universe.items()
                    if selector.get('source') == 'alloy/compliance-tiers.als'}
        self.assertEqual(len(selected), 21)
        self.assertEqual(set(selected), expected)
        members = {r['selector']['member']: r for r in selected.values()}
        self.assertIn('excludes old Orbis PRE', members['L1-L20']['reason'])
        self.assertIn('all five same-state transitions', members['L26-L35']['reason'])
        self.assertIn('Complete to Complete', members['L37-L40']['reason'])
        self.assertIn('does not prove eventual completion', members['L44-L47']['reason'])
        self.assertIn('does not validate the evidence', members['L52-L55']['reason'])
        self.assertIn('no Transfer object or ciphertext/key fields', members['L60-L62']['reason'])
        self.assertIn('only for one nonterminal', members['L66-L69']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == []
                            and r['selector']['owner'] == 'state-integration'
                            for r in selected.values()))

    def test_compliance_graph_names_and_commands_cannot_certify_current_audit_crypto(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        for member in ['L1-L20', 'L26-L35', 'L37-L40', 'L44-L47', 'L60-L62', 'L70-L70']:
            key = next(k for k, r in reviews.items()
                       if r['selector']['source'] == 'alloy/compliance-tiers.als'
                       and r['selector']['member'] == member)
            original = copy.deepcopy(reviews[key])
            for changes in [dict(status='proved'), dict(evidence=['old-Alloy-audit-check']),
                            dict(obligation='current:upstream-contract'),
                            dict(reason='Reachability guarantees eventual audit completion and four-tier encryption correctness.')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(member=member, changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        original = coverage.COMPLIANCE_TIERS_ALLOY_REVIEWS
        changed = original[0][:3] + ('0' * 64,) + original[0][4:]
        with patch.object(coverage, 'COMPLIANCE_TIERS_ALLOY_REVIEWS', (changed,) + original[1:]):
            with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                coverage.source_occurrence_reviews(universe)

    def test_external_state_records_preserve_current_deltas_and_complete_envelope_premises(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_EXTERNAL_STATE_REVIEWS}
        selected = [r for r in reviews.values()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members]
        self.assertEqual(len(selected), 12)
        by_member = {r['selector']['member']: r for r in selected}
        self.assertIn('signatures alone do not bind it', by_member['/predicates/42']['reason'])
        self.assertIn('item hash cannot recover complete payloads', by_member['/predicates/47']['reason'])
        self.assertIn('including padding', by_member['/predicates/52']['reason'])
        self.assertIn('before one pending object_put', by_member['/predicates/53']['reason'])
        self.assertIn('no hash injectivity premise', by_member['/predicates/54']['reason'])
        self.assertIn('Retire that generation-history mechanism', by_member['/predicates/55']['reason'])
        self.assertIn('disclaims typed provenance', by_member['/predicates/56']['reason'])
        self.assertIn('explicitly omits append order', by_member['/predicates/59']['reason'])
        self.assertIn('3600-to1800', by_member['/predicates/67']['reason'])
        self.assertIn('desired committed/atomic facts', by_member['/predicates/69']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == []
                            and r['selector']['owner'] == 'state-integration' for r in selected))

    def test_external_state_acceptance_premises_cannot_certify_native_transition(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        for member in ['/predicates/' + str(i) for i in [42,47,53,55,56,59,67,69]]:
            key = next(k for k, r in reviews.items()
                       if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                       and r['selector']['member'] == member)
            original = copy.deepcopy(reviews[key])
            for changes in [dict(status='proved'), dict(evidence=['old-transition-test']),
                            dict(obligation='current:upstream-contract'),
                            dict(reason='Old external transition and committed facts prove current native durable atomicity.')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(member=member, changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        original = coverage.MATRIX_EXTERNAL_STATE_REVIEWS
        changed = original[0][:3] + ('0' * 64,) + original[0][4:]
        with patch.object(coverage, 'MATRIX_EXTERNAL_STATE_REVIEWS', (changed,) + original[1:]):
            with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                coverage.source_occurrence_reviews(universe)

    def test_codec_shape_reviews_distinguish_cardinality_from_row_and_native_coverage(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {e[0] for e in coverage.MATRIX_CODEC_SHAPE_REVIEWS}
        selected = [r for r in reviews.values()
                    if r['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and r['selector']['member'] in members]
        self.assertEqual(len(selected), 3)
        by_member = {r['selector']['member']: r for r in selected}
        self.assertIn('packs64bytes into31/31/2-byte words', by_member['/predicates/0']['reason'])
        self.assertIn('note/path ranges remain unconditional', by_member['/predicates/10']['reason'])
        self.assertIn('ignores relationAll in its proof', by_member['/predicates/11']['reason'])
        self.assertIn('length47', by_member['/predicates/11']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected))
        for review in selected:
            key = coverage.identity(review['selector']);original = copy.deepcopy(reviews[key])
            for changes in [dict(status='proved'), dict(evidence=['old-shape-lemma']),
                            dict(obligation='current:upstream-contract'),
                            dict(reason='Fixed statement length proves complete row coverage and native packing.')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(member=review['selector']['member'], changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        original = coverage.MATRIX_CODEC_SHAPE_REVIEWS
        changed = original[0][:3] + ('0' * 64,) + original[0][4:]
        with patch.object(coverage, 'MATRIX_CODEC_SHAPE_REVIEWS', (changed,) + original[1:]):
            with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                coverage.source_occurrence_reviews(universe)

    def test_complete_compliance_protocol_models_keep_imported_and_closed_world_limits(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        for source, count in [('protocol/compliance-active.spthy', 29), ('protocol/compliance.spthy', 20)]:
            selected = {k: r for k, r in reviews.items() if r['selector']['source'] == source}
            expected = {k for k, r in universe.items() if r.get('source') == source}
            self.assertEqual(len(selected), count);self.assertEqual(set(selected), expected)
            self.assertTrue(all(r['status'] == 'open' and r['evidence'] == []
                                and r['selector']['owner'] == 'protocol' for r in selected.values()))
        active = {r['selector']['member']: r for r in reviews.values()
                  if r['selector']['source'] == 'protocol/compliance-active.spthy'}
        closed = {r['selector']['member']: r for r in reviews.values()
                  if r['selector']['source'] == 'protocol/compliance.spthy'}
        self.assertIn('transparent pairs containing fresh r', active['L33-L42']['reason'])
        self.assertIn('no KeyInIMT premise', active['L126-L133']['reason'])
        self.assertIn('prior honest generation is a trace restriction assumed', active['L145-L149']['reason'])
        self.assertIn('neither forbids replay', active['L164-L168']['reason'])
        self.assertIn('rules allocate distinct fresh atoms', active['L170-L172']['reason'])
        self.assertIn('never reads DemCipher', closed['L75-L83']['reason'])
        self.assertIn('event label,not native', closed['L97-L100']['reason'])
        self.assertIn('no age bound', closed['L119-L123']['reason'])

    def test_symbolic_status_restrictions_and_labels_cannot_promote_current_crypto_security(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        cases = [('protocol/compliance-active.spthy', m) for m in ['L5-L9','L145-L149','L157-L162','L164-L168','L170-L172']]
        cases += [('protocol/compliance.spthy', m) for m in ['L75-L83','L97-L100','L106-L110','L119-L123']]
        for source, member in cases:
            key = next(k for k, r in reviews.items() if r['selector']['source'] == source and r['selector']['member'] == member)
            original = copy.deepcopy(reviews[key])
            for changes in [dict(status='proved'), dict(evidence=['historical-Tamarin-VERIFIED']),
                            dict(obligation='current:upstream-contract'),
                            dict(reason='Imported ProofSound and DetectionAccepted prove current cryptographic correctness and replay rejection.')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(source=source, member=member, changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        for name in ['COMPLIANCE_ACTIVE_REVIEWS','COMPLIANCE_CLOSED_REVIEWS']:
            original = getattr(coverage, name)
            changed = original[0][:3] + ('0' * 64,) + original[0][4:]
            with patch.object(coverage, name, (changed,) + original[1:]):
                with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_complete_compliance_property_ledger_keeps_research_and_current_contracts_distinct(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        selected = {k: r for k, r in reviews.items() if r['selector']['source'] == 'compliance/soundness-properties.md'}
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        expected = {k for k, r in universe.items() if r.get('source') == 'compliance/soundness-properties.md'}
        self.assertEqual(len(selected), 21);self.assertEqual(set(selected), expected)
        members = {r['selector']['member']: r for r in selected.values()}
        self.assertEqual(members['L20-L20']['applicability'], 'separate_note_reshape_milestone')
        self.assertIn('paired-history delta', members['L15-L15']['reason'])
        self.assertIn('signature predicate injectivity', members['L17-L17']['reason'])
        self.assertIn('same-state replay includingComplete', members['L18-L18']['reason'])
        self.assertIn('needs recertification', members['L21-L21']['reason'])
        self.assertIn('no deployed V20 requirement', members['L22-L22']['reason'])
        self.assertIn('does not prove current Pari zero knowledge', members['L24-L24']['reason'])
        self.assertIn('stronger than extractability alone', members['L26-L26']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for member in ['L9-L9','L15-L15','L17-L17','L20-L20','L21-L21','L24-L24','L26-L26']:
            key = next(k for k, r in selected.items() if r['selector']['member'] == member)
            original = copy.deepcopy(reviews[key])
            for changes in [dict(status='proved'), dict(evidence=['historical-property-status']),
                            dict(obligation='current:upstream-contract'),
                            dict(reason='The historical property label is sufficient proof for current whole Transfer.')]:
                reviews[key] = {**copy.deepcopy(original), **changes}
                with self.subTest(member=member, changes=changes), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
            reviews[key] = original
        for name in ['COMPLIANCE_PROPERTY_REVIEWS','COMPLIANCE_PROPERTY_CIRCUIT_REVIEWS']:
            original = getattr(coverage,name);changed = original[0][:3] + ('0'*64,) + original[0][4:]
            with patch.object(coverage,name,(changed,)+original[1:]):
                with self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_complete_assumption_ledger_review_preserves_current_crypto_model_and_setup_boundaries(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        selected = {k:r for k,r in reviews.items() if r['selector']['source']=='compliance/assumption-ledger.md'}
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        expected={k for k,r in universe.items() if r.get('source')=='compliance/assumption-ledger.md'}
        self.assertEqual(len(selected),49);self.assertEqual(set(selected),expected)
        members={r['selector']['member']:r for r in selected.values()}
        self.assertIn('raw-affine',members['L41-L41']['reason'])
        self.assertIn('nine possible field representatives',members['L44-L44']['reason'])
        self.assertIn('group are algebraically dependent',members['L55-L55']['reason'])
        self.assertIn('does not prove that completeness premise',members['L65-L65']['reason'])
        self.assertIn('toxic waste erasure',members['L67-L67']['reason'])
        self.assertIn('security margin or provenance',members['L70-L70']['reason'])
        self.assertEqual(members['L63-L63']['applicability'],'separate_note_reshape_milestone')
        self.assertEqual(members['L68-L68']['applicability'],'separate_withdrawal_milestone')
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for member in ['L34-L34','L44-L44','L55-L55','L63-L63','L65-L65','L67-L67','L68-L68','L70-L70']:
            key=next(k for k,r in selected.items() if r['selector']['member']==member)
            original=copy.deepcopy(reviews[key])
            for changes in [dict(status='proved'),dict(evidence=['historical-discharged-assumption']),
                            dict(obligation='current:intent'),
                            dict(reason='Old discharged status and parameter checks establish current crypto security.')]:
                reviews[key]={**copy.deepcopy(original),**changes}
                with self.subTest(member=member,changes=changes),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name in ['ASSUMPTION_LEDGER_PROTOCOL_REVIEWS','ASSUMPTION_LEDGER_CIRCUIT_REVIEWS','ASSUMPTION_LEDGER_STATE_REVIEWS']:
            original=getattr(coverage,name);changed=original[0][:3]+('0'*64,)+original[0][4:]
            with patch.object(coverage,name,(changed,)+original[1:]):
                with self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_admission_construction_matrix_reviews_preserve_current_exact_context_and_contracts(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        members={entry[0] for entry in coverage.MATRIX_ADMISSION_CONSTRUCTION_REVIEWS}
        self.assertEqual(members,{'/predicates/'+str(i) for i in [57,58,60,61,62,63,64,66,68,70]})
        selected={k:r for k,r in reviews.items() if r['selector']['source']=='@history/fv-specification-predicate-matrix.json' and r['selector']['member'] in members}
        self.assertEqual(len(selected),10)
        by_member={r['selector']['member']:r for r in selected.values()}
        for member,clause in [(57,'construction-only'),(58,'272-byte'),(60,'private plans are not consensus inputs'),
                              (61,'does not itself compare a re-encoding'),(62,'actual compiled relation shape'),
                              (63,'exact slot coverage,item binding and registry identity'),(64,'64-field'),
                              (66,'one action-shared RK'),(68,'not algebraic generator independence'),
                              (70,'normalizes only anchor')]:
            self.assertIn(clause,by_member['/predicates/'+str(member)]['reason'])
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for changes in [dict(status='proved'),dict(evidence=['historical-proof-verification']),
                            dict(obligation='current:migration-review'),
                            dict(reason='Old external acceptance facts establish current native verifier soundness.')]:
                reviews[key]={**copy.deepcopy(original),**changes}
                with self.subTest(member=original['selector']['member'],changes=changes),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        original=coverage.MATRIX_ADMISSION_CONSTRUCTION_REVIEWS
        for i,entry in enumerate(original):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'MATRIX_ADMISSION_CONSTRUCTION_REVIEWS',original[:i]+(changed,)+original[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_matrix_routing_statement_review_preserves_premises_and_family_exclusions(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        members={e[0] for e in coverage.MATRIX_ROUTING_STATEMENT_REVIEWS}
        self.assertEqual(members,{'/predicates/'+str(i) for i in [9,50,97,98,99,107,109]})
        selected={k:r for k,r in reviews.items() if r['selector']['source']=='@history/fv-specification-predicate-matrix.json' and r['selector']['member'] in members}
        self.assertEqual(len(selected),7)
        by_member={r['selector']['member']:r for r in selected.values()}
        for i,clause in [(9,'min2/max8'),(50,'do not prove entropy'),(97,'64 ordered fields'),
                         (98,'does not prove it is the active configuration'),(99,'affine x/y'),
                         (107,'not integer no-inflation'),(109,'caller-supplied effect limbs')]:
            self.assertIn(clause,by_member['/predicates/'+str(i)]['reason'])
        self.assertEqual(by_member['/predicates/9']['applicability'],'separate_note_reshape_milestone')
        self.assertEqual(by_member['/predicates/109']['applicability'],'separate_withdrawal_milestone')
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-routing-consequence']),
                           dict(applicability='retired_history'),
                           dict(reason='Named semantic segments prove current nonce freshness and active routing.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        original=coverage.MATRIX_ROUTING_STATEMENT_REVIEWS
        for i,entry in enumerate(original):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'MATRIX_ROUTING_STATEMENT_REVIEWS',original[:i]+(changed,)+original[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_admission_surface_reviews_keep_transport_and_capability_scope_open(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        members={e[0] for e in coverage.MATRIX_ADMISSION_SURFACE_REVIEWS}
        self.assertEqual(members,{'/proof_acceptance_surface/production_sinks/'+str(i) for i in range(18)})
        selected={k:r for k,r in reviews.items() if r['selector']['source']=='@history/fv-specification-predicate-matrix.json' and r['selector']['member'] in members}
        self.assertEqual(len(selected),18)
        by_member={r['selector']['member']:r for r in selected.values()}
        prefix='/proof_acceptance_surface/production_sinks/'
        for i,clause in [(0,'entrypoint is absent'),(3,'failed batch'),(6,'Ordinary context'),
                         (8,'may occur before historical success'),(11,'dispatch_query'),
                         (12,'typed rejection versus transport error'),(13,'no grpc.rs'),
                         (15,'NoIndex mode'),(17,'each capability registry ID')]:
            self.assertIn(clause,by_member[prefix+str(i)]['reason'])
        for i,app in [(4,'separate_withdrawal_milestone'),(5,'separate_note_reshape_milestone'),(7,'separate_withdrawal_milestone')]:
            self.assertEqual(by_member[prefix+str(i)]['applicability'],app)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-frontdoor-test']),
                           dict(applicability='retired_history'),
                           dict(reason='Removed transports and sink census prove current invalid-proof rejection.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        original=coverage.MATRIX_ADMISSION_SURFACE_REVIEWS
        for i,entry in enumerate(original):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'MATRIX_ADMISSION_SURFACE_REVIEWS',original[:i]+(changed,)+original[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_runtime_policy_reviews_keep_changed_limits_and_cancellation_explicit(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        members={e[0] for e in coverage.MATRIX_RUNTIME_POLICY_REVIEWS}
        self.assertEqual(members,{'/runtime_policy_contract/policies/'+str(i) for i in range(10)})
        selected={k:r for k,r in reviews.items() if r['selector']['source']=='@history/fv-specification-predicate-matrix.json' and r['selector']['member'] in members}
        self.assertEqual(len(selected),10)
        by_member={r['selector']['member']:r for r in selected.values()}
        for i,clause in [(0,'eight old action variants'),(1,'not measured by the retained_raw_tx_bytes'),
                         (2,'reads SHIELDD_SERVICE_LIMITS'),(3,'seven-family Pari v2'),
                         (4,'does not establish a transitive no-I/O theorem'),(5,'No old six-frontdoor count'),
                         (6,'two Rayon workers'),(7,'cancelled Tokio blocking job'),(8,'uses1800 seconds'),
                         (9,'additionally counts volume nullifiers')]:
            self.assertIn(clause,by_member['/runtime_policy_contract/policies/'+str(i)]['reason'])
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-runtime-policy-receipt']),
                           dict(obligation='current:upstream-contract'),
                           dict(reason='Historical configured bounds and worker draining certify current resource safety.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        original=coverage.MATRIX_RUNTIME_POLICY_REVIEWS
        for i,entry in enumerate(original):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'MATRIX_RUNTIME_POLICY_REVIEWS',original[:i]+(changed,)+original[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_property_dependency_reviews_are_not_composition_or_acceptance_proofs(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        names=['MATRIX_PROPERTY_CIRCUIT_CRYPTO_REVIEWS','MATRIX_PROPERTY_STATE_INTEGRATION_REVIEWS','MATRIX_PROPERTY_PROTOCOL_REVIEWS']
        members={e[0] for name in names for e in getattr(coverage,name)}
        self.assertEqual(members,{'/property_contract/'+str(i) for i in range(25)})
        selected={k:r for k,r in reviews.items() if r['selector']['source']=='@history/fv-specification-predicate-matrix.json' and r['selector']['member'] in members}
        self.assertEqual(len(selected),25)
        by_member={r['selector']['member']:r for r in selected.values()}
        for i,clause in [(2,'algebraic generator independence'),(3,'arbitrary accepted witnesses'),
                         (5,'omits a native decoder success'),(7,'fixed arity alone does not prove'),
                         (12,'honest construction separately'),(16,'do not reject replay alone'),
                         (17,'cannot prove secrecy'),(20,'252/255 widths'),(21,'only VALUE-AMOUNT-128-RANGE'),
                         (24,'distinguish arbitrary accepted facts from honest privacy')]:
            self.assertIn(clause,by_member['/property_contract/'+str(i)]['reason'])
        for i in [22,23]:self.assertEqual(by_member['/property_contract/'+str(i)]['applicability'],'separate_note_reshape_milestone')
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-property-list']),
                           dict(applicability='retired_history'),
                           dict(reason='Property dependency enumeration proves current adversarial acceptance and secrecy.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        for name in names:
            original=getattr(coverage,name)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_retained_statement_frame_bodies_preserve_bounds_and_recorded_axioms(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        sources={'@history/snarkpack/fstar/StatementEncodingProofs.fst':('SNARKPACK_STATEMENT_ENCODING_REVIEWS',72),
                 '@history/snarkpack/fstar/FrameLemmas.fst':('SNARKPACK_FRAME_REVIEWS',12)}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in sources}
        for source,(name,count) in sources.items():
            expected={k:v for k,v in universe.items() if v['source']==source}
            actual={k:r for k,r in selected.items() if r['selector']['source']==source}
            self.assertEqual(len(actual),count)
            self.assertEqual(set(actual),set(expected))
            self.assertEqual({r['selector']['member'] for r in actual.values()},{e[0] for e in getattr(coverage,name)})
        by_name={r['selector']['name']:r for r in selected.values() if r['selector']['historical_kind']=='let'}
        for name,clause in [('lemma_append_len_ok','Int.v len<=2^32-1'),
                           ('wf_input','does not validate version/family'),
                           ('lemma_spec_fields_inj','equal field counts'),
                           ('lemma_encode_statement_injective','spec_statement byte equality'),
                           ('padding_list','trailingzero'),
                           ('lemma_u32_value_frame_inj','recorded Num.impl_u32__to_le_bytes_injective'),
                           ('lemma_lenpref_frame_inj','actual field length')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['historical-hax-proof']),
                           dict(reason='Byte framing and historical injectivity axioms prove current Pari codec refinement.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name,_ in sources.values():
            original=getattr(coverage,name)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_digest_and_family_bodies_keep_preimage_and_changed_route_contracts(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        sources={'@history/snarkpack/fstar/DigestBindingProofs.fst':('SNARKPACK_DIGEST_REVIEWS',12),
                 '@history/snarkpack/fstar/FamilyRoutingProofs.fst':('SNARKPACK_FAMILY_REVIEWS',21)}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in sources}
        for source,(name,count) in sources.items():
            expected={k:v for k,v in universe.items() if v['source']==source}
            actual={k:r for k,r in selected.items() if r['selector']['source']==source}
            self.assertEqual(len(actual),count)
            self.assertEqual(set(actual),set(expected))
            self.assertEqual({r['selector']['member'] for r in actual.values()},{e[0] for e in getattr(coverage,name)})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('lemma_default_srs_id_preimage_injective','SHA digest equality is not a premise'),
                           ('lemma_vk_digest_preimage_injective','both Result_Ok'),
                           ('lemma_statement_digest_preimage_content','does not establish canonicality'),
                           ('lemma_family_route_transfer_total','(7,0,0)'),
                           ('lemma_family_route_rejects_unknown_family','unequal to7,8,10'),
                           ('lemma_family_route_transfer_rejects_cross_subids','either foreign subid nonzero'),
                           ('lemma_family_proto_fields_note_reshape_inverse','{1,2,3,4}'),
                           ('lemma_family_proto_fields_shielded_ics20_withdrawal_inverse','getter equal1')]:
            self.assertIn(clause,by_name[name]['reason'])
        routing=[r for r in selected.values() if 'FamilyRouting' in r['selector']['source']]
        self.assertTrue(all('exactly bytes1,2,3,4,5,6,9' in r['reason'] for r in routing))
        self.assertEqual(sum(r['applicability']=='transfer_shared' for r in routing),9)
        self.assertEqual(sum('note_reshape' in r['applicability'] for r in routing),6)
        self.assertEqual(sum('withdrawal' in r['applicability'] for r in routing),6)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['historical-router-proof']),
                           dict(reason='Preimage identity and old route tuples certify current Pari Registry acceptance.'),
                           dict(applicability='retired_history'),dict(obligation='current:upstream-contract')]:
                if all(original.get(k)==v for k,v in change.items()):
                    continue
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name,_ in sources.values():
            original=getattr(coverage,name)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_preflight_and_machine_support_keep_truth_table_and_codec_boundaries(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        sources={'@history/snarkpack/fstar/PreflightProofs.fst':('SNARKPACK_PREFLIGHT_REVIEWS',5),
                 '@history/snarkpack/fstar/SnarkpackMachineSupport.fst':('SNARKPACK_MACHINE_REVIEWS',18)}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in sources}
        for source,(name,count) in sources.items():
            expected={k:v for k,v in universe.items() if v['source']==source}
            actual={k:r for k,r in selected.items() if r['selector']['source']==source}
            self.assertEqual(len(actual),count)
            self.assertEqual(set(actual),set(expected))
            self.assertEqual({r['selector']['member'] for r in actual.values()},{e[0] for e in getattr(coverage,name)})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('all_checks_ok','does not compute any flag'),
                           ('lemma_preflight_gate_allows_backend_work_iff','supplied flags'),
                           ('lemma_preflight_gate_rejects_if_size_or_digest_missing','after parsing'),
                           ('fstar_hax_bytes_roundtrip_index','within both'),
                           ('u32_to_le_bytes_injective','proved decoder/encoder round trip'),
                           ('u64_from_le_bytes','exactly eight'),
                           ('u32_is_power_of_two','all32 nonzero')]:
            self.assertIn(clause,by_name[name]['reason'])
        support=by_name['@history/snarkpack/fstar/SnarkpackMachineSupport.fst']
        self.assertIn('replaces former assumed Num helpers',support['reason'])
        frames=[r for r in reviews.values() if r['selector']['source']=='@history/snarkpack/fstar/FrameLemmas.fst']
        self.assertTrue(all('injectivity axiom' not in r['reason'] for r in frames))
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-fstar-lane']),
                           dict(reason='The preflight flags and byte model imply all native backend work and codec refinement.'),
                           dict(obligation='current:full-relation')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name,_ in sources.values():
            original=getattr(coverage,name)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_validation_and_wrapper_reviews_preserve_each_conversion_and_offset(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        sources={'@history/snarkpack/fstar/ValidationProofs.fst':('SNARKPACK_VALIDATION_REVIEWS',43),
                 '@history/snarkpack/fstar/WrapperProofs.fst':('SNARKPACK_WRAPPER_REVIEWS',48)}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in sources}
        for source,(name,count) in sources.items():
            expected={k:v for k,v in universe.items() if v['source']==source}
            actual={k:r for k,r in selected.items() if r['selector']['source']==source}
            self.assertEqual(len(actual),count)
            self.assertEqual(set(actual),set(expected))
            self.assertEqual({r['selector']['member'] for r in actual.values()},{e[0] for e in getattr(coverage,name)})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('lemma_validate_counts_rejects_real_gt_padded','real_count>padded_count'),
                           ('lemma_validate_counts_accepts_when_all_guards_pass','checked conversion equality'),
                           ('lemma_validate_row_arity_iff','index+row length<=Int.max_usize'),
                           ('all_arity','True for empty'),
                           ('lemma_check_repeat_suffix_iff','explicit Eq typeclass'),
                           ('wrapper_header_len','header length73'),
                           ('lemma_wrapper_roundtrip','cap=None'),
                           ('lemma_wrapper_decode_success_exposes_exact_inner','Successful decode is a premise'),
                           ('lemma_wrapper_rejects_oversize_before_parsing','length>supplied max'),
                           ('lemma_wrapper_digest_mismatch_before_range','different32-byte digests')]:
            self.assertIn(clause,by_name[name]['reason'])
        branch={r['selector']['member']:r for r in selected.values() if 'ValidationProofs' in r['selector']['source']}
        self.assertIn('error branch is False',branch['L248-L248']['reason'])
        self.assertIn('both sides false',branch['L330-L330']['reason'])
        self.assertIn('allow an empty padding suffix',branch['L267-L279']['reason'])
        self.assertNotEqual(coverage.identity(branch['L227-L227']['selector']),coverage.identity(branch['L291-L291']['selector']))
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] and r['obligation']=='current:admission' for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-wrapper-lane']),
                           dict(reason='Historical padding and wrapper range proofs establish current native Pari acceptance.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name,_ in sources.values():
            original=getattr(coverage,name)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_challenge_and_statement_extraction_keep_byte_and_crypto_contracts_separate(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        sources={'@history/snarkpack/fstar/ChallengePreimageProofs.fst':('SNARKPACK_CHALLENGE_REVIEWS',26),
                 'shielded-pool/hax-extraction-boundary.md':('STATEMENT_HAX_BOUNDARY_REVIEWS',4)}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in sources}
        for source,(name,count) in sources.items():
            expected={k:v for k,v in universe.items() if v['source']==source}
            actual={k:r for k,r in selected.items() if r['selector']['source']==source}
            self.assertEqual(len(actual),count)
            self.assertEqual(set(actual),set(expected))
            self.assertEqual({r['selector']['member'] for r in actual.values()},{e[0] for e in getattr(coverage,name)})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('label_len','Later layout/injectivity proofs require'),
                           ('lemma_challenge_context_bytes_injective','representation injectivity'),
                           ('lemma_challenge_preimage_layout','total domain+4+label+32+8+messages<=Int.max_usize'),
                           ('lemma_challenge_spec_injective','Equality of SHA outputs is not a premise'),
                           ('lemma_challenge_preimage_injective','both full preimage lengths fit usize')]:
            self.assertIn(clause,by_name[name]['reason'])
        boundary={r['selector']['member']:r for r in selected.values() if r['selector']['source']=='shielded-pool/hax-extraction-boundary.md'}
        self.assertIn('not a mechanized Go theorem',boundary['L6-L11']['reason'])
        self.assertIn('every lower-level',boundary['L12-L14']['reason'])
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['historical-challenge-kernel']),
                           dict(reason='Injective challenge bytes imply collision-free hashes and current native Pari soundness.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name,_ in sources.values():
            original=getattr(coverage,name)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_hax_boundary_metadata_retains_primitive_copy_and_caller_assumptions(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='@history/snarkpack/hax-extraction-boundary.md'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source}
        self.assertEqual(len(selected),116)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source})
        self.assertEqual({r['selector']['member'] for r in selected.values()},{e[0] for e in coverage.SNARKPACK_HAX_BOUNDARY_REVIEWS})
        by_member={r['selector']['member']:r for r in selected.values()}
        for member,clause in [('L18-L18','caller must already validate'),
                             ('L19-L19','cfg(hax) structural helper traversal'),
                             ('L44-L44','compile-time labels'),
                             ('L58-L58','no cryptographic meaning to GT'),
                             ('L100-L108','six limbs'),
                             ('L109-L122','Aeneas revision could not be identified'),
                             ('L156-L156','OrderedMsmConformance'),
                             ('L160-L160','inner product,left,right,target'),
                             ('L166-L166','r=1 uses row count'),
                             ('L175-L175','empty/nonsingleton rejects'),
                             ('L182-L182','does not model timing'),
                             ('L188-L188','MAX rejection fails closed'),
                             ('L206-L206','replaces earlier assumptions'),
                             ('L220-L225','Identity alone grants no semantic correspondence')]:
            self.assertIn(clause,by_member[member]['reason'])
        self.assertEqual(by_member['L40-L40']['applicability'],'separate_note_reshape_milestone')
        self.assertEqual(by_member['L41-L41']['applicability'],'separate_withdrawal_milestone')
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-proved-model-label']),
                           dict(reason='Pinned extraction metadata and adapter hashes prove current backend soundness.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        original=coverage.SNARKPACK_HAX_BOUNDARY_REVIEWS
        for i,entry in enumerate(original):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'SNARKPACK_HAX_BOUNDARY_REVIEWS',original[:i]+(changed,)+original[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_compliance_model_and_threat_reviews_keep_current_wire_and_live_dleq(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        sources={'compliance/symbolic-model-design.md':('COMPLIANCE_MODEL_DESIGN_REVIEWS',39),
                 'compliance/threat-model.md':('COMPLIANCE_THREAT_MODEL_REVIEWS',29)}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in sources}
        for source,(name,count) in sources.items():
            expected={k:v for k,v in universe.items() if v['source']==source}
            actual={k:r for k,r in selected.items() if r['selector']['source']==source}
            self.assertEqual(len(actual),count)
            self.assertEqual(set(actual),set(expected))
            self.assertEqual({r['selector']['member'] for r in actual.values()},{e[0] for e in getattr(coverage,name)})
        by_source_member={(r['selector']['source'],r['selector']['member']):r for r in selected.values()}
        for source,member,clause in [('compliance/symbolic-model-design.md','L46-L46','asset,salt,flag,reserved0'),
                                     ('compliance/symbolic-model-design.md','L49-L49','Current272-byte record'),
                                     ('compliance/symbolic-model-design.md','L50-L50','do not prove entropy'),
                                     ('compliance/symbolic-model-design.md','L52-L52','EvidenceValid/DecryptFailed'),
                                     ('compliance/symbolic-model-design.md','L62-L62','permanent spends includingdummy/fee'),
                                     ('compliance/threat-model.md','L15-L15','current835/272 bytes'),
                                     ('compliance/threat-model.md','L20-L25','paired current or authorized historical'),
                                     ('compliance/threat-model.md','L57-L62','64 bytes,not48'),
                                     ('compliance/threat-model.md','L98-L100','IssuerDhEvidence v1/v2')]:
            self.assertIn(clause,by_source_member[source,member]['reason'])
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['V16-certification']),
                           dict(reason='Old threat-model labels prove current secrecy and retire all deployed DLEQ obligations.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name,_ in sources.values():
            original=getattr(coverage,name)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_orbis_model_does_not_promote_structural_single_binding_to_crypto(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='alloy/orbis-authorization.als'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source}
        self.assertEqual(len(selected),20)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source})
        self.assertEqual({r['selector']['member'] for r in selected.values()},{e[0] for e in coverage.ORBIS_AUTHORIZATION_ALLOY_REVIEWS})
        by_member={r['selector']['member']:r for r in selected.values()}
        for member,clause in [('L1-L26','committee/DKG/quorum omitted'),
                             ('L38-L40','boundTo:one Issuer assumes'),
                             ('L43-L46','not group or DLEQ soundness'),
                             ('L48-L51','global unique issuer-key ownership'),
                             ('L64-L67','already imposed'),
                             ('L68-L69','not an intended semantic negative control'),
                             ('L77-L77','not be a genuine accepted transaction')]:
            self.assertIn(clause,by_member[member]['reason'])
        self.assertTrue(all('module is absent' in r['reason'] for r in selected.values()))
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['scope10-pre-check']),
                           dict(reason='One bound issuer in the Alloy signature proves native PRE cryptographic binding.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        original=coverage.ORBIS_AUTHORIZATION_ALLOY_REVIEWS
        for i,entry in enumerate(original):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'ORBIS_AUTHORIZATION_ALLOY_REVIEWS',original[:i]+(changed,)+original[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_external_map_reviews_keep_native_prerequisites_and_crypto_scope_open(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/external-check-map.md'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source}
        self.assertEqual(len(selected),31)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source and v['kind']=='migration-member'})
        members=coverage.EXTERNAL_MAP_CIRCUIT_REVIEWS+coverage.EXTERNAL_MAP_STATE_REVIEWS
        self.assertEqual({r['selector']['member'] for r in selected.values()},{e[0] for e in members})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('EXT-FIXED-SHAPE','one action RK/auth signature'),
                           ('EXT-PROOF-FAMILY','no leftover capabilities'),
                           ('EXT-BINDING-SIGNATURE','unknown-generator-log/signature assumptions'),
                           ('EXT-NULLIFIER-STATE','all2 slots includingdummy and fee'),
                           ('EXT-ASSET-ROOT','authorized paired historical'),
                           ('EXT-TIMESTAMP-FRESHNESS','current +/-1800'),
                           ('EXT-TRANSFER-NONCE-PRIVACY','not consensus accepted'),
                           ('EXT-PUBLIC-INPUT-HASH-CRYPTO','not globally injective')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertEqual(sum(r['applicability']=='separate_withdrawal_milestone' for r in selected.values()),9)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-composed-runtime']),
                           dict(reason='External acceptance facts and hash identity establish current full Transfer soundness.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name in ['EXTERNAL_MAP_CIRCUIT_REVIEWS','EXTERNAL_MAP_STATE_REVIEWS']:
            original=getattr(coverage,name)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_certified_ledger_reviews_do_not_adopt_old_certification_or_conservation(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/certified-circuit-obligation-ledger.md'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source}
        self.assertEqual(len(selected),61)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source})
        self.assertEqual({r['selector']['member'] for r in selected.values()},{e[0] for e in coverage.CERTIFIED_OBLIGATION_LEDGER_REVIEWS})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('CERT-PROOF-CANONICAL-ENCODING','no reserialize-equality check'),
                           ('CERT-SPEND-AUTH','one current action'),
                           ('CERT-TX-BINDING','not integer conservation'),
                           ('CONSTRUCTION-PLAN-PROJECTION','cannot be assumed to originate'),
                           ('T-ASSET-REGISTRY','paired historical snapshot'),
                           ('T-COMPLIANCE-TRANSCRIPT','Native835/272-byte codecs'),
                           ('T-CONSERVATION','not an opaque no-inflation premise'),
                           ('T-TIMESTAMP','current inclusive +/-1800'),
                           ('T-STATEMENT','current64 ordered fields')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertEqual(sum(r['applicability']=='transfer_shared' for r in selected.values()),34)
        self.assertEqual(sum('note_reshape' in r['applicability'] for r in selected.values()),13)
        self.assertEqual(sum('withdrawal' in r['applicability'] for r in selected.values()),14)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['certified-ledger-label']),
                           dict(reason='The certified checklist and binding-signature acceptance prove current conservation and runtime effects.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        original=coverage.CERTIFIED_OBLIGATION_LEDGER_REVIEWS
        for i,entry in enumerate(original):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'CERTIFIED_OBLIGATION_LEDGER_REVIEWS',original[:i]+(changed,)+original[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_findings_reviews_keep_old_resolution_separate_from_current_qualification(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/circuit-soundness-findings.md'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source}
        self.assertEqual(len(selected),77)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source})
        members=coverage.CIRCUIT_FINDING_REVIEWS+coverage.STATE_FINDING_REVIEWS
        self.assertEqual({r['selector']['member'] for r in selected.values()},{e[0] for e in members})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [
            ('ZK-FIND-DUMMY-NULLIFIER-DOMAIN','mathematically disjoint finite hash ranges'),
            ('ZK-FIND-PROOF-ENCODING-CANONICAL','no reserialize equality check'),
            ('ZK-FIND-TRANSFER-FALSE-CERTIFICATION','T0-T7 stay open'),
            ('ZK-FIND-HASH-BINDING-TRUST-BOUNDARY','Finite hashes are not globally injective'),
            ('ZK-FIND-IVK-ZERO-TRANSMISSION-IDENTITY','collide after modr without raw hash collision'),
            ('ZK-FIND-TRANSFER-DETECTION-ASSET-FLAG-ALIAS','current source is asset,salt,flag,reserved0'),
            ('ZK-FIND-FV-MUTATION-EVIDENCE-MASKING','collateral hash failure is no negative control'),
            ('ZK-FIND-FV-ADDRESS-PACKING-VISIBILITY','current255-bit circuit-field/252-bit scalar'),
            ('ZK-FIND-FV-SETUP-PROVENANCE-OVERCLAIM','coherence is not setup derivation or toxic-waste erasure'),
            ('ZK-FIND-CONSENSUS-ADMISSION-RESOURCE-BOUNDS','7 Pari families/Sequential dispatch'),
            ('ZK-FIND-ASYNC-WORKER-LIFETIME','distinct from cancellation'),
            ('ZK-FIND-STATELESS-CACHE-IDENTITY-AND-BOUNDS','Limits4096/96KiB/64MiB count raw bytes only'),
            ('ZK-FIND-CONSENSUS-DIAGNOSTIC-IO','not a transitive no-I/O theorem')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertEqual(sum(r['applicability']=='transfer_shared' for r in selected.values()),62)
        self.assertEqual(sum('note_reshape' in r['applicability'] for r in selected.values()),1)
        self.assertEqual(sum('withdrawal' in r['applicability'] for r in selected.values()),14)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['historical-resolved-label']),
                           dict(reason='The old resolved finding proves current Transfer qualification.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name in ['CIRCUIT_FINDING_REVIEWS','STATE_FINDING_REVIEWS']:
            original=getattr(coverage,name)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_consumer_contracts_preserve_related_key_nonce_and_changed_dleq_boundaries(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        packets={
            '@history/decaf/protocol-contracts.md':('CONSUMER_PROTOCOL_REVIEWS',17),
            '@history/decaf/nonce-contracts.md':('CONSUMER_NONCE_REVIEWS',15),
            '@history/dleq/README.md':('DLEQ_README_REVIEWS',21),
            '@history/decaf/obligations.json':('DECAF_OBLIGATION_REVIEWS',25)}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in packets}
        self.assertEqual(len(selected),78)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source'] in packets})
        by_source={source:{r['selector']['member']:r for r in selected.values()
                          if r['selector']['source']==source} for source in packets}
        for source,(constant,count) in packets.items():
            self.assertEqual(len(by_source[source]),count)
            self.assertEqual(set(by_source[source]),{e[0] for e in getattr(coverage,constant)})
        for source,member,clause in [
            ('@history/decaf/protocol-contracts.md','L15-L23','one circuit alpha'),
            ('@history/decaf/protocol-contracts.md','L61-L66','bare DH provides no peer authentication'),
            ('@history/decaf/protocol-contracts.md','L85-L87','distinct secrets'),
            ('@history/decaf/nonce-contracts.md','L13-L24','failed insertion can mutate expired entries'),
            ('@history/decaf/nonce-contracts.md','L36-L40','Consume does not check TTL'),
            ('@history/decaf/nonce-contracts.md','L56-L64','one-use cannot depend on cleanup'),
            ('@history/decaf/nonce-contracts.md','L73-L78','also borrow SigningNonces'),
            ('@history/dleq/README.md','L23-L23','no uniform-Fin challenge'),
            ('@history/dleq/README.md','L44-L53','verify_dleq alone checks only two equations'),
            ('@history/dleq/README.md','L67-L69','version2'),
            ('@history/decaf/obligations.json','/profiles','vendored Decaf exists'),
            ('@history/decaf/obligations.json','/families/4','zero-denominator branch'),
            ('@history/decaf/obligations.json','/replays','old partial logs do not qualify')]:
            self.assertIn(clause,by_source[source][member]['reason'])
        self.assertTrue(all(r['applicability']=='transfer_shared' and r['status']=='open'
                            and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-dleq-discharge']),
                           dict(reason='The old library and nonce contracts certify all current cryptographic consumers.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(source=original['selector']['source'],member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for constant,_ in packets.values():
            original=getattr(coverage,constant)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,constant,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(constant=constant,member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_statement_map_and_compliance_findings_keep_current_schema_and_live_issuer_api(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        packets={
            'shielded-pool/statement-field-map.md':('LEGACY_STATEMENT_MAP_REVIEWS',15),
            'compliance/compliance-soundness-findings.md':('COMPLIANCE_FINDING_REVIEWS',12)}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in packets}
        self.assertEqual(len(selected),27)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source'] in packets})
        by_source={source:{r['selector']['member']:r for r in selected.values()
                          if r['selector']['source']==source} for source in packets}
        for source,(constant,count) in packets.items():
            self.assertEqual(len(by_source[source]),count)
            self.assertEqual(set(by_source[source]),{e[0] for e in getattr(coverage,constant)})
        for source,member,clause in [
            ('shielded-pool/statement-field-map.md','L9-L9','current index2'),
            ('shielded-pool/statement-field-map.md','L10-L10','note/recovery'),
            ('shielded-pool/statement-field-map.md','L12-L12','recent-position floor that is absent'),
            ('shielded-pool/statement-field-map.md','L13-L13','one shared RK0/1'),
            ('shielded-pool/statement-field-map.md','L15-L15','Transfer order differs from Published.fields'),
            ('shielded-pool/statement-field-map.md','L17-L17','audit_epoch55'),
            ('compliance/compliance-soundness-findings.md','L5-L5','intentional issuer evidence exports authorized sharedpoint'),
            ('compliance/compliance-soundness-findings.md','L6-L6','do not invent an observed fail-closed API error'),
            ('compliance/compliance-soundness-findings.md','L10-L10','Current issuer Jubjub DLEQ is live'),
            ('compliance/compliance-soundness-findings.md','L11-L11','Distribution/bias and current reduction remain explicit'),
            ('compliance/compliance-soundness-findings.md','L12-L12','not only native constructor'),
            ('compliance/compliance-soundness-findings.md','L13-L13','asset,salt,Booleanflag,reservedzero')]:
            self.assertIn(clause,by_source[source][member]['reason'])
        self.assertEqual(sum(r['applicability']=='transfer_shared' for r in selected.values()),24)
        self.assertEqual(sum('note_reshape' in r['applicability'] for r in selected.values()),1)
        self.assertEqual(sum('withdrawal' in r['applicability'] for r in selected.values()),2)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-composed-or-resolved-label']),
                           dict(reason='The old schema and removed DLEQ fields prove current ciphertext and issuer API soundness.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(source=original['selector']['source'],member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for constant,_ in packets.values():
            original=getattr(coverage,constant)
            for i,entry in enumerate(original):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,constant,original[:i]+(changed,)+original[i+1:]):
                    with self.subTest(constant=constant,member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_range_requirement_reviews_preserve_exact_metadata_and_changed_volume_contract(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/fv-specification-requirements.json'
        members=coverage.REQUIREMENT_RANGE_SELECTOR_REVIEWS
        selectors={(e[0],e[2]) for e in members}
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and (r['selector']['member'],r['selector']['name']) in selectors}
        self.assertEqual(len(selected),34)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source
                         and v['kind']=='migration-member' and (v['member'],v['name']) in selectors})
        by_name={r['selector']['name']:r for r in selected.values()
                 if r['selector']['historical_kind']=='statement'}
        self.assertEqual(len(by_name),17)
        for name,clause in [
            ('ASSET-REGISTRY-GAP-ORDERING','two limbs127/128'),
            ('CIR-SELECTOR-BOOLEAN','one optionalsecond Transfer slot with firstreal'),
            ('COMPLIANCE-THRESHOLD-FLAG','creator may choose flagged padding'),
            ('FIELD-AUTH-RANDOMIZER-RANGE','one shared action scalar canonical'),
            ('FIELD-BALANCE-BLINDING-RANGE','blindingrange does not imply integer conservation'),
            ('FIELD-USER-DERIVATION-RANGE','removed from current complianceleaf'),
            ('FIELD-USER-POSITION-RANGE','unconditionally decomposed'),
            ('VALUE-AMOUNT-128-RANGE','sums require129bits'),
            ('VALUE-CONSERVATION','Unknowngeneratorlog/signature computational contracts are separate'),
            ('VALUE-THRESHOLD-128-RANGE','use_real implies inclusive<=daily_limit')]:
            self.assertIn(clause,by_name[name]['reason'])
        requirements=[r for r in selected.values() if r['selector']['historical_kind']=='requirement']
        self.assertEqual(len(requirements),17)
        self.assertTrue(all('placement/profile/branch/binding/disclosure/trace_arguments' in r['reason']
                            for r in requirements))
        self.assertTrue(all(r['applicability']=='transfer_shared' and r['status']=='open'
                            and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-predicate-specific-receipt']),
                           dict(reason='The old threshold and 251-bit ranges prove current volume and conservation.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for i,entry in enumerate(members):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'REQUIREMENT_RANGE_SELECTOR_REVIEWS',members[:i]+(changed,)+members[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_registry_requirements_preserve_nested_audit_hash_and_unconditional_constraints(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/fv-specification-requirements.json'
        members=coverage.REQUIREMENT_REGISTRY_COMPLIANCE_REVIEWS
        selectors={(e[0],e[2]) for e in members}
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and (r['selector']['member'],r['selector']['name']) in selectors}
        self.assertEqual(len(selected),30)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source
                         and v['kind']=='migration-member' and (v['member'],v['name']) in selectors})
        by_name={r['selector']['name']:r for r in selected.values()
                 if r['selector']['historical_kind']=='statement'}
        self.assertEqual(len(by_name),15)
        for name,clause in [
            ('ASSET-LEAF-HASH','AuditKeys hash is now nested into ring'),
            ('ASSET-PARAMETERS-HASH','affineDK.x/y,daily_limit,routepolicy'),
            ('ASSET-POLICY-KEY-ENCODING','Sentinel leaf keys mayidentity'),
            ('ASSET-REGISTRY-MEMBERSHIP','unconditionally authenticated'),
            ('ASSET-RING-HASH','distinct-role guards'),
            ('COMPLIANCE-POLICY-SELECTION','without requiring sentinel leaf itself nonidentity'),
            ('COMPLIANCE-SHARED-SECRET-SELECTION','registered AuditKeys.payload otherwise'),
            ('DEC-ACK-DERIVATION','replacedalgorithm does not retire live ownership/RNK contracts'),
            ('USER-COMPLIANCE-LEAF-HASH','nine affineaddress4'),
            ('USER-COMPLIANCE-MEMBERSHIP-GATE','constraints are unconditional'),
            ('USER-LEAF-CANONICAL-DERIVATION-BINDING','no opaque desired canonicalderivation premise')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertEqual(sum(r['selector']['historical_kind']=='requirement' for r in selected.values()),15)
        self.assertTrue(all(r['applicability']=='transfer_shared' and r['status']=='open'
                            and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-five-field-leaf-proof']),
                           dict(reason='The old leaf hash and ACK proofs certify current registry and RNK.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for i,entry in enumerate(members):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'REQUIREMENT_REGISTRY_COMPLIANCE_REVIEWS',members[:i]+(changed,)+members[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_group_requirement_reviews_do_not_inherit_quotient_or_real_only_scope(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/fv-specification-requirements.json'
        members=coverage.REQUIREMENT_GROUP_CODEC_REVIEWS
        selectors={(e[0],e[2]) for e in members}
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and (r['selector']['member'],r['selector']['name']) in selectors}
        self.assertEqual(len(selected),36)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source
                         and v['kind']=='migration-member' and (v['member'],v['name']) in selectors})
        by_name={r['selector']['name']:r for r in selected.values()
                 if r['selector']['historical_kind']=='statement'}
        self.assertEqual(len(by_name),18)
        for name,clause in [
            ('ADDRESS-CANONICAL-PACKING','three31byte limbs248/248/16bits'),
            ('DEC-AUTHORIZATION-KEY-ENCODING','curve equation alone does not exclude torsion'),
            ('DEC-BALANCE-COMMITMENT-DERIVATION','actionnet maynonzero'),
            ('DEC-BALANCE-COMMITMENT-ENCODING','statementtwo affinebalance coordinates'),
            ('DEC-EPHEMERAL-PUBLIC-KEY-DERIVATION','fixed126window execution'),
            ('DEC-INCOMING-VIEWING-KEY-DERIVATION','q8 lastbound preventing fieldwrap'),
            ('DEC-INCOMING-VIEWING-KEY-NONZERO','raw hash nonzero does not imply reduced remainder nonzero'),
            ('DEC-RANDOMIZED-VERIFICATION-KEY-NONIDENTITY','External_acceptance/formal_facts metadata'),
            ('DEC-SPEND-RK-DERIVATION','unconditional single action'),
            ('DEC-TRANSMISSION-KEY-DERIVATION','does not prove receiver walletsecret knowledge')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertEqual(sum(r['selector']['historical_kind']=='requirement' for r in selected.values()),18)
        self.assertTrue(all(r['applicability']=='transfer_shared' and r['status']=='open'
                            and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-decaf-quotient-proof']),
                           dict(reason='The old Decaf key derivation proofs qualify all current Jubjub ownership.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for i,entry in enumerate(members):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'REQUIREMENT_GROUP_CODEC_REVIEWS',members[:i]+(changed,)+members[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_note_requirement_reviews_preserve_recovery_unconditional_rows_and_committed_input(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/fv-specification-requirements.json'
        members=coverage.REQUIREMENT_NOTE_ROUTING_REVIEWS
        selectors={(e[0],e[2]) for e in members}
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and (r['selector']['member'],r['selector']['name']) in selectors}
        self.assertEqual(len(selected),30)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source
                         and v['kind']=='migration-member' and (v['member'],v['name']) in selectors})
        by_name={r['selector']['name']:r for r in selected.values()
                 if r['selector']['historical_kind']=='statement'}
        self.assertEqual(len(by_name),15)
        for name,clause in [
            ('CIR-DUMMY-ORDER-COUNT','not a Transfer arity theorem'),
            ('DUMMY-NULLIFIER-DOMAIN-BINDING','not disjoint finite outputranges'),
            ('DUMMY-SLOT-POSITION-BINDING','witness-suppliedslot'),
            ('NOTE-OUTPUT-COMMITMENT','Both outputs bind recovery capsules'),
            ('NOTE-OUTPUT-OWNER-BINDING','cannot be interchanged'),
            ('NOTE-SPEND-COMMITMENT','only optionalreal root equality is gated'),
            ('NOTE-SPEND-NULLIFIER-DERIVATION','regulated effectiveNK'),
            ('PUBLIC-STATEMENT-BINDING','Pari additionally commits witnessinput'),
            ('ROUTING-TAG-DERIVATION','transmission.x/y instead ofoldcompressedfield'),
            ('SCT-SPEND-MEMBERSHIP','same48bitposition for realNF androot')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertEqual(sum(r['applicability']=='transfer_shared' for r in selected.values()),28)
        self.assertEqual(sum('note_reshape' in r['applicability'] for r in selected.values()),2)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-notehash-proof']),
                           dict(reason='The historical note and sole-public-input statements certify current Transfer.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for i,entry in enumerate(members):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'REQUIREMENT_NOTE_ROUTING_REVIEWS',members[:i]+(changed,)+members[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_acceptance_requirement_reviews_keep_source_and_crypto_assumptions_explicit(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/fv-specification-requirements.json'
        constants=['REQUIREMENT_ACCEPTANCE_CIRCUIT_CRYPTO_REVIEWS',
                   'REQUIREMENT_ACCEPTANCE_STATE_INTEGRATION_REVIEWS']
        members=tuple(e for name in constants for e in getattr(coverage,name))
        selectors={(e[0],e[2]) for e in members}
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and (r['selector']['member'],r['selector']['name']) in selectors}
        self.assertEqual(len(selected),66)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source
                         and v['kind']=='migration-member' and (v['member'],v['name']) in selectors})
        self.assertEqual(sum(r['selector']['owner']=='state-integration' for r in selected.values()),56)
        by_name={r['selector']['name']:r for r in selected.values()
                 if r['selector']['historical_kind']=='statement'}
        self.assertEqual(len(by_name),33)
        for name,clause in [
            ('COMPLIANCE-ADDRESS-ENCRYPTION','Seed=c2-hash(selectedDH)'),
            ('EXT-ASSET-ANCHOR-CURRENT','authorized paired user+asset historicalsnapshots'),
            ('EXT-HONEST-COMPLIANCE-NONCE','Consensus accepts adversarial witnesses'),
            ('EXT-NULLIFIER-ATOMIC-TRANSITION','beforewrites'),
            ('EXT-NULLIFIER-FRESHNESS','permanent spendNF table'),
            ('EXT-NULLIFIER-TX-UNIQUENESS','no opaque completeenvelope desiredpremise'),
            ('EXT-PROOF-CANONICAL-ENCODING','Envelope doesnot reserializecompare'),
            ('EXT-PROOF-FAMILY-KEY-SELECTION','Registryidentity,item,orderedbody+fee slots'),
            ('EXT-PROOF-VERIFICATION','namedupstreamcrypto assumptions'),
            ('EXT-TIMESTAMP-FRESHNESS','+/-1800 notold +/-3600'),
            ('EXT-TRANSACTION-BINDING-SIGNATURE','not opaquezero-net/no-inflation premise'),
            ('EXT-TRANSACTION-EFFECTS-ATOMICITY','Abstractproof/source guards arenot Rust refinement')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertEqual(sum(r['selector']['historical_kind']=='requirement' for r in selected.values()),33)
        self.assertTrue(all(r['applicability']=='transfer_shared' and r['status']=='open'
                            and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-external-facts']),
                           dict(reason='Assumed external acceptance establishes current native transaction conservation and rollback.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name in constants:
            entries=getattr(coverage,name)
            for i,entry in enumerate(entries):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,entries[:i]+(changed,)+entries[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_withdrawal_requirements_keep_external_preconditions_and_fingerprint_bodies_open(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/fv-specification-requirements.json'
        constants=['REQUIREMENT_WITHDRAWAL_CIRCUIT_CRYPTO_REVIEWS',
                   'REQUIREMENT_WITHDRAWAL_STATE_INTEGRATION_REVIEWS']
        members=tuple(e for name in constants for e in getattr(coverage,name))
        selectors={(e[0],e[2]) for e in members}
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and (r['selector']['member'],r['selector']['name']) in selectors}
        self.assertEqual(len(selected),26)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source
                         and v['kind']=='migration-member' and (v['member'],v['name']) in selectors})
        by_name={r['selector']['name']:r for r in selected.values()
                 if r['selector']['historical_kind']=='statement'}
        self.assertEqual(len(by_name),12)
        for name,clause in [
            ('EXT-WITHDRAWAL-ACTION-ATOMICITY','supplied complete common/Withdrawal effect envelopes'),
            ('EXT-WITHDRAWAL-CHECKED-TOKEN-FRESH','immediate pre-mutation'),
            ('EXT-WITHDRAWAL-PAYLOAD-VALID','rejects deprecated/noncanonical forms'),
            ('EXT-WITHDRAWAL-STATE-TRANSITION','permits equal arbitrary remainder effects'),
            ('EXT-WITHDRAWAL-TIMEOUTS-FUTURE','must both strictly precede'),
            ('WITHDRAWAL-INTENT-FIELD-BINDING','byte chunk provenance external')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertEqual(sum(r['applicability']=='separate_withdrawal_milestone' for r in selected.values()),24)
        self.assertEqual(sum(r['applicability']=='transfer_shared' for r in selected.values()),2)
        # The arrays were reviewed as metadata; their source bodies and results remain open.
        remaining={v['member'] for k,v in universe.items() if v['source']==source
                   and v['kind']=='migration-member' and k not in reviews}
        self.assertEqual(remaining,set())
        fingerprints={r['selector']['member']:r for r in reviews.values()
                      if r['selector']['source']==source
                      and r['selector']['member'] in
                      {'/lean_declaration_fingerprints','/test_source_fingerprints'}}
        self.assertEqual(set(fingerprints),{'/lean_declaration_fingerprints','/test_source_fingerprints'})
        self.assertTrue(all(r['review']=='complete_fingerprint_array_metadata_reviewed_applicability_only'
                            and r['status']=='open' and r['evidence']==[]
                            for r in fingerprints.values()))
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-two-chain-receipt']),
                           dict(reason='The historical Withdrawal preconditions qualify current Transfer and all fingerprints.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for name in constants:
            entries=getattr(coverage,name)
            for i,entry in enumerate(entries):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,name,entries[:i]+(changed,)+entries[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_manifest_metadata_and_scope_markers_remain_identity_and_assumption_inventory(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        constants=['SNARKPACK_MANIFEST_METADATA_REVIEWS','COMPLIANCE_SCOPE_REVIEW']
        members={entry[0] for name in constants for entry in getattr(coverage,name)}
        sources={'@history/snarkpack/verification-manifest.json','@history/compliance-soundness-scope.txt'}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in sources and r['selector']['member'] in members}
        self.assertEqual(len(selected),11)
        by_member={r['selector']['member']:r for r in selected.values()}
        for member,clause in [('/fstar_checker_evidence','records identity only'),
                              ('/deployed_srs_evidence','not current v2 registry status'),
                              ('/fstar_modules','do not falsely classify its definitions as axioms'),
                              ('/allowed_axioms','A list is no axiom audit'),
                              ('/spec_roots','specification independence only'),
                              ('L1-L29','source presence only'),
                              ('L1-L29','bounded embedding is not hash injectivity'),
                              ('/statement_binding_evidence','five external assumed rows'),
                              ('/audit_modules','629 required-root entries'),
                              ('/audit_modules','declared expected capstones total801'),
                              ('/audit_modules','no cited theorem-body/axiom re-audit is claimed')]:
            self.assertIn(clause,by_member[member]['reason'])
        pending={v['member'] for k,v in universe.items() if v['source']=='@history/snarkpack/verification-manifest.json' and k not in reviews}
        self.assertEqual(pending,set())
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['fixed-string-match']),
                           dict(reason='The old artifact SHA and source markers certify current Transfer.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for constant in constants:
            entries=getattr(coverage,constant)
            for i,entry in enumerate(entries):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,constant,entries[:i]+(changed,)+entries[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_manifest_claim_records_do_not_promote_partial_correctness_or_fork_bounds(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='@history/snarkpack/verification-manifest.json'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and r['selector']['member'].startswith('/claims/')}
        self.assertEqual(len(selected),49)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source and v['member'].startswith('/claims/')})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('FULL-ADAPTIVE-END-TO-END-FV','does not prove prover termination'),
                            ('FULL-ADAPTIVE-END-TO-END-FV','not invalid-acceptance probability directly'),
                            ('FULL-ADAPTIVE-END-TO-END-FV','no inverted acceptance/numerical level'),
                            ('DEPLOYED-SRS-SOUNDNESS','Record is open with UNPROVED root'),
                            ('SCALAR-CACHE-AWARE-REPLACEMENT','native proof cache/state authorization is a different contract'),
                            ('BUNDLE-LEVEL-COMPOSITION','cache equivalence/distributions/adaptive security explicitly excluded'),
                            ('BOUNDED-CHALLENGE-SAMPLER','scoped tested evidence'),
                            ('COST-PROVER-MILLER','recurrence is not derived from protocol/production source')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertEqual(sum(r['selector']['owner']=='state-integration' for r in selected.values()),3)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[]
                            and 'not independent theorem-body/axiom re-audit' in r['reason'] for r in selected.values()))
        pending=[v for k,v in universe.items() if v['source']==source and k not in reviews]
        self.assertEqual(pending,[])
        self.assertTrue(all(v['historical_kind']=='historical-evidence-metadata' for v in pending))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['historical-proved-label']),
                           dict(reason='Full adaptive FV proves current Transfer total correctness and numerical soundness.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for constant in ['SNARKPACK_MANIFEST_CLAIM_REVIEWS','SNARKPACK_MANIFEST_APPLICATION_REVIEWS']:
            entries=getattr(coverage,constant)
            for i,entry in enumerate(entries):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,constant,entries[:i]+(changed,)+entries[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_manifest_assumptions_preserve_exact_postconditions_and_transport_owners(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='@history/snarkpack/verification-manifest.json'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and r['selector']['member'].startswith('/assumptions/')}
        self.assertEqual(len(selected),27)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source and v['member'].startswith('/assumptions/')})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('KZG-FALSE-OPENING-SECURITY','not a description of current v2 registry'),
                            ('RUST-TOKIO-JOIN-SEMANTICS','does not prove async scheduling, cancellation'),
                            ('RUST-IMMUTABLE-OBSERVED-RESULT-TRANSPORT','Explicitly excludes scheduler/cache/query/probability'),
                            ('ARKWORKS-SHIPPING-EFFECT-INSTALLATION','no acceptance/transcript/cache/query'),
                            ('ARKWORKS-AGGREGATE-PROOF-DECODE','do not prove shipping Rust decoder equation'),
                            ('BLAKE2B-ROM-SECURITY','not uniform replacement'),
                            ('ARKWORKS-VERIFIER-SRS-ID-LOAD','does not establish verifier identity load'),
                            ('WELL-FORMED-PROVING-SRS','does not prove setup relation')]:
            self.assertIn(clause,by_name[name]['reason'])
        for name in ['RUST-TOKIO-JOIN-SEMANTICS','RUST-IMMUTABLE-OBSERVED-RESULT-TRANSPORT']:
            self.assertEqual(by_name[name]['selector']['owner'],'state-integration')
        self.assertEqual(len([v for k,v in universe.items() if v['source']==source and k not in reviews]),0)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['manifest-postcondition']),
                           dict(reason='All historical assumptions are proved for current Commonware.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for constant in ['SNARKPACK_MANIFEST_ASSUMPTION_REVIEWS','SNARKPACK_MANIFEST_TRANSPORT_REVIEWS']:
            entries=getattr(coverage,constant)
            for i,entry in enumerate(entries):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,constant,entries[:i]+(changed,)+entries[i+1:]):
                    with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_snarkpack_operation_reviews_keep_backend_and_effect_order_contracts_live(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='@history/snarkpack/operation-reduction-register.md'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source}
        self.assertEqual(len(selected),40)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source})
        by_member={r['selector']['member']:r for r in selected.values()}
        for member,clause in [('L7-L12','absent formulas are unknown, not zero'),
                              ('L35-L35','prepared-kernel conformance'),
                              ('L38-L38','not a current BLS12-381/codec guarantee'),
                              ('L39-L40','no reserialization-comparison inference'),
                              ('L47-L47','source refinement broke'),
                              ('L50-L50','correlated error changes reduction'),
                              ('L54-L54','canonical routing/cross-key substitution proof'),
                              ('L60-L60','independent falsification oracle only'),
                              ('L62-L62','changed source invalidating old receipts')]:
            self.assertIn(clause,by_member[member]['reason'])
        self.assertTrue(all(r['applicability']=='transfer_shared' and r['status']=='open'
                            and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-verified-optimization']),
                           dict(reason='The vendored backend is completely trusted and old optimization status proves current security.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        entries=coverage.SNARKPACK_OPERATION_REVIEWS
        for i,entry in enumerate(entries):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'SNARKPACK_OPERATION_REVIEWS',entries[:i]+(changed,)+entries[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_phase0_examples_keep_proving_and_configuration_failure_explicit(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        entries = coverage.HISTORICAL_PHASE0_TEST_REVIEWS
        members = {entry[0] for entry in entries}
        selected = {key: review for key, review in reviews.items()
                    if review['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and review['selector']['member'] in members}
        self.assertEqual(len(selected), 3)
        by_member = {r['selector']['member']: r for r in selected.values()}
        for member, clause in [('/artifact_test_contract/tests/257', 'prover_required=false despite calling Prove'),
                               ('/artifact_test_contract/tests/258', 'does not check generator/cofactor/canonical points'),
                               ('/artifact_test_contract/tests/259', 'compiler failure is not a successful cryptographic')]:
            self.assertIn(clause, by_member[member]['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, original in selected.items():
            for change in [dict(status='proved'), dict(evidence=['old-missing-hash-compiler-control']),
                           dict(reason='Missing field-hasher compilation proves current Transfer security.')]:
                reviews[key] = {**copy.deepcopy(original), **change}
                with self.subTest(member=original['selector']['member'], change=change):
                    with self.assertRaisesRegex(security.CheckError, 'applicability review'):
                        self.check()
            reviews[key] = original
        for i, entry in enumerate(entries):
            changed = entry[:3] + ('0' * 64,) + entry[4:]
            with patch.object(coverage, 'HISTORICAL_PHASE0_TEST_REVIEWS', entries[:i] + (changed,) + entries[i + 1:]):
                with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_old_codec_adapter_controls_keep_parse_and_admission_separate(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        entries = coverage.HISTORICAL_CODEC_ADAPTER_TEST_REVIEWS
        members = {entry[0] for entry in entries}
        selected = {key: review for key, review in reviews.items()
                    if review['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and review['selector']['member'] in members}
        self.assertEqual(len(selected), 14)
        by_member = {r['selector']['member']: r for r in selected.values()}
        for member, clause in [('/property_test_contract/tests/29', 'writer copies supplied bytes'),
                               ('/property_test_contract/tests/89', 'differs from current252-bit Jubjub order'),
                               ('/property_test_contract/tests/91', 'outer bounded Vec is already allocated'),
                               ('/property_test_contract/tests/93', 'not all arithmetic no-wrap'),
                               ('/artifact_test_contract/tests/9', 'does not verify the included proof bytes'),
                               ('/artifact_test_contract/tests/10', 'without verifier validation'),
                               ('/artifact_test_contract/tests/37', 'not arbitrary bytes'),
                               ('/artifact_test_contract/tests/70', 'missing-before-cross-family errors')]:
            self.assertIn(clause, by_member[member]['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, original in selected.items():
            for change in [dict(status='proved'), dict(evidence=['historical-abi-test']),
                           dict(reason='Parsing and protobuf round-trip prove current Pari proof/key/claim acceptance.')]:
                reviews[key] = {**copy.deepcopy(original), **change}
                with self.subTest(member=original['selector']['member'], change=change):
                    with self.assertRaisesRegex(security.CheckError, 'applicability review'):
                        self.check()
            reviews[key] = original
        for i, entry in enumerate(entries):
            changed = entry[:3] + ('0' * 64,) + entry[4:]
            with patch.object(coverage, 'HISTORICAL_CODEC_ADAPTER_TEST_REVIEWS', entries[:i] + (changed,) + entries[i + 1:]):
                with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_tct_structure_examples_preserve_height_capacity_and_storage_assumptions(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        entries = coverage.HISTORICAL_TCT_STRUCTURE_REVIEWS
        members = {entry[0] for entry in entries}
        selected = {key: review for key, review in reviews.items()
                    if review['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and review['selector']['member'] in members}
        self.assertEqual(len(selected), 10)
        by_member = {r['selector']['member']: r for r in selected.values()}
        for member, clause in [('/property_test_contract/tests/25', 'only at height1/index0..3'),
                               ('/property_test_contract/tests/40', 'no48-bit exhaustion/monotonicity theorem'),
                               ('/property_test_contract/tests/48', 'finite sparse shape'),
                               ('/property_test_contract/tests/83', 'not rejected overflow insertion'),
                               ('/property_test_contract/tests/256', 'does not check consistency'),
                               ('/property_test_contract/tests/274', 'half-open height range excludes full24'),
                               ('/property_test_contract/tests/275', 'in-bounds modulo indices')]:
            self.assertIn(clause, by_member[member]['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, original in selected.items():
            for change in [dict(status='proved'), dict(evidence=['historical-tree-finite-trace']),
                           dict(reason='Finite traces prove full-height path soundness and authenticate unchecked storage.')]:
                reviews[key] = {**copy.deepcopy(original), **change}
                with self.subTest(member=original['selector']['member'], change=change):
                    with self.assertRaisesRegex(security.CheckError, 'applicability review'):
                        self.check()
            reviews[key] = original
        for i, entry in enumerate(entries):
            changed = entry[:3] + ('0' * 64,) + entry[4:]
            with patch.object(coverage, 'HISTORICAL_TCT_STRUCTURE_REVIEWS', entries[:i] + (changed,) + entries[i + 1:]):
                with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_tct_index_examples_do_not_establish_full_position_or_codec_bounds(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        entries = coverage.HISTORICAL_TCT_INDEX_REVIEWS
        members = {entry[0] for entry in entries}
        selected = {key: review for key, review in reviews.items()
                    if review['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and review['selector']['member'] in members}
        self.assertEqual(len(selected), 4)
        by_member = {r['selector']['member']: r for r in selected.values()}
        for member, clause in [('/property_test_contract/tests/101', 'bincode test is commented out'),
                               ('/property_test_contract/tests/253', 'half-open generator excludes65535'),
                               ('/property_test_contract/tests/254', 'Both half-open generators exclude65535'),
                               ('/property_test_contract/tests/255', 'not injectivity for arbitrary64-bit positions')]:
            self.assertIn(clause, by_member[member]['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, original in selected.items():
            for change in [dict(status='proved'), dict(evidence=['old-tct-property-test']),
                           dict(reason='Sampled conversions prove canonical arbitrary64-bit position injectivity.')]:
                reviews[key] = {**copy.deepcopy(original), **change}
                with self.subTest(member=original['selector']['member'], change=change):
                    with self.assertRaisesRegex(security.CheckError, 'applicability review'):
                        self.check()
            reviews[key] = original
        for i, entry in enumerate(entries):
            changed = entry[:3] + ('0' * 64,) + entry[4:]
            with patch.object(coverage, 'HISTORICAL_TCT_INDEX_REVIEWS', entries[:i] + (changed,) + entries[i + 1:]):
                with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_matching_memo_bodies_keep_heuristic_structure_and_privacy_distinct(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        entries = coverage.HISTORICAL_MEMO_TEST_REVIEWS
        members = {entry[0] for entry in entries}
        selected = {key: review for key, review in reviews.items()
                    if review['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and review['selector']['member'] in members}
        self.assertEqual(len(selected), 11)
        by_member = {r['selector']['member']: r for r in selected.values()}
        for member, clause in [('/property_test_contract/tests/55', 'cheap substring heuristic'),
                               ('/property_test_contract/tests/63', 'cannot treat None as authenticated approval'),
                               ('/property_test_contract/tests/85', 'regulated validation rejects that shape'),
                               ('/property_test_contract/tests/96', 'does not verify a circuit'),
                               ('/property_test_contract/tests/97', 'duplicate-key canonical JSON'),
                               ('/property_test_contract/tests/244', 'only two chosen Decaf field encodings'),
                               ('/property_test_contract/tests/279', 'intended structural-length branch')]:
            self.assertIn(clause, by_member[member]['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, original in selected.items():
            for change in [dict(status='proved'), dict(evidence=['old-compliance-memo-test']),
                           dict(reason='Correct memo length and field omission prove current ciphertext authorization and secrecy.')]:
                reviews[key] = {**copy.deepcopy(original), **change}
                with self.subTest(member=original['selector']['member'], change=change):
                    with self.assertRaisesRegex(security.CheckError, 'applicability review'):
                        self.check()
            reviews[key] = original
        for i, entry in enumerate(entries):
            changed = entry[:3] + ('0' * 64,) + entry[4:]
            with patch.object(coverage, 'HISTORICAL_MEMO_TEST_REVIEWS', entries[:i] + (changed,) + entries[i + 1:]):
                with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_matching_old_artifact_tests_do_not_certify_setup_or_misclassify_failure(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        entries = coverage.HISTORICAL_ARTIFACT_TEST_REVIEWS
        members = {entry[0] for entry in entries}
        selected = {key: review for key, review in reviews.items()
                    if review['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and review['selector']['member'] in members}
        self.assertEqual(len(selected), 7)
        by_member = {r['selector']['member']: r for r in selected.values()}
        for member, clause in [('/artifact_test_contract/tests/233', 'same-shape/different-relation fixture'),
                               ('/artifact_test_contract/tests/250', 'not ceremony randomness'),
                               ('/artifact_test_contract/tests/251', 'checks only the Circuit field'),
                               ('/artifact_test_contract/tests/252', 'size/digest checks before strict parsing'),
                               ('/artifact_test_contract/tests/269', 'old codec selection'),
                               ('/artifact_test_contract/tests/270', 'first accepts canonical PK/VK reads'),
                               ('/artifact_test_contract/tests/274', 'nil rejection is not semantic relation validation')]:
            self.assertIn(clause, by_member[member]['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in selected.values()))
        for key, original in selected.items():
            for change in [dict(status='proved'), dict(evidence=['old-key-parser-control']),
                           dict(reason='The appended byte proves strict parser rejection and setup security.')]:
                reviews[key] = {**copy.deepcopy(original), **change}
                with self.subTest(member=original['selector']['member'], change=change):
                    with self.assertRaisesRegex(security.CheckError, 'applicability review'):
                        self.check()
            reviews[key] = original
        for i, entry in enumerate(entries):
            changed = entry[:3] + ('0' * 64,) + entry[4:]
            with patch.object(coverage, 'HISTORICAL_ARTIFACT_TEST_REVIEWS', entries[:i] + (changed,) + entries[i + 1:]):
                with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_matching_historical_cache_bodies_keep_capability_and_resource_limits(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        entries = coverage.HISTORICAL_CACHE_TEST_REVIEWS
        members = {entry[0] for entry in entries}
        selected = {key: review for key, review in reviews.items()
                    if review['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and review['selector']['member'] in members}
        self.assertEqual(len(selected), 11)
        by_member = {r['selector']['member']: r for r in selected.values()}
        for member, clause in [('/runtime_policy_contract/tests/18', 'decoded memory'),
                               ('/runtime_policy_contract/tests/19', 'default invalid Groth16 proofs'),
                               ('/runtime_policy_contract/tests/21', 'not hash injectivity'),
                               ('/runtime_policy_contract/tests/23', 'no collision-resistance assumption'),
                               ('/runtime_policy_contract/tests/26', 'protected-clock branch'),
                               ('/runtime_policy_contract/tests/27', 'not genuine Transfer proof acceptance'),
                               ('/runtime_policy_contract/tests/28', 'not an unbounded invariant proof')]:
            self.assertIn(clause, by_member[member]['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == []
                            and r['selector']['owner'] == 'state-integration'
                            and 'Review is not an execution receipt' in r['reason']
                            for r in selected.values()))
        for key, original in selected.items():
            for change in [dict(status='proved'), dict(evidence=['old-cache-runtime-pass']),
                           dict(reason='Default test capabilities prove current Pari soundness and decoded memory bounds.')]:
                reviews[key] = {**copy.deepcopy(original), **change}
                with self.subTest(member=original['selector']['member'], change=change):
                    with self.assertRaisesRegex(security.CheckError, 'applicability review'):
                        self.check()
            reviews[key] = original
        for i, entry in enumerate(entries):
            changed = entry[:3] + ('0' * 64,) + entry[4:]
            with patch.object(coverage, 'HISTORICAL_CACHE_TEST_REVIEWS', entries[:i] + (changed,) + entries[i + 1:]):
                with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_matrix_test_ownership_is_membership_not_test_body_qualification(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        constants = ['MATRIX_TEST_OWNERSHIP_REVIEWS', 'MATRIX_SECRECY_OWNERSHIP_REVIEWS']
        members = {entry[0] for name in constants for entry in getattr(coverage, name)}
        selected = {key: review for key, review in reviews.items()
                    if review['selector']['source'] == '@history/fv-specification-predicate-matrix.json'
                    and review['selector']['member'] in members}
        self.assertEqual(len(selected), 22)
        by_member = {r['selector']['member']: r for r in selected.values()}
        for member, clause in [('/property_test_contract/owners/2', 'do not establish conservation'),
                               ('/property_test_contract/owners/10', 'Plans are not malicious consensus witnesses'),
                               ('/property_test_contract/owners/12', 'do not establish IND-CPA'),
                               ('/property_test_contract/owners/14', 'old ABI versions are not accepted evidence'),
                               ('/property_test_contract/source_census', 'independent exact-source correspondence'),
                               ('/artifact_test_contract/owners/1', 'independently supplied semantics'),
                               ('/artifact_test_contract/owners/2', 'test names do not establish pointer validity'),
                               ('/artifact_test_contract/owners/3', 'without reusing old parity/security receipts'),
                               ('/artifact_test_contract/source_census', 'no successful semantic control')]:
            self.assertIn(clause, by_member[member]['reason'])
        self.assertEqual(by_member['/property_test_contract/owners/12']['selector']['owner'], 'protocol')
        self.assertTrue(all(r['applicability'] == 'transfer_shared' and r['status'] == 'open'
                            and r['evidence'] == [] for r in selected.values()))
        for key, original in selected.items():
            for change in [dict(status='proved'), dict(evidence=['historical-test-owner-receipt']),
                           dict(reason='Named tests prove every current native relation and security contract.')]:
                reviews[key] = {**copy.deepcopy(original), **change}
                with self.subTest(member=original['selector']['member'], change=change):
                    with self.assertRaisesRegex(security.CheckError, 'applicability review'):
                        self.check()
            reviews[key] = original
        for name in constants:
            entries = getattr(coverage, name)
            for i, entry in enumerate(entries):
                changed = entry[:3] + ('0' * 64,) + entry[4:]
                with patch.object(coverage, name, entries[:i] + (changed,) + entries[i + 1:]):
                    with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_matrix_metadata_and_exclusions_do_not_establish_production_acceptance(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        constants=['MATRIX_METADATA_REVIEWS','MATRIX_FAMILY_METADATA_REVIEWS','MATRIX_EXCLUSION_REVIEWS']
        members={e[0] for name in constants for e in getattr(coverage,name)}
        source='@history/fv-specification-predicate-matrix.json'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and r['selector']['member'] in members}
        self.assertEqual(len(selected),13)
        by_member={r['selector']['member']:r for r in selected.values()}
        for member,clause in [('/role_sets','not an accepted LC/row or same-assignment certificate'),
                              ('/claim_set','does not establish completeness'),
                              ('/certification_status_vocabulary','not a status result'),
                              ('/profiles/2/metadata','matching counts prove no relation'),
                              ('/proof_acceptance_surface/nonproduction_exclusions/0','not an independent compiler/cfg audit'),
                              ('/proof_acceptance_surface/nonproduction_exclusions/1','not available in the archive for re-audit'),
                              ('/proof_acceptance_surface/nonproduction_exclusions/2','not successful controls')]:
            self.assertIn(clause,by_member[member]['reason'])
        self.assertEqual(sum(r['applicability']=='transfer_shared' for r in selected.values()),10)
        self.assertEqual(sum(r['selector']['owner']=='state-integration' for r in selected.values()),3)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-conditional-cfg-exclusion']),
                           dict(reason='Old source names and fixed slot counts establish current proof admission.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for constant in constants:
            entries=getattr(coverage,constant)
            for i,entry in enumerate(entries):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,constant,entries[:i]+(changed,)+entries[i+1:]):
                    with self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_native_census_keeps_constructor_and_circuit_boundaries_distinct(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='@history/native-circuit-predicate-census.json'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source}
        self.assertEqual(len(selected),6)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source})
        by_member={r['selector']['member']:r for r in selected.values()}
        for member,clause in [('/assumption_ids','untrusted native points and circuit roles must reject identity directly'),
                              ('/predicates/0','not an executed test receipt or source refinement'),
                              ('/predicates/1','honest diversifier-map nonidentity assumption'),
                              ('/predicates/2','252-bit subgroup-order remainder/quotient and actual inverse row'),
                              ('/predicates/3','canonical subgroup/codec and ownership multiplication rows')]:
            self.assertIn(clause,by_member[member]['reason'])
        self.assertTrue(all(r['status']=='open' and r['evidence']==[]
                            and r['applicability']=='transfer_shared' for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-native-test-recipe']),
                           dict(reason='Native types prove all current circuit nonidentity and map totality.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        entries=coverage.NATIVE_PREDICATE_CENSUS_REVIEWS
        for i,entry in enumerate(entries):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'NATIVE_PREDICATE_CENSUS_REVIEWS',entries[:i]+(changed,)+entries[i+1:]):
                with self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_historical_architecture_and_release_policy_do_not_certify_current_work(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        sources={'@history/snarkpack/DESIGN.md','@history/release.md'}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in sources}
        self.assertEqual(len(selected),46)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source'] in sources})
        bodies={(r['selector']['source'],r['selector']['member']):r for r in selected.values()}
        for source,member,clause in [
            ('@history/snarkpack/DESIGN.md','L11-L17','accepted-execution partial correctness'),
            ('@history/snarkpack/DESIGN.md','L28-L30','provenance only,not normative target'),
            ('@history/snarkpack/DESIGN.md','L38-L41','no actual current axiom audit'),
            ('@history/release.md','L88-L92','not semanticfalsification'),
            ('@history/release.md','L93-L102','not current161roster closure'),
            ('@history/release.md','L144-L149','didnot independently rebuildLeanclosure'),
            ('@history/release.md','L165-L175','errors never semanticcontrol passes')]:
            self.assertIn(clause,bodies[(source,member)]['reason'])
        self.assertTrue(all(r['status']=='open' and r['evidence']==[]
                            and r['applicability']=='transfer_shared' for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['historical-release-mode-pass']),
                           dict(reason='The old gate and architecture title certify every current Transfer obligation.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for constant in ['SNARKPACK_ARCHITECTURE_REVIEWS','HISTORICAL_RELEASE_POLICY_REVIEWS']:
            entries=getattr(coverage,constant)
            for i,entry in enumerate(entries):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,constant,entries[:i]+(changed,)+entries[i+1:]):
                    with self.subTest(constant=constant,member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_handoff_rendered_metadata_keeps_checker_and_security_limits(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='@history/snarkpack/formal-handoff.md'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source}
        self.assertEqual(len(selected),100)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('FULL-ADAPTIVE-END-TO-END-FV','not invalid-acceptance probability directly'),
                            ('DEPLOYED-SRS-SOUNDNESS','does not describe current v2 setup'),
                            ('OPTIMIZED-GT-FOLD-REFINEMENT','execution outside proof'),
                            ('RUST-TOKIO-JOIN-SEMANTICS','does not prove async scheduling'),
                            ('proofDecodeExact','external assumed strict old aggregate decoder'),
                            ('canonicalStatementInjective','distinct from finite hash collision security')]:
            self.assertIn(clause,by_name[name]['reason'])
        capstones=next(r for r in selected.values() if r['selector']['member']=='L114-L118')
        self.assertIn('Counts/status do not certify roots',capstones['reason'])
        property_rows=[r for r in selected.values() if r['selector']['historical_kind']=='property-record']
        self.assertEqual(len(property_rows),76)
        self.assertTrue(all('all rendered fields matched' in r['reason']
                            and 'not underlying theorem-body/axiom re-audit' in r['reason'] for r in property_rows))
        self.assertTrue(all(r['status']=='open' and r['evidence']==[]
                            and r['applicability']=='transfer_shared' for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-checker-pass']),
                           dict(reason='The historical title and audit count certify full current Transfer.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        entries=coverage.SNARKPACK_HANDOFF_REPORT_REVIEWS
        for i,entry in enumerate(entries):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'SNARKPACK_HANDOFF_REPORT_REVIEWS',entries[:i]+(changed,)+entries[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_remaining_family_bodies_keep_effects_and_conservation_as_premises(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        constants=['WITHDRAWAL_SEMANTICS_REVIEWS','WITHDRAWAL_CONCRETE_REVIEWS',
                   'WITHDRAWAL_SECURITY_REVIEWS','WITHDRAWAL_FACTS_REVIEWS',
                   'WITHDRAWAL_REFINEMENT_REVIEWS','NOTE_RESHAPE_CONCRETE_REVIEWS',
                   'NOTE_RESHAPE_SECURITY_REVIEWS','NOTE_RESHAPE_FACTS_REVIEWS',
                   'NOTE_RESHAPE_REFINEMENT_REVIEWS','WITHDRAWAL_ALLOY_REVIEWS',
                   'NOTE_RESHAPE_ALLOY_REVIEWS','NOTE_RESHAPE_ALLOY_STATE_REVIEWS']
        # These exact named sources have been read completely, including each branch.
        sources={'lean/ShieldedIcs20Withdrawal/'+name+'.lean'
                 for name in ['Semantics','Concrete','Security','CircuitFacts','Refinement']} | {
                 'lean/NoteReshape/'+name+'.lean'
                 for name in ['Concrete','Security','CircuitFacts','Refinement']} | {
                 'alloy/ics20-supply-conservation.als','alloy/note_reshape-statement-sufficiency.als'}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in sources}
        self.assertEqual(len(selected),265)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source'] in sources})
        bodies={(r['selector']['source'],r['selector']['member']):r for r in selected.values()}
        for source,member,clause in [
            ('lean/ShieldedIcs20Withdrawal/Semantics.lean','L320-L325','desired writes are premises'),
            ('lean/ShieldedIcs20Withdrawal/Semantics.lean','L450-L455','Old16-field prose conflicts with concrete21'),
            ('lean/ShieldedIcs20Withdrawal/Semantics.lean','L649-L652','no typed provenance'),
            ('lean/ShieldedIcs20Withdrawal/Semantics.lean','L769-L785','accepted.withdrawalEffects unchanged'),
            ('lean/ShieldedIcs20Withdrawal/Concrete.lean','L94-L104','Dummy RK derivation is absent'),
            ('lean/ShieldedIcs20Withdrawal/Concrete.lean','L144-L156','supplied field value equation'),
            ('lean/NoteReshape/Concrete.lean','L135-L136','Mismatched input/RK tails return empty'),
            ('lean/NoteReshape/Security.lean','L195-L210','supplied Concrete.conservation predicate'),
            ('lean/ShieldedIcs20Withdrawal/Refinement.lean','L31-L70','Durable effects are premises'),
            ('alloy/note_reshape-statement-sufficiency.als','L235-L238','repeats supplied BindingSigConserves equality'),
            ('alloy/ics20-supply-conservation.als','L82-L83','8steps/7-bit signed integers')]:
            self.assertIn(clause,bodies[(source,member)]['reason'])
        self.assertTrue(all(r['status']=='open' and r['evidence']==[]
                            and r['applicability'].startswith('separate_') for r in selected.values()))
        for source,member in [('lean/ShieldedIcs20Withdrawal/Semantics.lean','L769-L785'),
                              ('lean/ShieldedIcs20Withdrawal/Concrete.lean','L94-L104'),
                              ('lean/NoteReshape/Concrete.lean','L135-L136'),
                              ('alloy/note_reshape-statement-sufficiency.als','L235-L238')]:
            key=next(k for k,r in selected.items() if r['selector']['source']==source and r['selector']['member']==member)
            original=reviews[key]
            for change in [dict(status='proved'),dict(evidence=['old-projection-or-bounded-check']),
                           dict(applicability='transfer_shared'),dict(reason='Native conservation and effect execution are already proved.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(source=source,member=member,change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for constant in constants:
            entries=getattr(coverage,constant)
            for i,entry in enumerate(entries):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,constant,entries[:i]+(changed,)+entries[i+1:]):
                    with self.subTest(constant=constant,member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_withdrawal_matrix_preserves_external_source_postconditions(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='@history/fv-specification-predicate-matrix.json'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and r['selector']['member'] in {'/predicates/'+str(i) for i in range(72,83)}}
        self.assertEqual(len(selected),11)
        by_member={r['selector']['member']:r for r in selected.values()}
        for member,clause in [('/predicates/72','Rollback is separate executor testing'),
                              ('/predicates/74','before mutation'),
                              ('/predicates/76','no universal injectivity'),
                              ('/predicates/80','not a proof of executor refinement'),
                              ('/predicates/82','not substituted into current Transfer')]:
            self.assertIn(clause,by_member[member]['reason'])
        self.assertTrue(all(r['selector']['owner']=='state-integration'
                            and r['status']=='open' and r['evidence']==[]
                            and r['applicability']=='separate_withdrawal_milestone' for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['historical-listed-tests']),
                           dict(applicability='retired_history')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        entries=coverage.MATRIX_WITHDRAWAL_PREDICATE_REVIEWS
        for i,entry in enumerate(entries):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'MATRIX_WITHDRAWAL_PREDICATE_REVIEWS',entries[:i]+(changed,)+entries[i+1:]):
                with self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_filecoin_comparison_does_not_inherit_backend_certification(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='@history/snarkpack/filecoin-divergence-findings.md'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source}
        self.assertEqual(len(selected),38)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source})
        by_member={r['selector']['member']:r for r in selected.values()}
        for member,clause in [('L7-L10','not an upstream re-audit'),
                              ('L41-L48','No false blanket backend trust'),
                              ('L60-L60','own source'),
                              ('L62-L63','cannot inherit exemption'),
                              ('L107-L115','No current semantic control')]:
            self.assertIn(clause,by_member[member]['reason'])
        self.assertTrue(all(r['applicability']=='transfer_shared' and r['status']=='open'
                            and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-no-missing-fix']),
                           dict(reason='All Commonware and current cryptography are completely trusted.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        entries=coverage.FILECOIN_DIVERGENCE_REVIEWS
        for i,entry in enumerate(entries):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'FILECOIN_DIVERGENCE_REVIEWS',entries[:i]+(changed,)+entries[i+1:]):
                with self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_note_reshape_semantics_keep_transition_and_conservation_as_premises(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='lean/NoteReshape/Semantics.lean'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source}
        self.assertEqual(len(selected),78)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source})
        by_member={r['selector']['member']:r for r in selected.values()}
        for member,clause in [('L149-L153','desired state properties are fields'),
                              ('L181-L192','projection from transition premises'),
                              ('L197-L197','opaque canonical keys/scalars'),
                              ('L230-L232','Current Pari envelope/registry/claim source differs'),
                              ('L321-L322','Dummy randomizedKeys branch is True'),
                              ('L369-L376','Conservation is a premise'),
                              ('L421-L447','explicit committed premises'),
                              ('L483-L491','without deriving wallet construction'),
                              ('L116-L117','all-slot permanent replay stays live')]:
            self.assertIn(clause,by_member[member]['reason'])
        self.assertTrue(all(r['applicability']=='separate_note_reshape_milestone'
                            and r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['abstract-record-projection']),
                           dict(applicability='retired_history')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        entries=coverage.NOTE_RESHAPE_SEMANTICS_REVIEWS
        for i,entry in enumerate(entries):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'NOTE_RESHAPE_SEMANTICS_REVIEWS',entries[:i]+(changed,)+entries[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_withdrawal_roster_preserves_effect_limb_and_dummy_rk_limits(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/fv-predicate-consequence-roster.json'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and r['selector']['member'].startswith('/profiles/2/')}
        self.assertEqual(len(selected),40)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source
                                      and v['member'].startswith('/profiles/2/')})
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('CIR-SHAPE-FIXED','length21'),
                            ('DEC-SPEND-RK-DERIVATION','dummy derivation is absent'),
                            ('DEC-SPEND-RK-ENCODING','optional-dummy RK encodings'),
                            ('USER-LEAF-CANONICAL-DERIVATION-BINDING','same rfl hash5 equation'),
                            ('WITHDRAWAL-INTENT-FIELD-BINDING','does not prove limbs equal native withdrawal effect bytes'),
                            ('WITHDRAWAL-INTENT-FIELD-BINDING','permanent replay replaces removed history-window fields'),
                            ('ROUTING-PARAMETERS','Seg19/20/21.contract.spec')]:
            self.assertIn(clause,by_name[name]['reason'])
        self.assertTrue(all(r['applicability']=='separate_withdrawal_milestone'
                            and r['status']=='open' and r['evidence']==[] for r in selected.values()))
        roster=[r for r in reviews.values() if r['selector']['source']==source]
        self.assertEqual(len(roster),161)
        self.assertEqual(sum(r['applicability']=='transfer_shared' for r in roster),57)
        self.assertEqual(sum(r['applicability']=='separate_note_reshape_milestone' for r in roster),64)
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-withdrawal-receipt']),
                           dict(applicability='transfer_shared')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        entries=coverage.WITHDRAWAL_CONSEQUENCE_ROSTER_REVIEWS
        for i,entry in enumerate(entries):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'WITHDRAWAL_CONSEQUENCE_ROSTER_REVIEWS',entries[:i]+(changed,)+entries[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_note_reshape_roster_retains_real_branch_and_family_segment_scope(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/fv-predicate-consequence-roster.json'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and r['selector']['member'].startswith(('/profiles/0/','/profiles/1/'))}
        self.assertEqual(len(selected),64)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']==source
                                      and v['member'].startswith(('/profiles/0/','/profiles/1/'))})
        for profile,count in [('0',30),('1',34)]:
            family=[r for r in selected.values() if r['selector']['member'].startswith('/profiles/'+profile+'/')]
            self.assertEqual(len(family),count)
            by_name={r['selector']['name']:r for r in family}
            for name,clause in [('DEC-SPEND-RK-DERIVATION','dummy branch is True'),
                                ('NOTE-OUTPUT-OWNER-BINDING','not independent scalar ownership'),
                                ('VALUE-CONSERVATION','field-valued input sum'),
                                ('VALUE-CONSERVATION','Transfer actions can have nonzero net value'),
                                ('ROUTING-PARAMETERS','three family-specific routing segment specs')]:
                self.assertIn(clause,by_name[name]['reason'])
            self.assertIn('24,25,26' if profile=='0' else '34,35,36',by_name['ROUTING-PARAMETERS']['reason'])
            if profile=='0':self.assertNotIn('CIR-DUMMY-ORDER-COUNT',by_name)
            else:self.assertIn('realPrefix',by_name['CIR-DUMMY-ORDER-COUNT']['reason'])
        self.assertTrue(all(r['applicability']=='separate_note_reshape_milestone'
                            and r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-family-receipt']),
                           dict(applicability='transfer_shared')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        entries=coverage.NOTE_RESHAPE_CONSEQUENCE_ROSTER_REVIEWS
        for i,entry in enumerate(entries):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'NOTE_RESHAPE_CONSEQUENCE_ROSTER_REVIEWS',entries[:i]+(changed,)+entries[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_transfer_roster_preserves_actual_conclusions_and_unreviewed_family_members(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        source='shielded-pool/fv-predicate-consequence-roster.json'
        selected={k:r for k,r in reviews.items() if r['selector']['source']==source
                  and (r['selector']['member']=='/schema' or r['selector']['member'].startswith('/profiles/3/'))}
        expected={k for k,v in universe.items() if v['source']==source
                  and (v['member']=='/schema' or v['member'].startswith('/profiles/3/'))}
        self.assertEqual(set(selected),expected)
        self.assertEqual(len(selected),57)
        by_name={r['selector']['name']:r for r in selected.values()}
        for name,clause in [('VALUE-CONSERVATION','not zero net value or transaction conservation'),
                            ('CIR-SHAPE-FIXED','length47'),
                            ('ROUTING-PARAMETERS','Seg76/77/78.contract.spec'),
                            ('ROUTING-TAG-DERIVATION','twelve Seg79–90.contract.spec'),
                            ('DEC-ACK-DERIVATION','by rfl definition'),
                            ('FIELD-EPHEMERAL-SCALAR-RANGE','range only inside old definition'),
                            ('DEC-TRANSMISSION-KEY-DERIVATION','not current exact affine coordinate equality'),
                            ('COMPLIANCE-THRESHOLD-FLAG','prior+outbound128 volume'),
                            ('USER-LEAF-CANONICAL-DERIVATION-BINDING','no independent canonical derivation proof')]:
            self.assertIn(clause,by_name[name]['reason'])
        for r in selected.values():
            self.assertEqual(r['status'],'open')
            self.assertEqual(r['evidence'],[])
            if r['selector']['historical_kind']=='consequence':
                self.assertIn('old relationAll and semantic-provider/translator closure',r['reason'])
                self.assertIn('theorem specification_',r['reason'])
        # Every roster body now has its own exact family disposition; none is proved.
        pending=[v for k,v in universe.items() if v['source']==source and k not in reviews]
        self.assertEqual(pending,[])
        self.assertTrue(all(v['member'].startswith('/profiles/2/') for v in pending))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-gnark-kernel-receipt']),
                           dict(reason='The roster proves current Transfer and all transaction consequences.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        entries=coverage.TRANSFER_CONSEQUENCE_ROSTER_REVIEWS
        for i,entry in enumerate(entries):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'TRANSFER_CONSEQUENCE_ROSTER_REVIEWS',entries[:i]+(changed,)+entries[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_threat_model_keeps_joint_admission_and_family_scopes_open(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        selected={k:r for k,r in reviews.items() if r['selector']['source']=='shielded-pool/circuit-threat-model.md'}
        self.assertEqual(len(selected),7)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source']=='shielded-pool/circuit-threat-model.md'})
        by_member={r['selector']['member']:r for r in selected.values()}
        self.assertEqual(by_member['L11-L11']['applicability'],'separate_note_reshape_milestone')
        self.assertEqual(by_member['L12-L13']['applicability'],'separate_withdrawal_milestone')
        for member,clause in [('L3-L7','explicitly excludes constraint-level verification'),
                              ('L10-L10','sender and receiver nonidentity'),
                              ('L14-L22','per-slot nonidentity RK/signatures'),
                              ('L14-L22','identity BvK is only no-proof sentinel'),
                              ('L14-L22','beyond raw field-hash collision resistance'),
                              ('L14-L22','Current IVK hash_3/reduction')]:
            self.assertIn(clause,by_member[member]['reason'])
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['threat-list']),
                           dict(applicability='retired_history')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        entries=coverage.CIRCUIT_THREAT_MODEL_REVIEWS
        for i,entry in enumerate(entries):
            changed=entry[:3]+('0'*64,)+entry[4:]
            with patch.object(coverage,'CIRCUIT_THREAT_MODEL_REVIEWS',entries[:i]+(changed,)+entries[i+1:]):
                with self.subTest(member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                    coverage.source_occurrence_reviews(universe)

    def test_dleq_bodies_preserve_two_transcript_and_idealization_boundaries(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        packets={
            '@history/dleq/Group.lean':('DLEQ_GROUP_BODY_REVIEWS',6),
            '@history/dleq/Challenge.lean':('DLEQ_CHALLENGE_BODY_REVIEWS',5),
            '@history/dleq/Sigma.lean':('DLEQ_SIGMA_BODY_REVIEWS',8),
            '@history/dleq/FiatShamir.lean':('DLEQ_FIATSHAMIR_BODY_REVIEWS',9),
            '@history/dleq/Smoke.lean':('DLEQ_SMOKE_BODY_REVIEWS',2)}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in packets}
        self.assertEqual(len(selected),30)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source'] in packets})
        by_source={source:{r['selector']['member']:r for r in selected.values()
                          if r['selector']['source']==source} for source in packets}
        for source,(constant,count) in packets.items():
            self.assertEqual(len(by_source[source]),count)
            self.assertEqual(set(by_source[source]),{e[0] for e in getattr(coverage,constant)})
        for source,member,clause in [
            ('Group','L31-L32','is an axiom, not a primality proof'),
            ('Group','L37-L40','only the exact natural inequality'),
            ('Challenge','L45-L53','not hash injectivity'),
            ('Challenge','whole-source-support','4or5 preimages'),
            ('Sigma','L37-L37','only rel type declaration'),
            ('Sigma','L43-L58','uniform F includes zero'),
            ('Sigma','L76-L104','same statement and commitment'),
            ('Sigma','L76-L104','distinct challenges and injective embedding'),
            ('Sigma','L118-L142','perfect honest-verifier distribution'),
            ('FiatShamir','L48-L48','only its type declaration'),
            ('FiatShamir','L82-L97','honestly generated relation'),
            ('FiatShamir','L124-L136','CC-ASSUME-DLEQ-FS-NONMALLEABLE'),
            ('FiatShamir','whole-source-support','Fr wide64 reduction'),
            ('Smoke','L12-L12','elaboration/API availability only')]:
            self.assertIn(clause,by_source['@history/dleq/'+source+'.lean'][member]['reason'])
        self.assertTrue(all(r['applicability']=='transfer_shared' and r['status']=='open'
                            and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-dleq-kernel-receipt']),
                           dict(reason='Old DLEQ proves the current issuer transcript and adversarial statement security.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for constant,_ in packets.values():
            entries=getattr(coverage,constant)
            for i,entry in enumerate(entries):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,constant,entries[:i]+(changed,)+entries[i+1:]):
                    with self.subTest(constant=constant,member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_soundness_docs_preserve_independence_receipt_scope_and_measurement_limits(self):
        reviews=self.register['transfer_assurance']['source_occurrence_reviews']
        _,_,universe=coverage.historical_universe(security.ROOT,security.read_json)
        packets={
            '@history/soundness/README.md':('SOUNDNESS_AUTHORITY_REVIEWS',26),
            '@history/soundness/fv.md':('SOUNDNESS_FV_BOUNDARY_REVIEWS',45),
            '@history/soundness/optimization.md':('SOUNDNESS_OPTIMIZATION_REVIEWS',43)}
        selected={k:r for k,r in reviews.items() if r['selector']['source'] in packets}
        self.assertEqual(len(selected),114)
        self.assertEqual(set(selected),{k for k,v in universe.items() if v['source'] in packets})
        by_source={source:{r['selector']['member']:r for r in selected.values()
                          if r['selector']['source']==source} for source in packets}
        for source,(constant,count) in packets.items():
            self.assertEqual(len(by_source[source]),count)
            self.assertEqual(set(by_source[source]),{e[0] for e in getattr(coverage,constant)})
        for source,member,clause in [
            ('@history/soundness/README.md','L23-L23','direct generated edits is prohibited'),
            ('@history/soundness/README.md','L35-L39','Current Commonware patch closure is live'),
            ('@history/soundness/README.md','L75-L78','localpatch guarantees explicitly'),
            ('@history/soundness/fv.md','L69-L75','circularly'),
            ('@history/soundness/fv.md','L76-L81','fixed-secret satisfiability'),
            ('@history/soundness/fv.md','L179-L187','no enumerated typed action provenance'),
            ('@history/soundness/fv.md','L260-L278','coherence is not derivation or erasure'),
            ('@history/soundness/fv.md','L358-L364','changed source invalidates old kernel receipt'),
            ('@history/soundness/optimization.md','L104-L104','not current200770row relation'),
            ('@history/soundness/optimization.md','L122-L123','current252canonicalscalar or255fieldreader'),
            ('@history/soundness/optimization.md','L134-L136','body is no Lean declaration'),
            ('@history/soundness/optimization.md','L137-L141','not compiler/timeout failure')]:
            self.assertIn(clause,by_source[source][member]['reason'])
        self.assertEqual(sum(r['applicability']=='transfer_shared' for r in selected.values()),92)
        self.assertEqual(sum('note_reshape' in r['applicability'] for r in selected.values()),19)
        self.assertEqual(sum('withdrawal' in r['applicability'] for r in selected.values()),3)
        self.assertTrue(all(r['status']=='open' and r['evidence']==[] for r in selected.values()))
        for key,original in selected.items():
            for change in [dict(status='proved'),dict(evidence=['old-certified-family-label']),
                           dict(reason='The old certification documents and constraint counts prove current Transfer soundness.')]:
                reviews[key]={**copy.deepcopy(original),**change}
                with self.subTest(member=original['selector']['member'],change=change),self.assertRaisesRegex(security.CheckError,'applicability review'):
                    self.check()
            reviews[key]=original
        for constant,_ in packets.values():
            entries=getattr(coverage,constant)
            for i,entry in enumerate(entries):
                changed=entry[:3]+('0'*64,)+entry[4:]
                with patch.object(coverage,constant,entries[:i]+(changed,)+entries[i+1:]):
                    with self.subTest(constant=constant,member=entry[0]),self.assertRaisesRegex(ValueError,'reviewed historical selector changed'):
                        coverage.source_occurrence_reviews(universe)

    def test_native_reviews_preserve_quotient_codec_and_live_dleq_caller_gaps(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {entry[0] for entry in coverage.COMMON_NATIVE_REVIEWS}
        native = [r for r in reviews.values() if r['selector']['source'] == 'lean/Common.lean'
                  and r['selector']['member'] in members]
        self.assertEqual(len(native), 25)
        by_name = {r['selector']['name']: r for r in native}
        self.assertIn('not affine coordinate equality', by_name['equivalent']['reason'])
        self.assertIn('optional request', by_name['doubleBaseDigit']['reason'])
        self.assertEqual(by_name['doubleBaseDigit']['obligation'], 'current:disclosure')
        self.assertIn('zero-denominator sqrt0', by_name['sqrtCase']['reason'])
        self.assertIn('three ordered fields nk,ak.x,ak.y', by_name['dtkIvkModQ']['reason'])
        self.assertIn('equal reduced remainders', by_name['incomingViewingKeyDerived']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in native))
        # Identical empty-ladder text remains two exact source occurrences.
        bases = [r for r in reviews.values() if r['selector']['source'] == 'lean/Common.lean'
                 and r['selector']['member'] in ['L238-L238', 'L292-L292']]
        self.assertEqual(len(bases), 2)
        self.assertEqual(bases[0]['selector']['member_sha256'], bases[1]['selector']['member_sha256'])
        self.assertNotEqual(coverage.identity(bases[0]['selector']), coverage.identity(bases[1]['selector']))
        key = coverage.identity(by_name['doubleBaseDigit']['selector'])
        original = copy.deepcopy(reviews[key])
        reviews[key]['obligation'] = 'current:upstream-contract'
        with self.assertRaisesRegex(security.CheckError, 'applicability review'):
            self.check()
        reviews[key] = original

    def test_radix4_reviews_keep_width_bounds_and_each_duplicate_body_occurrence(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {entry[0] for entry in coverage.COMMON_WINDOW_REVIEWS}
        windows = [r for r in reviews.values() if r['selector']['source'] == 'lean/Common.lean'
                   and r['selector']['member'] in members]
        self.assertEqual(len(windows), 14)
        odd = next(r for r in windows if r['selector']['name'] == 'scalarMulWindow2OddFromBits')
        self.assertIn('m=0', odd['reason'])
        self.assertIn('positive pair count', odd['reason'])
        self.assertIn('Current252bit loop is even', odd['reason'])
        bases = [r for r in windows if r['selector']['member'] in ['L213-L213', 'L228-L228']]
        self.assertEqual(len(bases), 2)
        self.assertEqual(bases[0]['selector']['member_sha256'], bases[1]['selector']['member_sha256'])
        self.assertNotEqual(coverage.identity(bases[0]['selector']), coverage.identity(bases[1]['selector']))
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in windows))

    def test_accepted_fact_templates_cannot_substitute_for_current_soundness_or_execution(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        selected = [r for r in reviews.values() if r['selector']['source'] in (
            'lean/Transfer/Security.lean', 'lean/Transfer/CircuitFacts.lean',
            'lean/Transfer/Refinement.lean')]
        self.assertEqual(len(selected), 17)
        by_name = {r['selector']['name']: r for r in selected}
        rk = by_name['consensusAccepted_randomizedVerificationKeys_nonIdentity']
        self.assertIn('already present in assumed acceptance', rk['reason'])
        self.assertIn('single action RK', rk['reason'])
        self.assertEqual(rk['obligation'], 'current:action-key')
        self.assertIn('eleven fields assume', by_name['CircuitFacts']['reason'])
        self.assertEqual(by_name['CircuitFacts']['obligation'], 'current:full-relation')
        committed = by_name['transactionAccepted_of_circuitFacts']
        self.assertIn('already assumes unique/fresh', committed['reason'])
        self.assertEqual(committed['obligation'], 'current:state')
        self.assertTrue(all(r['status'] == 'open' and not r['evidence'] for r in selected))
        original = copy.deepcopy(rk)
        key = coverage.identity(original['selector'])
        for field, value in [('status', 'proved'), ('evidence', ['historical-Lean']),
                             ('reason', 'accepted source record proves current arbitrary rows')]:
            reviews[key] = {**copy.deepcopy(original), field: value}
            with self.subTest(field=field), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                self.check()
        reviews[key] = original

    def test_map_replacement_keeps_zero_branch_and_transaction_balance_contract(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {entry[0] for entry in coverage.COMMON_MAP_REVIEWS}
        maps = [r for r in reviews.values() if r['selector']['source'] == 'lean/Common.lean'
                and r['selector']['member'] in members]
        self.assertEqual(len(maps), 18)
        by_name = {r['selector']['name']: r for r in maps}
        self.assertIn('assumes both output denominators nonzero', by_name['relation']['reason'])
        self.assertIn('identity branch followed by cofactor8', by_name['relation']['reason'])
        self.assertIn('source-read, not rerun or promoted', by_name['relation']['reason'])
        self.assertIn('selector0/1', by_name['selectF']['reason'])
        self.assertIn('per-action balance may be nonzero', by_name['netBalanceCommitment2']['reason'])
        self.assertIn('not universal generator independence', by_name['valueGeneratorDomain']['reason'])
        self.assertTrue(all(r['obligation'] == 'current:balance' and r['status'] == 'open'
                            and r['evidence'] == [] for r in maps))
        old_constants = [r for r in reviews.values() if r['selector']['source'] == 'lean/Common.lean'
                         and r['selector']['member'] in ['L312-L314', 'L384-L386']]
        self.assertEqual(len(old_constants), 2)
        self.assertEqual(old_constants[0]['selector']['member_sha256'],
                         old_constants[1]['selector']['member_sha256'])
        self.assertNotEqual(coverage.identity(old_constants[0]['selector']),
                            coverage.identity(old_constants[1]['selector']))

    def test_complete_common_review_preserves_all_current_tree_hash_and_native_gaps(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        common = [r for r in reviews.values() if r['selector']['source'] == 'lean/Common.lean']
        self.assertEqual(len(common), 129)
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        self.assertEqual({coverage.identity(r['selector']) for r in common},
                         {key for key, selector in universe.items()
                          if selector.get('source') == 'lean/Common.lean'})
        by_member = {r['selector']['member']: r for r in common}
        self.assertIn('no current two-modulus reduction', by_member['L16-L17']['reason'])
        self.assertIn('current native_root begins directly', by_member['L514-L518']['reason'])
        self.assertIn('indices above3', by_member['L557-L558']['reason'])
        self.assertIn('runtime tree depth0 is rejected', by_member['L585-L585']['reason'])
        self.assertIn('current ordered eight fields', by_member['L479-L483']['reason'])
        self.assertIn('persistent width6 state', by_member['L608-L610']['reason'])
        self.assertIn('membership alone', by_member['L588-L592']['reason'])
        self.assertTrue(all(r['status'] == 'open' and r['evidence'] == [] for r in common))

    def test_historical_committed_effect_records_are_premises_not_native_proofs(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        names = {r['selector']['name']: r for r in reviews.values()
                 if r['selector']['source'] == 'lean/Common.lean'}
        self.assertIn('ASSUME nullifiersUnique', names['CommittedEffects']['reason'])
        self.assertIn('assume the desired state outcome', names['CommittedTargetTransaction']['reason'])
        self.assertEqual(names['CommittedEffects']['obligation'], 'current:state')
        self.assertEqual(names['proofBearingBindingSignatureAccepted']['obligation'], 'current:admission')
        self.assertIn('multiplicity', names['exactExtension']['reason'])
        self.assertTrue(all(names[name]['status'] == 'open' and names[name]['evidence'] == []
                            for name in ['CommittedEffects', 'CommittedTargetTransaction', 'exactExtension']))

    def test_local_patch_guarantees_cannot_be_omitted_or_promoted(self):
        dependencies = self.register['transfer_assurance']['dependencies']
        original = copy.deepcopy(dependencies)
        for name in coverage.LOCAL_PATCH_REVIEWS:
            review = original['local_patch_reviews'][name]
            self.assertIn('guarantee', review)
            self.assertTrue(review['native_tests'])
            self.assertEqual(review['status'], 'source_reviewed_guarantee_refinement_open')
            self.assertEqual(review['evidence'], [])
            for field, value in [('status', 'proved'), ('evidence', ['upstream-trust']),
                                 ('missing', ''), ('native_tests', [])]:
                self.register['transfer_assurance']['dependencies'] = copy.deepcopy(original)
                self.register['transfer_assurance']['dependencies']['local_patch_reviews'][name][field] = value
                with self.subTest(patch=name, field=field), self.assertRaisesRegex(security.CheckError, 'dependency contract'):
                    self.check()
        self.register['transfer_assurance']['dependencies'] = copy.deepcopy(original)
        del self.register['transfer_assurance']['dependencies']['local_patch_reviews']['0005-pari-constant-outline.patch']
        with self.assertRaisesRegex(security.CheckError, 'dependency contract'):
            self.check()

    def test_missing_or_new_applicability_review_fails(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        key = next(iter(reviews))
        review = reviews.pop(key)
        with self.assertRaisesRegex(security.CheckError, 'applicability review'):
            self.check()
        reviews[key] = review
        reviews['unknown'] = copy.deepcopy(review)
        with self.assertRaisesRegex(security.CheckError, 'applicability review'):
            self.check()

    def test_review_remap_source_drift_or_proof_promotion_fails(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        key = next(iter(reviews))
        original = copy.deepcopy(reviews[key])
        for field, value in [('obligation', 'current:full-relation'),
                             ('applicability', 'excluded'), ('reason', 'retired'),
                             ('status', 'proved'), ('evidence', ['historical-proof'])]:
            with self.subTest(field=field):
                reviews[key] = {**copy.deepcopy(original), field: value}
                with self.assertRaisesRegex(security.CheckError, 'applicability review'):
                    self.check()
        reviews[key] = copy.deepcopy(original)
        reviews[key]['selector']['member_sha256'] = 'f' * 64
        with self.assertRaisesRegex(security.CheckError, 'applicability review'):
            self.check()

    def test_reviewed_source_missing_from_universe_fails(self):
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        key = next(iter(self.register['transfer_assurance']['source_occurrence_reviews']))
        del universe[key]
        with self.assertRaisesRegex(ValueError, 'reviewed historical selector changed'):
            coverage.source_occurrence_reviews(universe)

    def test_duplicate_exact_source_review_refused_before_register_overwrite(self):
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        duplicate = coverage.COMMON_NATIVE_REVIEWS + (coverage.COMMON_NATIVE_REVIEWS[0],)
        with patch.object(coverage, 'COMMON_NATIVE_REVIEWS', duplicate):
            with self.assertRaisesRegex(ValueError, 'duplicate reviewed historical selector'):
                coverage.source_occurrence_reviews(universe)

    def test_unknown_review_applicability_cannot_fall_through_to_other_family(self):
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        original = coverage.RETIRED_HISTORY_REVIEWS
        changed = original[0][:4] + ('retired_everything',) + original[0][5:]
        with patch.object(coverage, 'RETIRED_HISTORY_REVIEWS', (changed,) + original[1:]):
            with self.assertRaisesRegex(ValueError, 'unsupported reviewed historical applicability'):
                coverage.source_occurrence_reviews(universe)

    def test_unknown_current_review_obligation_fails_at_mapping_boundary(self):
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        original = coverage.TRANSFER_LAYOUT_REVIEWS
        changed = original[0][:6] + ('current:unregistered',)
        with patch.object(coverage, 'TRANSFER_LAYOUT_REVIEWS', (changed,) + original[1:]):
            with self.assertRaisesRegex(ValueError, 'unsupported reviewed historical obligation'):
                coverage.source_occurrence_reviews(universe)

    def test_exact_history_accessors_retired_without_retiring_current_replay(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        retired = [r for r in reviews.values() if r['applicability'] == 'retired_history']
        self.assertEqual({r['selector']['member'] for r in retired},
                         {'L79-L79', 'L80-L80', 'L81-L82'})
        for review in retired:
            self.assertEqual(review['selector']['source'], 'lean/Transfer/Semantics.lean')
            self.assertEqual(review['disposition'], 'retired')
            self.assertEqual(review['status'], 'open')
            self.assertEqual(review['evidence'], [])
            self.assertIn('permanent spend replay', review['contract'])
            self.assertIn('day-scoped volume replay', review['contract'])
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        # Mixed spend/nullifier declarations remain live after their own review.
        for name in ['RealSpend', 'DummySpend', 'OptionalSpend.nullifier']:
            keys = [key for key, selector in universe.items()
                    if selector.get('source') == 'lean/Transfer/Semantics.lean'
                    and selector.get('name') == name]
            self.assertEqual(len(keys), 1)
            self.assertEqual(reviews[keys[0]]['applicability'], 'transfer_shared')
            self.assertEqual(reviews[keys[0]]['obligation'], 'current:spends')
            self.assertEqual(reviews[keys[0]]['status'], 'open')
        key = coverage.identity(retired[0]['selector'])
        original = copy.deepcopy(reviews[key])
        for field, value in [('status', 'proved'), ('applicability', 'retired_history_and_replay'),
                             ('contract', 'all replay is retired')]:
            reviews[key] = {**copy.deepcopy(original), field: value}
            with self.subTest(field=field), self.assertRaisesRegex(security.CheckError, 'applicability review'):
                self.check()
        reviews[key] = original

    def test_envelope_reviews_keep_assumed_state_and_honest_entropy_separate(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        members = {entry[0] for entry in coverage.TRANSFER_ENVELOPE_REVIEWS}
        envelope = [r for r in reviews.values()
                    if r['selector']['source'] == 'lean/Transfer/Semantics.lean'
                    and r['selector']['member'] in members]
        self.assertEqual(len(envelope), 22)
        by_name = {r['selector']['name']: r for r in envelope}
        self.assertIn('assumes live/current roots', by_name['ConsensusTransition']['reason'])
        self.assertIn('already premises', by_name['TransactionAccepted']['reason'])
        self.assertIn('all assumed', by_name['transactionAcceptedNullifiersUnique']['reason'])
        self.assertIn('ordered payload provenance', by_name['transactionAcceptedIncludesTargetOutputs']['reason'])
        self.assertIn('even for dummy', by_name['actionNullifiers']['reason'])
        self.assertIn('current single action RK', by_name['SpendSlot']['reason'])
        for name in ['ConstructionChecks', 'HonestConstructionFacts', 'ConstructedAndAccepted']:
            self.assertEqual(by_name[name]['obligation'], 'current:privacy')
        self.assertTrue(all(r['status'] == 'open' and not r['evidence'] for r in envelope))
        self.assertIn('no-inflation', by_name['ExternalChecks']['reason'])
        self.assertIn('matching keys/upstream contracts', by_name['ExternalChecks']['reason'])

    def test_full_semantics_layout_review_preserves_current_roles_and_retired_boundary(self):
        reviews = self.register['transfer_assurance']['source_occurrence_reviews']
        semantic = [r for r in reviews.values() if r['selector']['source'] == 'lean/Transfer/Semantics.lean']
        self.assertEqual(len(semantic), 55)
        _, _, universe = coverage.historical_universe(security.ROOT, security.read_json)
        self.assertEqual({coverage.identity(r['selector']) for r in semantic},
                         {key for key, selector in universe.items()
                          if selector.get('source') == 'lean/Transfer/Semantics.lean'})
        by_name = {r['selector']['name']: r for r in semantic}
        self.assertIn('unconditionally range-constrained', by_name['DummySpend']['reason'])
        self.assertIn('stronger relation', by_name['.dummy spend => spend.randomizedVerificationKey']['reason'])
        self.assertIn('does not force zero itself', by_name['.dummy spend => spend.amount']['reason'])
        self.assertIn('131bit lifecycle', by_name['ComplianceProof']['reason'])
        self.assertIn('audit epoch/payload/checking', by_name['IndexedAssetLeaf']['reason'])
        self.assertIn('eight-field note hash including recovery', by_name['Note']['reason'])
        self.assertEqual(sum(r['disposition'] == 'retired' for r in semantic), 3)
        self.assertTrue(all(r['status'] == 'open' and not r['evidence'] for r in semantic))

    def test_separate_family_group_cannot_be_silently_removed(self):
        groups = self.register['transfer_assurance']['occurrence_groups']
        key = 'migration-member:current:migration-review:separate_note_reshape_milestone'
        self.assertEqual(groups[key]['count'], 339)
        del groups[key]
        with self.assertRaisesRegex(security.CheckError, 'source occurrences'):
            self.check()

    def test_admission_paths_cannot_be_removed_remapped_or_promoted(self):
        section = self.register['transfer_assurance']
        original = copy.deepcopy(section['acceptance_paths'])
        for mutate in [lambda x: x['paths'].pop('fallback'),
                       lambda x: x['paths']['cached-delivery'].update(obligations=['current:full-relation']),
                       lambda x: x['signature_dependency'].update(version='0.5.3'),
                       lambda x: x['signature_dependency'].update(status='proved'),
                       lambda x: x.update(status='proved'),
                       lambda x: x.update(evidence=['source-digest']),
                       lambda x: x.update(assumptions=[])]:
            section['acceptance_paths'] = copy.deepcopy(original)
            mutate(section['acceptance_paths'])
            with self.assertRaisesRegex(security.CheckError, 'acceptance path'):
                self.check()


    def test_missing_requirement_fails(self):
        del self.register['transfer_assurance']['obligations']['DUMMY-AMOUNT-ZERO']
        with self.assertRaisesRegex(security.CheckError, 'missing or unknown'):
            self.check()

    def test_unknown_requirement_fails(self):
        self.register['transfer_assurance']['obligations']['HISTORY-PROMOTED'] = {}
        with self.assertRaisesRegex(security.CheckError, 'missing or unknown'):
            self.check()

    def test_source_occurrence_cannot_be_removed_or_retired(self):
        groups = self.register['transfer_assurance']['occurrence_groups']
        key = next(key for key in groups if key.startswith('historical-test-source:'))
        groups[key]['count'] -= 1
        with self.assertRaisesRegex(security.CheckError, 'source occurrences'):
            self.check()
        groups[key]['count'] += 1
        groups[key]['applicability'] = 'excluded'
        with self.assertRaisesRegex(security.CheckError, 'source occurrences'):
            self.check()

    def test_scope_or_status_promotion_fails(self):
        self.register['transfer_assurance']['status'] = 'complete'
        with self.assertRaisesRegex(security.CheckError, 'unsupported Transfer completion'):
            self.check()

    def test_unsupported_proof_and_retirement_fail(self):
        entry = self.register['transfer_assurance']['obligations']['DUMMY-AMOUNT-ZERO']
        entry['status'] = 'proved'
        with self.assertRaisesRegex(security.CheckError, 'unsupported Transfer obligation'):
            self.check()
        entry['status'] = 'open'
        entry['disposition'] = 'retired'
        with self.assertRaisesRegex(security.CheckError, 'invalid Transfer disposition'):
            self.check()

    def test_stale_runtime_and_historical_identity_fail(self):
        self.register['transfer_assurance']['runtime_sha'] = 'a' * 40
        with self.assertRaisesRegex(security.CheckError, 'stale Transfer runtime'):
            self.check()
        self.register['transfer_assurance']['runtime_sha'] = security.locked_sha()
        self.register['transfer_assurance']['historical_inputs'][coverage.MIGRATION] = 'a' * 64
        with self.assertRaisesRegex(security.CheckError, 'historical source identity'):
            self.check()

    def test_unknown_dependency_and_cycle_fail(self):
        entry = self.register['transfer_assurance']['obligations']['current:patches']
        entry['conditional_on'] = ['unknown']
        with self.assertRaisesRegex(security.CheckError, 'unknown or duplicate Transfer dependency'):
            self.check()
        entry['conditional_on'] = ['current:relation-key']
        with self.assertRaisesRegex(security.CheckError, 'cyclic Transfer dependencies'):
            self.check()

    def test_constructor_order_and_dependency_trust_fail(self):
        constructors = self.register['transfer_assurance']['constructors']
        constructors[0], constructors[1] = constructors[1], constructors[0]
        with self.assertRaisesRegex(security.CheckError, 'current Transfer constructor'):
            self.check()
        constructors[0], constructors[1] = constructors[1], constructors[0]
        self.register['transfer_assurance']['dependencies']['local_patch_status'] = 'assumed'
        with self.assertRaisesRegex(security.CheckError, 'dependency contract'):
            self.check()

    def test_open_join_blocks_stage_and_delivery(self):
        self.register['transfer_assurance']['stage_gates']['T4'] = 'complete'
        with self.assertRaisesRegex(security.CheckError, 'stage completion'):
            self.check()
        self.register['transfer_assurance']['stage_gates']['T4'] = 'open'
        self.register['delivery_milestones']['complete_transfer'] = 'complete'
        with self.assertRaisesRegex(security.CheckError, 'delivery gate'):
            self.check()


class AdmissionSourceContractTests(unittest.TestCase):
    """Synthetic marker fixtures exercise source-contract refusals, not Rust tests."""
    def setUp(self):
        self.metadata = copy.deepcopy(coverage.ADMISSION_SOURCE_FILES)
        self.sources = {path: ('\n'.join(m['guards']) + '\n').encode()
                        for path, m in self.metadata.items()}
        for path, raw in self.sources.items():
            self.metadata[path]['sha256'] = hashlib.sha256(raw).hexdigest()

    def inspect(self):
        with patch.object(coverage, 'ADMISSION_SOURCE_FILES', self.metadata):
            return coverage.inspect_admission_source_contracts(self.sources, security.CheckError)

    def test_source_contract_fixture_is_explicitly_unqualified(self):
        result = self.inspect()
        self.assertEqual(result['status'], 'source_reviewed_refinement_open')
        self.assertEqual(result['evidence'], [])
        self.assertEqual(result['files'], 48)
        self.assertEqual(result['guards'], 300)
        self.assertEqual(result['paths'], 16)

    def test_published_snapshot_and_nullifier_reader_fail_closed_source_controls(self):
        controls = [
            ('crates/bin/shieldd/src/query.rs', b'height != expected.height', b'false'),
            ('crates/bin/shieldd/src/query.rs', b'root.0.as_slice() != expected.root_hash', b'false'),
            ('crates/bin/shieldd/src/query.rs', b'boundary.height != Some(height)', b'false'),
            ('crates/bin/shieldd/src/query.rs', b'boundary.block_id.as_slice() != expected.block_id', b'false'),
            ('crates/bin/shieldd/src/query.rs', b'self.nullifiers()?.validate_boundary(&boundary)', b'Ok::<(), ServiceError>(())'),
            ('crates/bin/shieldd/src/query.rs', b'previous.snapshot.version() > snapshot.version()', b'false'),
            ('crates/bin/shieldd/src/query.rs', b'HostExecution::check_tx_at(self.snapshot()?,', b'HostExecution::check_tx_at(self.storage.latest_snapshot(),'),
            ('crates/core/app/src/app/host.rs', b'BlockTxIndexingMode::NoIndex', b'BlockTxIndexingMode::Immediate'),
            ('crates/core/app/src/app/host.rs', b'self.phase == HostExecutionPhase::InBlock,', b'true,'),
            ('crates/core/component/sct/src/permanent_nullifiers/store.rs', b'store.actual_roots() == boundary.roots,', b'true,'),
            ('crates/core/component/sct/src/permanent_nullifiers/store.rs', b'self.boundary.as_ref() == Some(committed),', b'true,'),
            ('crates/core/component/sct/src/permanent_nullifiers/store.rs', b'status.verify(&committed)?;', b''),
            ('crates/core/component/sct/src/permanent_nullifiers.rs', b'&self.boundary == committed,', b'true,'),
            ('crates/core/component/sct/src/permanent_nullifiers.rs', b'hash.update(nullifier.to_bytes());', b'hash.update([0u8; 32]);'),
            ('crates/core/component/sct/src/permanent_nullifiers.rs', b'let path = key(self.nullifier);', b'let path = [0u8; 32];'),
            ('crates/core/component/sct/src/permanent_nullifiers.rs', b'value_hash: Sha2Hasher::hash_value(SPENT_VALUE)', b'value_hash: [0u8; 32]'),
            ('crates/core/component/sct/src/permanent_nullifiers.rs', b'.confirm_nonexistence(&path)', b'.confirm_nonexistence(&[0u8; 32])'),
            ('crates/core/component/sct/src/component/tree.rs', b'*spent |= pending.contains(nullifier);', b'*spent = pending.contains(nullifier);'),
        ]
        for path, old, new in controls:
            with self.subTest(path=path, guard=old):
                original = self.sources[path]
                self.assertEqual(original.count(old), 1)
                self.sources[path] = original.replace(old, new)
                try:
                    with self.assertRaisesRegex(security.CheckError, 'source guard/API changed'):
                        self.inspect()
                finally:
                    self.sources[path] = original

    def test_publication_review_retains_concurrency_and_source_assumptions(self):
        contract = coverage.ADMISSION_PATHS['published-checktx-and-live-delivery']['contract']
        for boundary in ['older published snapshot may become unavailable',
                         'Bankd calling publication after its durable commit/recovery record',
                         'Rust concurrency/cancellation', 'not unreviewed query methods',
                         'pinned NOMT PathProof verification remain upstream',
                         'raw value-index miss is not unspentness']:
            self.assertIn(boundary, contract)
        self.assertEqual(self.inspect()['evidence'], [])

    def test_lazy_proving_key_check_is_not_registry_load_or_setup_certification(self):
        contract = coverage.ADMISSION_PATHS['local-key-registry']['contract']
        for boundary in ['proving-key artifact hashing/decoding is lazy',
                         'Registry load alone is not proving-key validation',
                         'full sparse public columns', 'correct setup ceremony']:
            self.assertIn(boundary, contract)
        path = 'crates/crypto/proof-params/src/pari.rs'
        original = self.sources[path]
        for old, new in [(b'key.verifying_key() == &trusted.verifying,', b'true,'),
                         (b'let values = catalogue::evaluate(witness)?;', b'let values = unrelated_values;')]:
            with self.subTest(guard=old):
                self.assertEqual(original.count(old), 1)
                self.sources[path] = original.replace(old, new)
                try:
                    with self.assertRaisesRegex(security.CheckError, 'source guard/API changed'):
                        self.inspect()
                finally:
                    self.sources[path] = original

    def test_native_projection_source_edges_cannot_be_swapped_or_omitted(self):
        controls = [
            ('crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
             b'nullifier: input.nullifier,', b'nullifier: other_nullifier,'),
            ('crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
             b'note_commitment: output.note_payload.note_commitment,', b'note_commitment: unrelated,'),
            ('crates/core/component/shielded-pool/src/public_input_hash.rs',
             b'note: o.note_commitment.0, recovery: o.recovery_commitment.0,',
             b'note: o.recovery_commitment.0, recovery: o.note_commitment.0,'),
            ('crates/crypto/circuits/src/transfer.rs',
             b'for s in &self.spends { f.push(s.nullifier.clone()); }', b''),
            ('crates/core/component/shielded-pool/src/transfer/generated.rs',
             b'PADDED_TRANSFER_INPUTS: usize = 2;', b'PADDED_TRANSFER_INPUTS: usize = 1;'),
            ('crates/core/app/src/stateless_cache.rs',
             b'ProofSlot::FeeFunding, ProofLocation { family_id, family_index, },',
             b'ProofSlot::BodyAction(0), ProofLocation { family_id, family_index, },'),
        ]
        for path, old, new in controls:
            with self.subTest(edge=old):
                original = self.sources[path]
                self.assertEqual(original.count(old), 1)
                self.sources[path] = original.replace(old, new)
                with self.assertRaisesRegex(security.CheckError, 'source guard/API changed'):
                    self.inspect()
                self.sources[path] = original

    def test_wrong_family_registry_and_prebound_api_source_controls(self):
        controls = [
            ('crates/crypto/circuits/src/proof.rs', b'self.family == family', b'true'),
            ('crates/crypto/proof-params/src/pari.rs', b'items.iter().all(|item| item.family == family)', b'true'),
            ('crates/core/app/src/stateless_cache.rs', b'capability.registry_id() == registry.id()', b'true'),
            ('crates/core/app/src/stateless_cache.rs', b'value.registry_id != registry_id || value.raw_tx.as_ref() != raw_tx', b'false'),
            ('crates/crypto/circuits/src/proof.rs', b'pari::verify(', b'pari::verify_prebound('),
            ('crates/crypto/circuits/src/proof.rs', b'pari::batch_verify(', b'pari::batch_verify_prebound('),
            ('third_party/commonware/cryptography/src/zk/pari/mod.rs', b'transcript.commit(claim.encode());', b''),
            ('third_party/commonware/cryptography/src/zk/pari/verifier.rs', b'transcript.commit(claim.encode());', b''),
        ]
        for path, old, new in controls:
            with self.subTest(path=path, guard=old):
                original = self.sources[path]
                self.assertEqual(original.count(old), 1)
                self.sources[path] = original.replace(old, new)
                with self.assertRaisesRegex(security.CheckError, 'source guard/API changed'):
                    self.inspect()
                self.sources[path] = original

    def test_identity_drift_and_missing_source_fail(self):
        path = next(iter(self.sources))
        self.sources[path] += b'// changed source\n'
        with self.assertRaisesRegex(security.CheckError, 'source identity changed'):
            self.inspect()
        del self.sources[path]
        with self.assertRaisesRegex(security.CheckError, 'missing or unknown'):
            self.inspect()

    def test_effect_anchor_fee_and_binding_mode_source_controls(self):
        controls = [
            ('crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs',
             b'action_anchor == context.anchor', b'true'),
            ('crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
             b'anchor: context.anchor,', b'anchor: transfer.body.anchor,'),
            ('crates/core/transaction/src/transaction.rs',
             b'state.update(fee_funding_hash.as_bytes());', b''),
            ('crates/core/transaction/src/transaction.rs',
             b'balance_commitments += fee_funding.balance_commitment().0;', b''),
            ('crates/core/component/fee/src/fee.rs', b'-Balance::from(self.0)', b'Balance::from(self.0)'),
            ('crates/core/app/src/action_handler/transaction/stateless.rs', b'tx.num_proofs() == 0,', b'true,'),
            ('crates/core/app/src/action_handler/transaction/stateless.rs',
             b'is_no_binding_signature(tx.binding_sig()),', b'true,'),
            ('crates/core/component/fee/src/component/fee_pay.rs',
             b'fee.asset_id() == *shieldd_sdk_asset::BASE_ASSET_ID,', b'true,'),
            ('crates/core/transaction/src/transaction.rs',
             b'.hash(&self.encode_to_vec())', b'.hash(&self.effect_hash().as_bytes())'),
        ]
        for path, old, new in controls:
            with self.subTest(path=path, guard=old):
                original = self.sources[path]
                self.assertEqual(original.count(old), 1)
                self.sources[path] = original.replace(old, new)
                with self.assertRaisesRegex(security.CheckError, 'source guard/API changed'):
                    self.inspect()
                self.sources[path] = original

    def test_effect_order_change_keeps_markers_but_fails_exact_source_identity(self):
        path = 'crates/core/transaction/src/transaction.rs'
        before = self.sources[path]
        params = b'state.update(parameters_hash.as_bytes());'
        fee = b'state.update(fee_funding_hash.as_bytes());'
        self.assertLess(before.index(params), before.index(fee))
        self.sources[path] = before.replace(params, b'REORDER_PLACEHOLDER').replace(fee, params).replace(b'REORDER_PLACEHOLDER', fee)
        with self.assertRaisesRegex(security.CheckError, 'source identity changed'):
            self.inspect()

    def test_current_envelope_framing_source_controls(self):
        path = 'crates/crypto/circuits/src/proof.rs'
        original = self.sources[path]
        for old, new in [
            (b'bytes.len() == ENCODED_LEN,', b'bytes.len() >= 73,'),
            (b'bytes[0] == SUITE,', b'true,'),
            (b'let family = Family::try_from(bytes[1])?;', b'let family = Family::Transfer;'),
            (b'ensure!(input.is_empty(), "trailing Pari proof bytes");', b''),
        ]:
            self.assertEqual(original.count(old), 1)
            self.sources[path] = original.replace(old, new)
            try:
                with self.subTest(guard=old), self.assertRaisesRegex(security.CheckError, 'source guard/API changed'):
                    self.inspect()
            finally:
                self.sources[path] = original

    def test_local_patch_source_precondition_controls(self):
        base = 'third_party/commonware/cryptography/src/zk/pari/'
        controls = [
            ('prover.rs', b'mask_vanishing(&a_mask, relation.size())', b'mask_vanishing(&a_mask, relation.size().ilog2() as usize)'),
            ('prover.rs', b'quotient.trim();', b''),
            ('prover.rs', b'if remainder != Poly::zero()', b'if false'),
            ('types.rs', b'self.public_inputs as usize == relation.public_inputs()', b'true'),
            ('types.rs', b'Ok(columns) if columns == self.public_columns', b'Ok(columns) if true'),
            ('circuit.rs', b'squared: other_base, linear: expression.clone(),', b'squared: other_base, linear: LinearCombination::zero(),'),
            ('circuit.rs', b'let copy = self.allocate(ValueSource::One)?;', b'let copy = self.allocate(ValueSource::Circuit(CircuitIdx::Constant(Scalar::zero())))?;'),
            ('circuit.rs', b'self.link_inputs()?; self.outline_constant()?;', b'self.outline_constant()?; self.link_inputs()?;'),
        ]
        for filename, old, new in controls:
            path = base + filename
            original = self.sources[path]
            with self.subTest(source=filename, guard=old):
                self.assertEqual(original.count(old), 1)
                self.sources[path] = original.replace(old, new)
                try:
                    with self.assertRaisesRegex(security.CheckError, 'source guard/API changed'):
                        self.inspect()
                finally:
                    self.sources[path] = original

    def test_effect_staging_and_savepoint_source_controls(self):
        controls = [
            ('crates/core/component/sct/src/component/tree.rs', b'local.insert(*nullifier),', b'true,'),
            ('crates/core/component/sct/src/component/tree.rs', b'!membership.contains(nullifier),', b'true,'),
            ('crates/core/component/sct/src/component/tree.rs', b'ensure!(!spent,', b'ensure!(true,'),
            ('crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs',
             b'inputs.iter().map(input_nullifier)', b'inputs.iter().take(1).map(input_nullifier)'),
            ('crates/core/component/shielded-pool/src/component/action_handler/note_reshape.rs',
             b'for output in outputs {', b'for output in outputs.iter().take(1) {'),
            ('crates/core/component/shielded-pool/src/component/action_handler/transfer.rs',
             b'if validated.proof_context == TransferProofContext::Ordinary',
             b'if validated.proof_context == TransferProofContext::FeeFunding'),
            ('crates/core/component/shielded-pool/src/component/shielded_pool.rs',
             b'!self.volume_nullifier_exists(day_start, nullifier).await?,', b'true,'),
            ('crates/core/component/compliance/src/admission.rs', b'snapshot.freeze_epoch != epoch', b'false'),
            ('crates/core/component/compliance/src/admission.rs', b'snapshot.user_root == *user && snapshot.asset_root == *asset,',
             b'snapshot.user_root == *user || snapshot.asset_root == *asset,'),
            ('crates/core/component/compliance/src/registry.rs', b'target_timestamp != 0,', b'true,'),
            ('third_party/cnidarium-0.83.0/src/delta.rs', b'Arc::get_mut(self).map(StateDelta::new)',
             b'Arc::get_mut(self).map(|state| state)'),
            ('crates/core/app/src/app/delivery.rs', b'let events = state_tx.apply().1;', b'let events = Vec::new();'),
        ]
        for path, old, new in controls:
            with self.subTest(path=path, guard=old):
                original = self.sources[path]
                self.assertEqual(original.count(old), 1)
                self.sources[path] = original.replace(old, new)
                try:
                    with self.assertRaisesRegex(security.CheckError, 'source guard/API changed'):
                        self.inspect()
                finally:
                    self.sources[path] = original

    def test_nullifier_staging_before_checks_and_deferred_index_before_apply_are_identity_drift(self):
        for path, first, second in [
            ('crates/core/component/sct/src/component/tree.rs', b'local.insert(*nullifier),',
             b'ordered.extend(nullifiers.iter().copied());'),
            ('crates/core/app/src/app/delivery.rs', b'let events = state_tx.apply().1;',
             b'self.deferred_block_transactions.push(transaction);'),
        ]:
            original = self.sources[path]
            self.sources[path] = original.replace(first, b'REORDER').replace(second, first).replace(b'REORDER', second)
            with self.subTest(path=path), self.assertRaisesRegex(security.CheckError, 'source identity changed'):
                self.inspect()
            self.sources[path] = original

    def test_signature_base_codec_and_honest_builder_source_controls(self):
        controls = [
            ('crates/crypto/primitives/src/generators.rs', b'SigningKey::<Binding>::try_from(one)',
             b'SigningKey::<SpendAuth>::try_from(one)'),
            ('crates/crypto/primitives/src/encoding.rs', b'Fr::from_bytes(bytes)', b'Fr::from_bytes_wide(bytes)'),
            ('crates/core/transaction/src/plan/build.rs', b'synthetic_blinding_factor += fee_funding.value_blinding();', b''),
            ('crates/core/transaction/src/plan/build.rs', b'supplied_effect_hash == transaction_effect_hash,', b'true,'),
            ('crates/core/transaction/src/plan/build.rs', b'spend_auths.next().is_none(),', b'true,'),
            ('crates/core/transaction/src/plan/build.rs',
             b'self.num_proofs() == 0 || !bool::from(synthetic_blinding_factor.is_zero()),', b'true,'),
        ]
        for path, old, new in controls:
            with self.subTest(path=path, guard=old):
                original = self.sources[path]
                self.assertEqual(original.count(old), 1)
                self.sources[path] = original.replace(old, new)
                with self.assertRaisesRegex(security.CheckError, 'source guard/API changed'):
                    self.inspect()
                self.sources[path] = original



if __name__ == '__main__':
    unittest.main()
