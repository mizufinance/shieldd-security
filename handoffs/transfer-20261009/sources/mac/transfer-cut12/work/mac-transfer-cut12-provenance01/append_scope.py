"""Append-only review scope disposition; preserves all previous sealed bytes."""
import hashlib,json
from pathlib import Path
S=Path(__file__).resolve().parent;R=S.parents[1]
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
producer=R/'outputs/mac-transfer-cut12/publication-manifest01.json'
envelope=R/'outputs/mac-transfer-cut12/seal-envelope01.json'
successor=S/'successor-manifest01.json'
assert sha(producer)=='cf1511163550fb7e788df052bdef1837dd464f5cc7a0d6b17ab19f07f27f5a45'
assert sha(envelope)=='288dd9601abaf54a7418e5f6ec3c0011efb742ebea827cbf31dab0902d2363ce'
assert sha(successor)=='5e22357bd13c6eb325d2608db5416874e06d444c00c781c27643274c8016d3f2'
previous={**json.loads(producer.read_text())['files'],**json.loads(envelope.read_text())['entries'],**json.loads(successor.read_text())['files']}
for relative,identity in previous.items():assert sha(R/relative)==identity['sha256']
scope=S/'scope-addendum01.json';assert not scope.exists()
scope.write_text(json.dumps(dict(schema='cut12-append-only-scope-correction-v1',
    disposition='Supersedes imprecise control/checker scope wording in original metadata; no change to historical theorem names, proof sources, objects, kernel outcomes or counts.',
    control_count=dict(production_checker_refusals=6,mapping_size_component_refusals=1,positive=1),
    reverse_component_rejected=dict(historical_theorem_name='ShielddSecurity.TransferCut12Controls01.reverse_component_rejected',
        precise_scope='Mapping-size component refusal: four mapping entries versus five original rows.',
        does_not_establish='Not bidirectional or reverse-coverage semantics; not a missing-row completeness counterexample.'),
    addChecks=dict(precise_scope='Fixed source-syntax Boolean independent of candidateRows; checked_fields discards this conjunct.',
        classification='Fixed syntax/data check only',
        not_claimed=['mutable candidate guard component','separately targeted control']),
    theorem_boundaries=dict(checked_cut_values='Parametric checked bridge proves the two cut formulas.',
        source_node_values='Separate fixed source theorem proves all six expression values.'),
    census=dict(root_new_modules=3,root_new_audits=39,root_inherited_owned_modules=308,root_total_owned_modules=311,
        all_stage_fresh_modules=7,all_stage_audits=61,root_vs_all_stage='Probes and checker/control modules are separate from the three-module mathematical root closure.'),
    review=dict(parent_report='work/parent-cut12-review01/opus55-review.json',reported_model='actual Claude Opus5.5 high',
        reported_result='No new mathematical, soundness or construction defect; exact scope labels corrected by this addendum.',
        evidence_basis='Trusted parent review relay; no new review process or kernel execution by worker'),
    new_kernel_runs=0,original_proof_bytes_unchanged=True,
    open=['larger parent page/full200770 formal rowAt','native/rawconsumer/callsite identity','later consumer preservation','whole joined candidate checker','fullTransfer']),indent=2)+'\n')
for relative,identity in previous.items():assert sha(R/relative)==identity['sha256']
p=S/'scope-binding-envelope01.json';assert not p.exists()
entries={str(x.relative_to(R)):dict(sha256=sha(x),bytes=x.stat().st_size,classification='append-only scope metadata; zero new kernel credit') for x in [Path(__file__),scope]}
p.write_text(json.dumps(dict(schema='cut12-scope-binding-envelope-v1',
    original_producer=dict(path=str(producer.relative_to(R)),sha256=sha(producer)),
    original_envelope=dict(path=str(envelope.relative_to(R)),sha256=sha(envelope)),
    provenance_successor=dict(path=str(successor.relative_to(R)),sha256=sha(successor)),
    previous_entry_paths_rehashed_unchanged=len(previous),entries=entries,
    scope='Append-only actual-review label correction; original83sealedpaths plus9provenance-successorpaths unchanged'),indent=2)+'\n')
print(json.dumps(dict(scope_path=str(scope),scope_sha256=sha(scope),binding_path=str(p),binding_sha256=sha(p),previous_paths_unchanged=len(previous))))
