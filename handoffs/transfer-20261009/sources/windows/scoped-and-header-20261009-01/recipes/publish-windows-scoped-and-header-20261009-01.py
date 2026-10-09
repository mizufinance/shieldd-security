from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, subprocess, sys

repo = Path('C:/src/shieldd-transfer-windows-publication-20261009')
local = Path('C:/src/shieldd-transfer-handoffs')
diag = Path('C:/src/shieldd-formal/.work/diagnostics/transfer-implementation-20261002')
base = repo / 'handoffs/transfer-20261009'
dest = base / 'sources/windows/scoped-and-header-20261009-01'
packets = {'scoped': local / 'windows-scoped-field-knowledge-20261009-02-packet',
           'header': local / 'windows-header-carrier-20261009-01-packet'}
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
load = lambda p: json.loads(p.read_text(encoding='utf-8-sig'))
write = lambda p, value: p.write_bytes((json.dumps(value, indent=2) + '\n').encode())
phase = sys.argv[1]
if phase == 'sources':
    assert not dest.exists()
    dest.mkdir(parents=True)
    files = {}
    def copy(p, rel):
        target = dest / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        target.write_bytes(p.read_bytes())
        assert sha(p) == sha(target)
        files[rel] = {'sha256': sha(target), 'bytes': target.stat().st_size}
    for label, packet in packets.items():
        manifest = load(packet / 'manifest.json')
        for rel, expected in manifest['files'].items():
            assert sha(packet / rel) == expected['sha256']
            if rel != 'receipt.json':
                copy(packet / rel, label + '/' + rel)
    resolution = {}
    for label in packets:
        source_manifest = load(dest / label / 'inputs/manifest.json')
        closure = {}
        for name, identity in source_manifest['sources'].items():
            candidates = [dest / label / 'circuits/ShielddSecurity' / (name + '.lean'),
                repo / 'circuits/ShielddSecurity' / (name + '.lean'),
                base / 'sources/windows/maintained-review-20261009-01/formal/circuits/ShielddSecurity' / (name + '.lean')]
            matches = [p for p in candidates if p.exists() and sha(p) == identity['sha256']]
            assert matches, ('exact transported dependency required', label, name)
            closure[name] = {'path': str(matches[0].relative_to(repo)).replace('\\', '/'),
                             'sha256': identity['sha256']}
        resolution[label] = closure
    write(dest / 'dependency-resolution.json', resolution)
    files['dependency-resolution.json'] = {'sha256': sha(dest / 'dependency-resolution.json'), 'bytes': (dest / 'dependency-resolution.json').stat().st_size}
    roster = {
        'scoped_root': {'module': 'TransferScopedFieldClaimAcceptance',
            'definition_constructor_audits': ['FieldClaim', 'UpstreamFieldKnowledge.mk', 'OwnedRange'],
            'theorems': ['promote_field_claim', 'expected_statement_canonical', 'verified_field_claims',
                'preparation_compiled_claims_from_field_knowledge', 'preparation_semantic_or_collision_from_field_knowledge',
                'full_carrier_consequence_from_field_knowledge'],
            'changed_boundary': 'Individual extraction requires item.family=input.family and relation=input.key.key.relationDigest. Batch extraction requires the same for its first item and relation. verified_field_claims extracts only an expected-family item, derives exact relation from registry selection, and preparation obtains that selection from checked Policy.',
            'residual_premises': ['Primitive individual and randomized-batch field knowledge for the exact selected family/relation',
                'CanonicalCrypto and deployed field/codec/opening interpretation',
                'OwnedRange supplied by the existing indexed owned-range bridge only after concrete IndexedCoverage',
                'Independent full LocalRowSoundness for semantic/collision and full-carrier conclusions',
                'Native/Rust interpretation of decoder, compiler relation, verification, model and durable state'],
            'same_owned_range_predicate': 'Definitionally identical to the original field bridge; no subgroup bound added to backend knowledge.'},
        'header_join': {'module': 'TransferCircuitHeaderCarrierSeed',
            'theorems': ['private_inputs_preserved', 'blinding_private_input', 'committed_private_blinding_link',
                'claimed_statement_private_input', 'public_private_statement_link', 'header_rows_complete'],
            'conclusion': 'Construct eight header input values and final claimed statement; preserve all supplied private input values at columns3+i; derive two role links and satisfy four expected local rows.',
            'residual_premises': ['Structured independently legal semantic construction inputs',
                '22726 remaining gadget input values still supplied and not proved legal',
                'Exact pinned compiler input/column/data instance and indexed full-row inclusion',
                'Materialized output and auxiliary construction with concrete Topological/Legal and reverse row coverage',
                'Complete graph assertions, graph-to-TransferSem and Rust constructor correspondence'],
            'no_extra_boolean_input_or_satisfied_row_premise': True},
        'full_transfer': 'OPEN', 'native_successors': 'SOURCE_PREPARED_UNRUN'}
    write(dest / 'review-roster.json', roster)
    files['review-roster.json'] = {'sha256': sha(dest / 'review-roster.json'), 'bytes': (dest / 'review-roster.json').stat().st_size}
    copy(Path(__file__), 'recipes/' + Path(__file__).name)
    for p in [local / 'prepare-windows-scoped-field-packet-20261009-01.py', local / 'prepare-windows-header-carrier-packet-20261009-01.py']:
        copy(p, 'recipes/' + p.name)
    write(dest / 'manifest.json', {'files': files, 'runtime_sha': load(packets['header']/'receipt.json')['runtime_sha'],
        'scope': 'Exact successor sources, local check recipes and bounded source/input identities. Audit receipts published separately. No raw logs, objects, caches or certification evidence.', 'full_transfer': 'OPEN'})
    print(json.dumps({'files': len(files), 'manifest_sha256': sha(dest/'manifest.json')}))
elif phase == 'verify-index':
    for rel, identity in load(dest/'manifest.json')['files'].items():
        path = str((dest/rel).relative_to(repo)).replace('\\','/')
        raw = subprocess.check_output(['git','-C',str(repo),'show',':'+path])
        assert hashlib.sha256(raw).hexdigest() == identity['sha256'],path
    print('Exact source Git index bytes PASS')
elif phase == 'receipts':
    source_commit = subprocess.check_output(['git','-C',str(repo),'rev-parse','HEAD'],text=True).strip()
    refs = {}
    for label, packet in packets.items():
        receipt = load(packet/'receipt.json')
        receipt.update({'publication': 'EXACT_SOURCE_COMMIT_AND_ACTUAL_CHECK_RECEIPTS', 'source_commit': source_commit,
            'source_packet': str(dest.relative_to(base)).replace('\\','/'), 'source_manifest_sha256': sha(dest/'manifest.json'),
            'producer_manifest_sha256': sha(packet/'manifest.json'), 'producer_receipt_sha256': sha(packet/'receipt.json'),
            'source_index_exact_bytes_verified': True,
            'source_diff_check': 'FAILED_FROZEN_PRODUCER_SOURCE_TERMINAL_CRLF_BLANK_LINES; exact checked Lean and recipe bytes retained'})
        p = base / f'receipts/windows/{label}-successor-20261009-01.json'
        assert not p.exists()
        write(p,receipt)
        refs[label] = {'path':str(p.relative_to(base)).replace('\\','/'),'sha256':sha(p)}
    status_path = base / 'status/windows.json'
    status = load(status_path)
    journal = load(diag/'root-dh-primary-joint-after-initialization-2516-successor-3130/journal.json')
    status['snapshot_utc'] = datetime.now(timezone.utc).isoformat()
    status['synchronized_origin_sha'] = 'f8911398a91399329c9b77a6085dc15994372923'
    status['active_controller'].update({'settled_dh_phases':len(journal),
        'settled_dh_modules':sum(x.get('modules',0) for x in journal),
        'settled_dh_audits':sum(x.get('exports',0) for x in journal),
        'whole_root_complete':(diag/'root-field-native-epk-cast-repair-3130/complete.txt').exists()})
    status['checked_successors_20261009_01'] = {'source_commit':source_commit, 'receipts':refs,
        'scoped_root_audits':9, 'scoped_root_theorems':6,'scoped_root_definition_constructor_audits':3,
        'scoped_dependency_replays':242,'header_new_theorems':6,'header_prerequisite_replays':23,
        'safe_resume_status':[0,0],'review_roster':str((dest/'review-roster.json').relative_to(base)).replace('\\','/'),
        'full_transfer':'OPEN'}
    status['native_3057_3060'] = 'SOURCE_PREPARED_UNRUN; prepare a fresh coordinator only after actual whole3130 success and actual statement3117 success'
    write(status_path,status)
    print(json.dumps({'source_commit':source_commit,'receipts':refs,'settled_dh_phases':len(journal)}))
else:
    raise ValueError(phase)
