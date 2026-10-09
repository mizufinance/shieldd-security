from pathlib import Path
import argparse, hashlib, json, re

p = argparse.ArgumentParser()
for name in ['candidate', 'generated-source-dir', 'reference-source-dir', 'producer', 'record', 'scalar-source', 'output']:
    p.add_argument('--' + name, required=True)
args = p.parse_args()
sha = lambda f: hashlib.sha256(f.read_bytes()).hexdigest()
candidate = Path(args.candidate)
assert sha(candidate) == '028924209b34a15720e93083253a54b4fe2f759bd19e93e43fdf2707c576096c'
data = json.loads(candidate.read_text())
record = json.loads(Path(args.record).read_text())
assert record['candidate_sha256'] == sha(candidate) and record['producer_sha256'] == sha(Path(args.producer))
assert [s['step_index'] for s in record['steps']] == list(range(3, 252))
sources = {}
for step in record['steps']:
    name = step['module'] + '.lean'
    generated, reference = Path(args.generated_source_dir) / name, Path(args.reference_source_dir) / name
    assert generated.read_bytes() == reference.read_bytes()
    assert sha(generated) == step['source_sha256']
    sources[name] = {'sha256': sha(reference), 'bytes': reference.stat().st_size}
scalar = Path(args.scalar_source)
matched = re.search(r'^def order : Nat := (\d+)\s*$', scalar.read_text(), re.M)
assert matched is not None
order = int(matched.group(1))
final = data['steps'][251]
base_x, base_y = data['base']
double_x, double_y = final['doubling']['after']
checks = {'final_same_x': double_x == base_x,
          'final_opposite_y': (double_y + base_y) % data['p'] == 0,
          'final_prefix_equals_candidate_r': final['prefix'] == data['r'],
          'final_prefix_equals_Scalar_order': final['prefix'] == order,
          'final_addition_case_inverse': final['addition']['case'] == 'inverse',
          'final_addition_infinity_post_state': final['addition']['after'] is None,
          'final_step_infinity_post_state': final['after'] is None}
assert all(checks.values())
out = Path(args.output)
assert not out.exists()
out.parent.mkdir(parents=True, exist_ok=True)
result = {'marker': 'TRANSFER_POINT_TRACE_PORTABLE_BYTE_REPLAY_DATA_V1',
          'producer_sha256': sha(Path(args.producer)), 'verifier_sha256': sha(Path(__file__)),
          'generation_record_sha256': sha(Path(args.record)), 'candidate_sha256': sha(candidate),
          'scalar_source_sha256': sha(scalar), 'modules_byte_exact': len(sources), 'source_identities': sources,
          'independently_checked_final_branch_data': checks,
          'final_branch_values': {'candidate_step_index': 251, 'base_x': base_x, 'base_y': base_y,
                                 'double_x': double_x, 'double_y': double_y,
                                 'prefix': final['prefix'], 'Scalar_order': order, 'field_modulus': data['p'],
                                 'addition_post_state': final['addition']['after'], 'step_post_state': final['after']},
          'classification': 'DATA/byte identity only; hash replay and Python arithmetic establish no kernel theorem',
          'new_kernel_credit': 0, 'new_control_credit': 0, 'full_transfer': 'OPEN'}
out.write_bytes((json.dumps(result, indent=2) + '\n').encode())
print(json.dumps({'marker': result['marker'], 'modules_byte_exact': len(sources),
                  'final_branch_data_checks': checks, 'record_sha256': sha(out),
                  'new_kernel_credit': 0, 'new_control_credit': 0}))
