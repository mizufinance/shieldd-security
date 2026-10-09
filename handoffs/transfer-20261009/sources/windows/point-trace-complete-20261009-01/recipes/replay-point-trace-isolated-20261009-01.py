from pathlib import Path
import argparse, hashlib, json, subprocess, sys

p = argparse.ArgumentParser()
for name in ['candidate', 'scalar-source', 'reference-source-dir', 'generator', 'verifier', 'fresh-root', 'receipt']:
    p.add_argument('--' + name, required=True)
args = p.parse_args()
assert sys.flags.isolated and sys.flags.no_site and sys.flags.dont_write_bytecode, 'Supported invocation requires Python -I -B -S'
sha = lambda path: hashlib.sha256(path.read_bytes()).hexdigest()
candidate, scalar = Path(args.candidate).resolve(), Path(args.scalar_source).resolve()
generator, verifier = Path(args.generator).resolve(), Path(args.verifier).resolve()
assert sha(candidate) == '028924209b34a15720e93083253a54b4fe2f759bd19e93e43fdf2707c576096c'
assert sha(generator) == 'e21f62db7ccd9d6431ad0a9e3c7102a6e206ba150b5237608c314425d02774ad'
fresh, receipt = Path(args.fresh_root).resolve(), Path(args.receipt).resolve()
assert not fresh.exists() and not receipt.exists()
fresh.mkdir(parents=True)
output_root, records_root = fresh / 'generated', fresh / 'generation-records'
verification = fresh / 'byte-replay-data.json'
command_generator = [sys.executable, '-I', '-B', '-S', str(generator), '--candidate', str(candidate),
                     '--output-root', str(output_root), '--records-root', str(records_root), '--start', '3', '--end', '251']
command_verifier = [sys.executable, '-I', '-B', '-S', str(verifier), '--candidate', str(candidate),
                    '--generated-source-dir', str(output_root / 'circuits/ShielddSecurity'),
                    '--reference-source-dir', str(Path(args.reference_source_dir).resolve()),
                    '--producer', str(generator), '--record', str(records_root / 'point-trace-generation-20261009-01-003-251.json'),
                    '--scalar-source', str(scalar), '--output', str(verification)]
outputs = []
for command in [command_generator, command_verifier]:
    result = subprocess.run(command, check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    outputs.append({'argv': command, 'exit': result.returncode,
                    'stdout_sha256': hashlib.sha256(result.stdout).hexdigest(),
                    'stderr_sha256': hashlib.sha256(result.stderr).hexdigest()})
data = json.loads(verification.read_text())
assert data['modules_byte_exact'] == 249 and data['new_kernel_credit'] == 0 and data['new_control_credit'] == 0
assert all(data['independently_checked_final_branch_data'].values())
inventory = [{'role': role, 'sha256': sha(path), 'bytes': path.stat().st_size}
             for role, path in [('supported_recipe', Path(__file__)), ('generator', generator), ('verifier', verifier),
                                ('candidate_input', candidate), ('Scalar_source', scalar)]]
result = {'marker': 'TRANSFER_POINT_TRACE_SUPPORTED_ISOLATED_REPLAY_DATA_V1',
          'supported_entry_flags': ['-I', '-B', '-S'], 'python_version': sys.version,
          'python_executable_sha256': sha(Path(sys.executable)),
          'recipe_sha256': sha(Path(__file__)), 'source_input_inventory': inventory,
          'source_input_inventory_sha256': hashlib.sha256(json.dumps(inventory, separators=(',', ':'), sort_keys=True).encode()).hexdigest(),
          'supported_commands': outputs, 'fresh_output_root': str(fresh),
          'byte_verification_sha256': sha(verification), 'modules_byte_exact': 249,
          'final_branch_data_checks': data['independently_checked_final_branch_data'],
          'import_provenance': 'Isolated/no-site/no-pyc supported CLI; no script-directory, CWD, PYTHON environment, site or unlisted bootstrap helpers',
          'classification': 'DATA/byte identity only; no kernel or semantic-control credit',
          'new_kernel_credit': 0, 'new_control_credit': 0, 'full_transfer': 'OPEN'}
receipt.parent.mkdir(parents=True, exist_ok=True)
receipt.write_bytes((json.dumps(result, indent=2) + '\n').encode())
print(json.dumps({'marker': result['marker'], 'receipt_sha256': sha(receipt),
                  'source_input_inventory_sha256': result['source_input_inventory_sha256'],
                  'modules_byte_exact': 249, 'flags': ['-I', '-B', '-S'], 'new_kernel_credit': 0, 'new_control_credit': 0}))
