"""Freeze the qualified domain-18 prefix for a read-only Opus review."""
import hashlib, json, re, shutil, subprocess, time
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[1]
S = ROOT / 'work/mac-poseidon-width3-call10'
P = S / 'project/ShielddSecurity'
F = HERE / 'frozen-prefix01'
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
assert not F.exists()
F.mkdir()
manifest = {}

def copy(src, dst):
    dst.parent.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(src, dst)
    assert sha(src) == sha(dst)
    manifest[str(dst.relative_to(F))] = {'source': str(src), 'sha256': sha(dst), 'bytes': dst.stat().st_size}

pending = ['TransferPoseidonWidth3Prefix10Program01']
seen = set()
while pending:
    name = pending.pop()
    if name in seen:
        continue
    seen.add(name)
    src = P / (name + '.lean')
    copy(src, F / 'ShielddSecurity' / src.name)
    pending.extend(re.findall(r'^import ShielddSecurity\.([A-Za-z0-9_]+)', src.read_text(), re.M))
for name in ['generate_direct.py', 'generate_absorption_proof.py', 'generate_prefix_program.py', 'generation_common.py', 'prefix_match.py', 'validate_records.py']:
    copy(S / name, F / name)
for src in sorted(S.glob('*.txt')):
    copy(src, F / src.name)
copy(HERE / 'data-audit01.json', F / 'parent-data-audit01.json')
(HERE / 'prefix-source-manifest01.json').write_text(json.dumps(manifest, indent=2) + '\n')
prompt = f'''Review the immutable frozen domain-18 width3 Poseidon prefix at {F}, read-only using Read/Glob/Grep. No edits, code execution, or builds. Focus on TransferPoseidonWidth3Prefix10AbsorbData01/AbsorbProof01, R00/R01 data/checkers/proofs, Prefix10Program01 and maintained generators/templates. Check actual native absorption with domain 18, arity 1, IV 274, one input LC cut 363983, zero padding; round 0 words 0 and 2 are native constants while word 1 is dynamic. Check both full rounds, actual coefficient/constant folding, proof checker soundness, same rho, rounds recurrence, finite checked row coverage and constructor preserving outside writes. There are 44 raw nodes, 26 constants, 16 arithmetic rows at 38876..38891 plus copy row 200769, 12 materialized steps plus one copy step, actual write support 61614..61629. Input LC contains six terms at 61592/61596/61600/61604/61608/61612. Constructor keeps original 22735 inputs, zero/copy and cut values. Arbitrary two-round theorem explicitly assumes Field/CharP p, rho 0 = 1, 4 != 0, and satisfaction of exact selected rows; constructor explicitly assumes copy linked to zero. Do not confuse these premises with native/deployment closure. Parent independently checked the DB nodes/constants/cuts/rows and actual parameter bytes against descriptor SHA 01b68f32bf6896a6122805713cdd5448105d2aab2da056699c9d35dd57f162ff and matching round-1/suffix data boundary. That is DATA, not a new kernel claim. The stable prefix modules passed worker audits, but parent receipt reconstruction is still pending. Whole-call composition/page endpoints are deliberately outside this review and still in development. Full Transfer, all 210 permutations, upstream input derivation, global 200770 parent-row frame, raw/native association remain OPEN. Prior imported helpers are accepted context. Review for soundness, hidden premises, incorrect recurrence/count/state index, accidentally assumed boundary or coefficients, and misleading scope. Review matcher controls as data qualification only. Return actionable defects with file evidence or no defect in this exact prefix scope.'''
(HERE / 'prefix-review-prompt01.txt').write_text(prompt + '\n')
started = time.monotonic()
cmd = ['/Users/antoinecyr/.local/bin/claude', '--model', 'claude-opus-5-5', '--effort', 'high', '--permission-mode', 'plan', '--tools', 'Read,Glob,Grep', '--strict-mcp-config', '--no-session-persistence', '--output-format', 'json', '--print', prompt]
with (HERE / 'prefix-opus55-review01.json').open('w') as out, (HERE / 'prefix-opus55-review01.stderr').open('w') as err:
    r = subprocess.run(cmd, stdout=out, stderr=err, timeout=900)
j = json.loads((HERE / 'prefix-opus55-review01.json').read_text())
assert r.returncode == 0 and not j['is_error'] and 'claude-opus-5-5' in j['modelUsage']
assert all(sha(F / name) == record['sha256'] for name, record in manifest.items())
print(json.dumps({'review': 'complete', 'files': len(manifest), 'seconds': time.monotonic() - started, 'model': list(j['modelUsage'])}))
