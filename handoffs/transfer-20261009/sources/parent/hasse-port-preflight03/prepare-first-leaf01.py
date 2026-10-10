"""Expose one exact unbuilt foreign leaf for a bounded compatibility admission plan."""
import sys
assert sys.flags.isolated and sys.flags.dont_write_bytecode and sys.flags.no_site
import hashlib,json,shutil
from pathlib import Path
H=Path(__file__).resolve().parent;R=H.parents[1];REPO=R/'work/shared-build-handoff';P=R/'work/parent-hasse-port-preflight03/prepared'
BASE=REPO/'handoffs/transfer-20261009/sources/parent/hasse-port-preflight03'
sha=lambda p:hashlib.sha256(p.read_bytes()).hexdigest()
manifest=BASE/'prepared-manifest.json';m=json.loads(manifest.read_bytes())
assert m['external_commit']=='ce9417a37c7a74fa60a3e05f6d85392c2e8a0618' and m['kernel_run'] is False
name='HasseWeil.Foundation.Auxiliary.EllipticDivisibilitySequence';x=m['sources'][name]
src=P/x['relative_path'];license=P/'LICENSE';assert sha(src)==x['original_sha256']==x['prepared_sha256']=='52cd8d1e4597b321ffea64635e45f109455142016d3ea5460c1399716e45fbd8'
assert src.stat().st_size==46499 and not x['changed'] and sha(license)==m['license_sha256']=='b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1'
preflight=json.loads((BASE/'preflight.json').read_bytes());assert preflight['source_nodes'][name]['owned_imports']==[]
out=H/'packet';assert not out.exists();out.mkdir()
for p,n in [(src,x['relative_path']),(license,'LICENSE')]:
 dst=out/n;dst.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(p,dst)
scope=dict(kind='unbuilt-exact-single-foreign-leaf-source-transport',module=name,external_commit=m['external_commit'],prepared_manifest_sha256=sha(manifest),source_sha256=sha(src),source_bytes=46499,license_sha256=sha(license),owned_imports=[],external_imports=preflight['source_nodes'][name]['external_imports'],source_changed=False,additional_prepared_sources_needed_for_this_leaf=0,remaining_foreign_sources=186,kernel_runs=0,kernel_credit=0,admission='Not admitted; Windows must resolve qualified exact-pin Mathlib artifact closure and complete finite budget plan',foreign_toolchain='4.35.0-rc4 is source provenance only; campaign stays Lean4.30.0',full_transfer='OPEN')
(out/'scope01.json').write_text(json.dumps(scope,indent=2)+'\n')
files={str(p.relative_to(out)):dict(sha256=sha(p),bytes=p.stat().st_size) for p in out.rglob('*') if p.is_file()}
(out/'manifest01.json').write_text(json.dumps(dict(files=files,scope=scope),indent=2)+'\n')
print(json.dumps(dict(status='passed_source_only',files=len(files),module=name,kernel_runs=0)))
