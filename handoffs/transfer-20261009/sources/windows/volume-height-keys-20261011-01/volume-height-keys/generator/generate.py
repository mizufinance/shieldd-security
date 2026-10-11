"""Emit exact ASCII constants from checked locked Rust key literal functions."""
import argparse
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent
def render(sct: str, pool: str) -> str:
    def literal(text, function):
        found = re.findall(r'pub fn ' + function + r'\(\) -> &\x27static str \{\s*"([^"\n]+)"\s*\}', text)
        assert len(found) == 1, function
        return found[0]
    height = literal(sct, 'block_height')
    volume_module = pool[pool.index('pub mod volume_nullifiers {'):pool.index('pub fn shielded_pool_params')]
    entry = literal(volume_module, 'prefix')
    day = literal(volume_module, 'day_marker_prefix')
    assert height == 'sct/block_manager/block_height'
    assert entry == 'shielded_pool/volume_nullifiers/entries/'
    assert day == 'shielded_pool/volume_nullifiers/days/'
    root = 'shielded_pool/volume_nullifiers/'
    template = (ROOT / 'source.lean.in').read_text()
    for name, value in {'HEIGHT': height, 'VOLUME_ROOT': root, 'ENTRIES': entry[len(root):], 'DAYS': day[len(root):]}.items():
        assert template.count('@@' + name + '@@') == 1
        template = template.replace('@@' + name + '@@', '[' + ', '.join(map(str, value.encode('ascii'))) + ']')
    names = re.findall(r'^(?:def|theorem) ([A-Za-z0-9_]+)', template, re.M)
    assert len(names) == 9 and '@@' not in template and '#check' not in template
    audits = '\n'.join('set_option pp.all true in\n#check @' + n + '\n#print axioms ' + n for n in names)
    return template.replace('\nend ShielddSecurity.TransferVolumeHeightKeys01', '\n' + audits + '\n\nend ShielddSecurity.TransferVolumeHeightKeys01')

if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--runtime-root', type=Path, default=Path('C:/src/shieldd-pr160-844389ee'))
    parser.add_argument('--output', type=Path, default=ROOT / 'portable-source/TransferVolumeHeightKeys01.lean')
    args = parser.parse_args()
    assert not args.output.exists()
    data = render((args.runtime_root / 'crates/core/component/sct/src/state_key.rs').read_text(),
        (args.runtime_root / 'crates/core/component/shielded-pool/src/state_key.rs').read_text())
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_bytes(data.encode('utf-8'))
    print({'public_declarations': 9, 'ascii_prefixes': 3, 'proof_credit': 0})
