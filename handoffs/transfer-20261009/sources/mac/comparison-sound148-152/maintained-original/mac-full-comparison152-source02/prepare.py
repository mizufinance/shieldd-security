from pathlib import Path
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-full-comparison152-source01';S=W/'mac-full-comparison152-source02'
if S.exists():raise ValueError('fresh')
S.mkdir();t=(P/'template.lean').read_text().replace('variable {F : Type} [Field F] [CharP F p]','variable {F : Type} [Field F]').replace('theorem high_sound','variable [CharP F p]\ntheorem high_sound')
(S/'template.lean').write_text(t);(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
