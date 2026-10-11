from pathlib import Path
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-zero-flag-sound155-source01';S=W/'mac-zero-flag-sound155-source02'
if S.exists():raise ValueError('fresh')
S.mkdir();t=(P/'template.lean').read_text().replace('theorem first_delta','omit [CharP F p] in\ntheorem first_delta').replace('theorem next_delta','omit [CharP F p] in\ntheorem next_delta')
(S/'template.lean').write_text(t);(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
