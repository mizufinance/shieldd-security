from pathlib import Path
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-comparison-sound148-source02';S=W/'mac-comparison-sound148-source03'
if S.exists():raise ValueError('fresh')
S.mkdir();t=(P/'template.lean').read_text().replace('import ShielddSecurity.LexicographicComparison144','import ShielddSecurity.LexicographicComparison144\nimport ShielddSecurity.CapturedEpochHints62')
(S/'template.lean').write_text(t);(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
