from pathlib import Path
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-boolean-decode150-source02';S=W/'mac-boolean-decode150-source03'
if S.exists():raise ValueError('fresh')
S.mkdir();t=(P/'template.lean').read_text().replace('    cases bit <;> simp [encodeBits,binary,ih]','    have half : (1+2*binary bits)/2=binary bits := by omega\n    cases bit <;> simp [encodeBits,binary,ih,half]')
(S/'template.lean').write_text(t);(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
