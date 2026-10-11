from pathlib import Path
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');P=W/'mac-high-comparison-sound149-source01';S=W/'mac-high-comparison-sound149-source02'
if S.exists():raise ValueError('fresh')
S.mkdir();t=(P/'template.lean').read_text().replace('⟨column,member,rfl⟩','⟨column,inColumns,rfl⟩').replace('at member','at inColumns').replace("List.mem_range'.mp member","List.mem_range'.mp inColumns")
(S/'template.lean').write_text(t);(S/'generate.py').write_bytes((P/'generate.py').read_bytes());(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
