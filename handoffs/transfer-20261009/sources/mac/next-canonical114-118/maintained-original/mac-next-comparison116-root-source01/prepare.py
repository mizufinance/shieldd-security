from pathlib import Path
import re
W=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work');S=W/'mac-next-comparison116-root-source01';A=W/'mac-asset-comparison111-root-source01'
if S.exists():raise ValueError('immutable root')
S.mkdir();t=(A/'template.lean').read_text().replace('AssetComparison111','NextComparison116').replace('AssetComparison110','NextComparison115').replace('NextComparison115Numeric','AssetComparison110Numeric').replace('NextComparison115.selected_numeric','AssetComparison110.selected_numeric')
nums={471:726,725:980,33260:33768}
t=re.sub(r'\b(?:'+'|'.join(map(str,nums))+r')\b',lambda m:str(nums[int(m[0])]),t);(S/'template.lean').write_text(t)
g=(A/'generate.py').read_text().replace('AssetComparison111','NextComparison116').replace('Only actual asset508 arithmetic row transport','Only actual nextValue508 arithmetic row transport');(S/'generate.py').write_text(g);(S/'prepare.py').write_bytes(Path(__file__).read_bytes())
