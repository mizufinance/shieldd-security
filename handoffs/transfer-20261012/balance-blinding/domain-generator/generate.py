from pathlib import Path
import json,sys
root=Path(__file__).resolve().parent;out=Path(sys.argv[1]);out.mkdir();dest=out/'source-root/ShielddSecurity';dest.mkdir(parents=True);data=json.loads((root/'points.json').read_text());s=(root/'template.lean.in').read_text().replace('BASE_X',str(data['base'][0])).replace('BASE_Y',str(data['base'][1]));(dest/'BalanceBlindingDomain670.lean').write_text(s);print('Generated670 fixed blinding point domain; unrun')
