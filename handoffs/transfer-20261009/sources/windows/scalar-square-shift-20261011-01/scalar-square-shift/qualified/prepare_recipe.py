from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-square-shift-20261011-03'
s=(OLD/'prepare_recipe.py').read_text()
s=s.replace("assert source.count('prefix')==3\nsource=source.replace('prefix','crossPrefix')","import re\nassert len(re.findall(r'\\bprefix\\b',source))==3\nsource=re.sub(r'\\bprefix\\b','crossPrefix',source)")
s=s.replace('transfer-scalar-square-shift-owned-floor-20261011-03','transfer-scalar-square-shift-owned-floor-20261011-04')
exec(compile(s,str(OLD/'prepare_recipe.py'),'exec'),{'__file__':str(ROOT/'prepare_recipe.py')})
s=(ROOT/'prepare.py').read_text();at=s.index("plan['artifact_policy']")
s=s[:at]+"unpreparedShiftRename=DIAG/'transfer-scalar-square-shift-20261011-03'\nassert not (unpreparedShiftRename/'plan.json').exists()\nplan['pins'].append(pin(unpreparedShiftRename/'prepare_recipe.py'))\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
