from pathlib import Path
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-square-shift-20261011-01'
assert not (ROOT/'prepare.py').exists()
(ROOT/'handwritten').mkdir()
(ROOT/'handwritten/TransferScalarSquareShift01.lean').write_bytes((OLD/'handwritten/TransferScalarSquareShift01.lean').read_bytes())
s=(OLD/'prepare_recipe.py').read_text().replace("body.index('        // Add')","body.index('        let (r0, carry) =')").replace('transfer-scalar-square-shift-owned-floor-20261011-01','transfer-scalar-square-shift-owned-floor-20261011-02')
exec(compile(s,str(OLD/'prepare_recipe.py'),'exec'),{'__file__':str(ROOT/'prepare_recipe.py')})
s=(ROOT/'prepare.py').read_text()
at=s.index("plan['artifact_policy']")
s=s[:at]+"unpreparedShift=DIAG/'transfer-scalar-square-shift-20261011-01'\nassert not (unpreparedShift/'plan.json').exists()\nplan['pins'] += [pin(unpreparedShift/n) for n in ['prepare_recipe.py','handwritten/TransferScalarSquareShift01.lean']]\n"+s[at:]
(ROOT/'prepare.py').write_text(s)
