from pathlib import Path
import runpy
ROOT=Path(__file__).resolve().parent;DIAG=ROOT.parent
OLD=DIAG/'transfer-scalar-inverse-correctness-20261012-01'
assert not (ROOT/'prepare.py').exists() and not (ROOT/'prepare_recipe_from01.py').exists()
assert not (OLD/'prepare.py').exists() and not (OLD/'context').exists()
source=(OLD/'handwritten/TransferScalarInverseCorrectness01.lean').read_text()
assert source.count('import Mathlib.FieldTheory.Finite.Basic')==1
assert source.count('  have fermat := ZMod.pow_card_sub_one_eq_one positive')==1
source=source.replace('import Mathlib.FieldTheory.Finite.Basic','import Mathlib.Data.Fintype.Units\nimport Mathlib.GroupTheory.OrderOfElement')
source=source.replace('  have fermat := ZMod.pow_card_sub_one_eq_one positive', '''  let unit : (ZMod nullifierModulus)ˣ := Units.mk0 (base : ZMod nullifierModulus) positive
  have cardinality : Fintype.card (ZMod nullifierModulus)ˣ = nullifierModulus - 1 := by
    rw [Fintype.card_units, ZMod.card]
  have unitPower : unit ^ (nullifierModulus - 1) = 1 := by
    rw [← cardinality]
    exact pow_card_eq_one
  have fermat := congrArg (fun u : (ZMod nullifierModulus)ˣ => (u : ZMod nullifierModulus)) unitPower
  change (base : ZMod nullifierModulus) ^ (nullifierModulus - 1) = 1 at fermat''')
(ROOT/'handwritten').mkdir();(ROOT/'handwritten/TransferScalarInverseCorrectness01.lean').write_text(source)
recipe=(OLD/'prepare_recipe.py').read_text()
recipe=recipe.replace("POOL = DIAG / 'transfer-scalar-inverse-correctness-owned-floor-20261012-01'","POOL = DIAG / 'transfer-scalar-inverse-correctness-owned-floor-20261012-02'")
assert recipe.count("assert 'Mathlib.FieldTheory.Finite.Basic' in json.loads(floor.read_text())['modules']")==1
recipe=recipe.replace("assert 'Mathlib.FieldTheory.Finite.Basic' in json.loads(floor.read_text())['modules']","assert {'Mathlib.Data.Fintype.Units','Mathlib.GroupTheory.OrderOfElement'} <= set(json.loads(floor.read_text())['modules'])")
assert recipe.count("'Mathlib.FieldTheory.Finite.Basic']")==1
recipe=recipe.replace("'Mathlib.FieldTheory.Finite.Basic']","'Mathlib.Data.Fintype.Units', 'Mathlib.GroupTheory.OrderOfElement']")
marker="(ROOT/'prepare.py').write_text(s)"
assert recipe.count(marker)==1
addition="""extraHistory="plan['pins'] += [pin(DIAG/'transfer-scalar-inverse-correctness-20261012-01/prepare_recipe.py'),pin(DIAG/'transfer-scalar-inverse-correctness-20261012-01/handwritten/TransferScalarInverseCorrectness01.lean'),pin(ROOT/'prepare_recipe_from01.py')]\\n"
at=s.index("plan['artifact_policy']")
s=s[:at]+extraHistory+s[at:]
"""
recipe=recipe.replace(marker,addition+marker)
(ROOT/'prepare_recipe_from01.py').write_text(recipe)
runpy.run_path(str(ROOT/'prepare_recipe_from01.py'),run_name='__main__')
