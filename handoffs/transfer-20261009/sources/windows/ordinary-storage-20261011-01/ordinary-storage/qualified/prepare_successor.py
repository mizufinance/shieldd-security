"""Keep first Ordinary source immutable; type framing observations at the installed alias."""
from pathlib import Path
ROOT = Path(__file__).resolve().parent
BASE = ROOT.parent / 'transfer-ordinary-storage-source-20261011-01'
assert not (ROOT / 'prepare.py').exists()
source = (BASE / 'handwritten/TransferOrdinaryStorageSource01.lean').read_text()
before = '''    have frames := TransferRawSourceFrames01.reshape_preserves_input_write_domains
      (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
        volume sct treeKey volumeKey payload) notes sct wordMax capacity treeKey notesKey nullifierKey child inputs outputs'''
after = '''    have frames :
        (TransferRawEffectsSource01.reshape
          (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
          wordMax capacity nullifierKey child inputs outputs).cache.verifiable = child.cache.verifiable ∧
        (TransferRawEffectsSource01.reshape
          (installBoth raw notes volume sct available treeKey notesKey volumeKey payload entryKey)
          wordMax capacity nullifierKey child inputs outputs).cache.nonverifiable = child.cache.nonverifiable :=
      TransferRawSourceFrames01.reshape_preserves_input_write_domains
        (installVolume (TransferCurrentVolumeSource01.withVolumeRead raw available entryKey)
          volume sct treeKey volumeKey payload) notes sct wordMax capacity treeKey notesKey nullifierKey child inputs outputs'''
assert source.count(before) == 2
source = source.replace(before, after)
assert source.count('refine ⟨rfl, ?_, ?_, suffix.1.trans frames.2⟩') == 1
source = source.replace('refine ⟨rfl, ?_, ?_, suffix.1.trans frames.2⟩', 'refine ⟨True.intro, ?_, ?_, suffix.1.trans frames.2⟩')
handwritten = ROOT / 'handwritten/TransferOrdinaryStorageSource01.lean'
handwritten.parent.mkdir()
handwritten.write_text(source)
prepare = (BASE / 'prepare.py').read_text().replace('transfer-ordinary-storage-owned-floor-20261011-01', 'transfer-ordinary-storage-owned-floor-20261011-02')
prepare = prepare.replace("ROOT / 'prepare_recipe.py'", "ROOT / 'prepare_successor.py'")
prepare = prepare.replace('Fresh first source; symbolic all-return framing and whole success inversion with finite reusable lemmas; no guard or audit relaxation.',
    'Fresh successor explicitly types two reshape frame observations at installBoth before rewriting; closes simplified True with True.intro. All three program definitions and nine theorem contracts unchanged. Failed01 full zero credit. All guards and audits unchanged.')
(ROOT / 'prepare.py').write_text(prepare)
print({'fresh_reports': 12, 'definitions_and_contracts_unchanged': True, 'failed01_credit': 0})
