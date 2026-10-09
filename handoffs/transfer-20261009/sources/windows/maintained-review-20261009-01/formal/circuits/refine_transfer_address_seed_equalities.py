"""Prove seed/copy links through local assignment bindings explicitly."""


def generate(source):
    old = ('    rw [RuntimeOwnershipNativeEndpoint.seed_preserves fq fr model upstream backend sender scalar base 200692 (by decide),\n'
           '      RuntimeOwnershipNativeEndpoint.seed_preserves fq fr model upstream backend sender scalar base 0 (by decide),linked]')
    new = ('    exact (RuntimeOwnershipNativeEndpoint.seed_preserves fq fr model upstream backend sender scalar base 200692 (by decide)).trans\n'
           '      (linked.trans (RuntimeOwnershipNativeEndpoint.seed_preserves fq fr model upstream backend sender scalar base 0 (by decide)).symm)')
    assert source.count(old) == 1
    source = source.replace(old, new)
    old = ('    rw [RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y seed 200692 (by simp),\n'
           '      RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y seed 0 (by simp),seedLink]')
    new = ('    exact (RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y seed 200692 (by simp)).trans\n'
           '      (seedLink.trans (RuntimeOwnershipNativeConstructor.ivk_constants fq backend codec nk x y seed 0 (by simp)).symm)')
    assert source.count(old) == 1
    return source.replace(old, new)
