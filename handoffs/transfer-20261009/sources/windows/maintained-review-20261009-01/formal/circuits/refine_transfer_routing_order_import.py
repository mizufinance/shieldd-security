"""Repair coherent imports and membership in the left-associated row union."""
def generate(module,source):
    assert module in ['RuntimeRoutingBitTheory','RuntimeRoutingOrderActiveJoin']
    if module=='RuntimeRoutingOrderActiveJoin':
        # Lean parses A ++ B ++ pages as (A ++ B) ++ pages.  These
        # membership proofs must follow that actual unchanged definition.
        first='  exact satisfied row (List.mem_append_left _ member)\n'
        second='  exact satisfied row (List.mem_append_right _ (List.mem_append_left _ member))\n'
        page='      apply List.mem_append_right\n      apply List.mem_append_right\n'
        assert source.count(first)==1 and source.count(second)==1
        assert source.count(page)==32
        return (source.replace(first,'  exact satisfied row (List.mem_append_left _ (List.mem_append_left _ member))\n')
                .replace(second,'  exact satisfied row (List.mem_append_left _ (List.mem_append_right _ member))\n')
                .replace(page,'      apply List.mem_append_right\n'))
    before='import ShielddSecurity.Scalar\n'
    assert source.startswith(before) and source.count(before)==1
    return source.replace(before,'import ShielddSecurity.RoutingPrecision\n',1)
