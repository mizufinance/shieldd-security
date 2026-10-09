"""Give finite RNK bit adapters their certified scalar definition import."""
import re


def generate(name, source):
    match = re.fullmatch(r'RuntimeRnkSparseBlock(\d{3})', name)
    if match and (int(match.group(1)) % 17 == 16 or int(match.group(1)) == 133):
        assert 'import ShielddSecurity.RuntimeOwnershipConstructorTrace\n' not in source
        assert 'Scalar.modulus' in source
        source = 'import ShielddSecurity.RuntimeOwnershipConstructorTrace\n' + source
    return source
