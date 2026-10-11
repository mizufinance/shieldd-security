from pathlib import Path
import argparse,json,re,hashlib
def parse(expression, outer=False):
    pattern = 'ArithmeticCoefficients39C\\d{2}\\.value|\\d+|[()]|<|\\b(?:if|index|then|else)\\b'
    matches = list(re.finditer(pattern, expression))
    position = 0
    for match in matches:
        assert not expression[position:match.start()].strip()
        position = match.end()
    assert not expression[position:].strip()
    tokens = [m.group(0) for m in matches]
    cursor = 0

    def consume(value=None):
        nonlocal cursor
        assert cursor < len(tokens)
        token = tokens[cursor]
        cursor += 1
        assert value is None or token == value
        return token

    def node():
        token = consume()
        if token == '(':
            consume('if')
            consume('index')
            consume('<')
            cut = int(consume())
            consume('then')
            left = node()
            consume('else')
            right = node()
            consume(')')
            return (cut, left, right)
        if outer:
            assert re.fullmatch('ArithmeticCoefficients39C\\d{2}\\.value', token)
            consume('index')
            return token.removesuffix('.value')
        assert token.isdigit()
        return int(token)
    tree = node()
    assert cursor == len(tokens)
    return tree

def lookup(tree, index):
    while isinstance(tree, tuple):
        cut, left, right = tree
        tree = left if index < cut else right
    return tree
parser=argparse.ArgumentParser();parser.add_argument('--output',type=Path,required=True);args=parser.parse_args()
S=Path('/Users/antoinecyr/Documents/Codex/2026-10-08/can/work/mac-assertion-provider50-source01')
source=S/'source-root/ShielddSecurity/AssertionCoefficients50.lean';data=S/'extra-coefficients01.json'
sb=source.read_bytes();db=data.read_bytes();extra=json.loads(db)
assert hashlib.sha256(db).hexdigest()=='cb4ed89bd29d0399be130012f9533aeeafb07557965a4f403ac4ecad09f1db22'
assert extra['first_index']==7483 and len(extra['coefficients'])==13
pattern=r'^noncomputable def value \(index : Nat\) : Int := if index<7483 then ArithmeticCoefficients39.value index else (.*)$'
match=re.search(pattern,sb.decode(),re.M);assert match;tree=parse(match[1])
assert [lookup(tree,i)for i in range(7483,7496)]==extra['coefficients']
assert lookup(tree,7496)==lookup(tree,1000000)==extra['coefficients'][-1]
old=extra['old_store'];old_bytes=Path(old['path']).read_bytes();assert len(old_bytes)==old['bytes']and hashlib.sha256(old_bytes).hexdigest()==old['sha256']
result={'kind':'Independent lexical lookup-tree interpretation for13 assertion coefficients; source/DATA only','source_sha256':hashlib.sha256(sb).hexdigest(),'extra_data_sha256':hashlib.sha256(db).hexdigest(),'inherited_store':old,'checked_half_open_indices':[7483,7496],'values_checked':13,'outside_behavior':'Below7483 delegates to the accepted arithmetic coefficient provider; index>=7496 returns final literal. No zero-outside law asserted.','kernel_replay':False,'full_transfer':'OPEN'}
assert source.read_bytes()==sb and data.read_bytes()==db
with args.output.open('x')as f:json.dump(result,f,indent=2);f.write('\n')
print(json.dumps({'coefficients':13,'source_data_only':True}))
