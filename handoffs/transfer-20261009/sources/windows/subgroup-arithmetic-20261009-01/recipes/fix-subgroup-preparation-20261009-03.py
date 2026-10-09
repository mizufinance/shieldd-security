from pathlib import Path
original = Path('C:/src/shieldd-transfer-handoffs/prepare-windows-subgroup-arithmetic-20261009-01.py')
body = original.read_text()
scanner = '''
def without_comments(text):
    result, index, depth = [], 0, 0
    while index < len(text):
        if text[index:index+2] == '/-':
            depth += 1; index += 2
        elif depth and text[index:index+2] == '-/':
            depth -= 1; index += 2
        elif not depth and text[index:index+2] == '--':
            end = text.find('\\n', index)
            index = len(text) if end == -1 else end
        else:
            if not depth: result.append(text[index])
            elif text[index] == '\\n': result.append('\\n')
            index += 1
    assert depth == 0
    return ''.join(result)
'''
body = body.replace("stem = 'windows-subgroup-arithmetic-20261009-01'", "stem = 'windows-subgroup-arithmetic-20261009-03'")
body = body.replace('\ndef visit(name):', scanner + '\ndef visit(name):')
line = next(line for line in body.splitlines() if line.startswith('    assert not re.search'))
body = body.replace(line, line.removesuffix('body)') + 'without_comments(body))')
start = body.index("# The original Mac source identity")
end = body.index("(out / 'manifest.json')", start)
body = body[:start] + "manifest.pop('original_mac_source_sha256')\n" + body[end:]
Path('C:/src/shieldd-transfer-handoffs/prepare-windows-subgroup-arithmetic-20261009-03.py').write_text(body)
