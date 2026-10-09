"""Genuine H ingress with membership proofs for its actual flat kept list.

The original generator is retained because completed source packets pin it.
H's captured order module has one flat list, unlike the split EPK list.
"""
from . import generate_transfer_balance_blinding_template_canonical_ingress as original
from . import transfer_relation as relation


def generate_modules(*args, **kwargs):
    modules = original.generate_modules(*args, **kwargs)
    result = []
    for name, source in modules:
        if name == 'RuntimeBalanceBlindingTemplateCanonicalIngress':
            for column in (0, 200692):
                prefix = f'  have preserve{0 if column == 0 else "Copy"} := ingress.2.2.2 {column} '
                lines = source.splitlines(keepends=True)
                matching = [i for i, line in enumerate(lines) if line.startswith(prefix)]
                if len(matching) != 1 or 'keptPart' not in lines[matching[0]]:
                    raise relation.RelationError('H flat kept membership proof anchor')
                lines[matching[0]] = prefix + '(by decide)\n'
                source = ''.join(lines)
            if 'keptPart' in source:
                raise relation.RelationError('H ingress retained nonexistent split kept names')
        result.append((name, source))
    return result
