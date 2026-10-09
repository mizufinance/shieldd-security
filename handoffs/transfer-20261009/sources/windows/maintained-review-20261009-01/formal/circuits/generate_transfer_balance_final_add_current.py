"""Current final-add proof renderer over the genuine shared-inverse source plan."""
from . import generate_transfer_balance_final_add_completion as construction
from . import generate_transfer_balance_final_add_soundness as soundness
from .transfer_relation import RelationError


def _current(result):
    namespace, source = result
    for operation in ('cross', 'diagonal'):
        old = f'    simp only [signedPoint,blindedPoint,Group.{operation}]\n    ring'
        if source.count(old) != 1:
            raise RelationError('final-add exact endpoint polynomial proof anchor')
        source = source.replace(old,
            f'    simp only [signedPoint,blindedPoint,Group.{operation}] <;> ring')
    if namespace == 'RuntimeTransferBalanceFinalAddSoundness':
        old = '  rcases Bool.or_eq_true.mp checked with direct | reversed'
        if source.count(old) != 1:
            raise RelationError('final-add exact reverse-row Boolean proof anchor')
        source = source.replace(old,
            '  simp only [Bool.or_eq_true] at checked\n'
            '  rcases checked with direct | reversed')
    return namespace, source


def generate_from_joint(*args, **kwargs):
    return [_current(construction.generate_from_joint(*args, **kwargs)),
            _current(soundness.generate_from_joint(*args, **kwargs))]


def render_plan(plan):
    return [_current(construction.render_plan(plan)),
            _current(soundness.render_plan(plan))]
