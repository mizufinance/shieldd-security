"""Bounded VALUE_BLINDING pages using the universal fixed-window proof.

Only the genuine balance blinding parser and original-row union accept data.
Already checked row, LC, table, and allocation facts feed neutral rendering
functions; no EPK observation, qualification flag, or scalar role is fabricated.
The initial folded window and canonical/native scalar composition are separate.
"""
from . import transfer_balance_blinding_program as whole
from . import transfer_balance_blinding_completion as local
from . import generate_transfer_epk_fixed_template as window_renderer
from . import generate_transfer_epk_fixed_template_program as program_renderer
from . import generate_transfer_epk_fixed_template_trace_page as trace_renderer
from . import transfer_relation as relation


def generate_modules(parent, pages, expected_base, expected_blinding, extracted,
                     page, *, phase='window', readonly_lcs=()):
    if type(page) is not int or not 0 <= page < 8:
        raise relation.RelationError('VALUE_BLINDING bounded page0..7 required')
    if phase not in ('window', 'trace'):
        raise relation.RelationError('VALUE_BLINDING exact template rendering phase')
    accepted = whole.plan(parent, pages, expected_base, expected_blinding, extracted, readonly_lcs)
    checked = accepted['checked']['chunks'][page]
    selection = accepted['selections'][page]
    raw, normalized, _, _ = local.selection(checked, selection)
    plan = accepted['local_plans'][page]
    bounds = accepted['bounds']
    data = [(offset, window_renderer._layout(checked, raw, normalized, plan, offset))
            for offset, window in enumerate(plan['windows']) if window['index'] != 0]
    if not 1 <= len(data) <= 16:
        raise relation.RelationError('VALUE_BLINDING exact bounded ordinary page')
    stem = 'RuntimeBalanceBlinding'
    if phase == 'window':
        modules = []
        for offset, item in data:
            name = stem + f'Window{item["index"]:03d}'
            modules.append((name+'TemplateCompletion', window_renderer.render_checked(
                checked, raw, normalized, plan, offset, stem=name)))
            modules.append(program_renderer.render_checked(
                checked, raw, normalized, plan, offset, stem=name))
        return modules
    incoming = {column for terms in data[0][1]['before'] for column, _ in terms}
    kept = sorted(set(plan['kept']) | incoming)
    for _, item in data:
        if item['copy'] != bounds['constant_copy']:
            raise relation.RelationError('VALUE_BLINDING whole/page constant copy differs')
        for step in item['stages']:
            writes = ({step['output'], step['auxiliary']} if step['kind'] == 'product'
                      else {step['quotient'], step['product'], step['auxiliary']})
            if writes & set(kept):
                raise relation.RelationError('VALUE_BLINDING actual writes alias incoming/caller columns')
    for (_, previous), (_, current) in zip(data, data[1:]):
        if previous['after'] != current['before'] or previous['table'][3] != current['table'][0]:
            raise relation.RelationError('VALUE_BLINDING source endpoint/table adjacency differs')
    modules = []
    for _, item in data:
        name = stem + f'Window{item["index"]:03d}TemplateTrace'
        modules.append((name, trace_renderer._window(
            item, bounds['frames'][item['index']], bounds, kept, stem)))
    name = stem + f'TemplatePage{page:02d}Trace'
    modules.append((name, trace_renderer._page(
        [item for _, item in data], bounds, kept, stem, name)))
    return modules
