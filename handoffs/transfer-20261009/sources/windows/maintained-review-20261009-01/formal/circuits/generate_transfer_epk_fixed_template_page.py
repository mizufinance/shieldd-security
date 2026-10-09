"""Bounded page rendering after one strict actual EPK plan acceptance.

The qualified folded window0 remains an explicit prerequisite. All ordinary
windows are rendered with the same checked page plan and actual shared frame.
"""
import re
from . import generate_transfer_epk_fixed_completion as ingress
from . import generate_transfer_epk_fixed_template as template
from . import generate_transfer_epk_fixed_template_program as program
from . import transfer_relation as relation


def generate_modules(qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,
                     scope_id,page_index=0,*,readonly_lcs=()):
    # Page0 has the separately qualified folded first window. The strict
    # selection still checks the whole page before any ordinary adapter emits.
    first_offset=1 if page_index==0 else 0
    checked,raw,normalized,_,_,plan,selected_stem=ingress._selection(
        qualified_parent,raw_pages,accepted_capsules,accepted_roles,extracted,
        scope_id,page_index,first_offset,readonly_lcs)
    match=re.fullmatch(r'(RuntimeTransferEpk[0-5]FixedWindow)([0-9]{3})',selected_stem)
    if match is None or int(match[2])!=plan['windows'][first_offset]['index']:
        raise relation.RelationError('EPK template page exact accepted namespace/index')
    if (type(plan['window_count'])is not int or not 1<=plan['window_count']<=16 or
        len(plan['windows'])!=plan['window_count']):
        raise relation.RelationError('EPK template bounded actual page plan')
    result=[]
    for offset,window in enumerate(plan['windows']):
        if window['index']==0:
            if page_index!=0 or offset!=0:
                raise relation.RelationError('EPK template folded0 must be the actual initial window')
            continue
        stem=match[1]+f'{window["index"]:03}'
        source=template.render_checked(checked,raw,normalized,plan,offset,stem=stem)
        result.append((stem+'TemplateCompletion',source))
        result.append(program.render_checked(checked,raw,normalized,plan,offset,stem=stem))
    if len({name for name,_ in result})!=len(result) or not result:
        raise relation.RelationError('EPK template exact nonempty ordinary page module inventory')
    return result
