"""Synthetic complete-relation range-row controls for captured current spends."""
import copy
import json
import unittest
from circuits import transfer_note_spend as notes,transfer_note_ranges as ranges,transfer_relation as relation
from circuits.transfer_balance_rows import canonical,combine
from tests.test_transfer_note_spend import fixture


def range_fixture(slot=0,kind='amount',reverse=False,omit=None):
    args=fixture();checked=notes.inspect_metadata(args[0],args[2]);spend=checked['spends'][slot]
    rows=notes.extract(*args)['selected_rows']
    bits=[bit[0][0] for bit in spend[kind+'_bits']]
    value=spend['note'][1] if kind=='amount' else spend['position']
    for index,column in enumerate(bits):
        if index!=omit:rows.append(dict(row=len(rows),a=[[column,f'{1:064x}']],b=[[column,f'{1:064x}']]))
    weighted=canonical((column,2**index) for index,column in enumerate(bits))
    delta=combine(weighted,value,-1)
    if reverse:delta=canonical((c,-v) for c,v in delta)
    rows.append(dict(row=len(rows),a=[[c,f'{v:064x}'] for c,v in delta],b=[]))
    return fixture(rows=rows)


class NoteRangeTests(unittest.TestCase):
    def test_all_four_actual_role_blocks_and_constructive_exports(self):
        for slot,kind in ((0,'amount'),(0,'position'),(1,'amount'),(1,'position')):
            with self.subTest(slot=slot,kind=kind):
                args=range_fixture(slot,kind);selected=ranges.extract(*args,slot,kind)
                self.assertEqual(len(selected['selected_rows']),130 if kind=='amount' else 50)
                text=ranges.generate(args[0],json.loads(json.dumps(selected)),args[2],slot,kind)
                self.assertEqual(text.count('#print axioms'),5)
                self.assertIn('writeBits_range_complete',text)
                self.assertIn('theorem complete_actual_range',text)
                self.assertIn('expectedRows.any',text)
                self.assertIn('set_option maxRecDepth 4096',text)
                self.assertIn('rw [weightedValue,singleton] at reconstruction',text)
                self.assertIn('have bitCount : bits.length',text)
                self.assertNotIn('simpa only [weightedValue,eval',text)

    def test_opposite_assertion_orientation_and_omitted_bit_refusal(self):
        args=range_fixture(reverse=True);selected=ranges.extract(*args,0,'amount')
        self.assertIn('have reconstruction := reconstruction.symm',ranges.generate(args[0],selected,args[2],0,'amount'))
        with self.assertRaisesRegex(relation.RelationError,'missing note-0-amount actual template bit.127'):
            ranges.extract(*range_fixture(omit=127),0,'amount')

    def test_prior_source_bit_alias_refusal_and_selected_row_mutation(self):
        args=range_fixture();selected=ranges.extract(*args,0,'amount')
        changed=copy.deepcopy(selected);changed['selected_rows'][-1]['a'][0][1]=f'{2:064x}'
        with self.assertRaises(relation.RelationError):
            ranges.generate(args[0],changed,args[2],0,'amount')
        accepted=copy.deepcopy(args[2]);accepted['observed'][(2,9999)]=((603,1),)
        with self.assertRaisesRegex(relation.RelationError,'occur in another source role'):
            ranges.generate(args[0],selected,accepted,0,'amount')

    def test_legal_boundaries_and_exact_boolean_reconstruction_controls(self):
        args=range_fixture();selected=ranges.extract(*args,0,'amount');rows=selected['selected_rows']
        block=ranges.boundary(args[0],args[2],0,'amount');columns=block['columns'];value=block['value']
        def rejects(n,nonboolean=False,wrong_value=False):
            rho={0:1,1000:1,value:n+(1 if wrong_value else 0),1:7,2:11}
            for index,column in enumerate(columns):rho[column]=(n>>index)&1
            if nonboolean:rho[columns[-1]]=2;rho[value]=2**128
            def evaluate(lc):return sum(rho.get(c,0)*int(v,16) for c,v in lc)%relation.MODULUS
            return [r['row'] for r in rows if evaluate(r['a'])**2%relation.MODULUS!=evaluate(r['b'])]
        for n in (0,1,2**128-1):self.assertEqual(rejects(n),[])
        self.assertEqual(len(rejects(0,nonboolean=True)),1)
        self.assertEqual(len(rejects(1,wrong_value=True)),1)


if __name__=='__main__':unittest.main()
