"""Typed physical-template fixtures only; no runtime or kernel evidence."""
import json,unittest
from circuits import transfer_routing_rows as routing
from circuits.transfer_relation import RelationError,MODULUS

unit=lambda column:((column,1),)
c=routing.canonical
add=routing.combine

class Fixture:
    def __init__(self):self.rows={};self.next=5000
    def row(self,a,b=()):
        index=len(self.rows);self.rows[index]=(a,b);return index
    def fresh(self):self.next+=1;return unit(self.next)
    def product(self,left,right,numerator=None):
        auxiliary=self.fresh();output=self.fresh()
        self.row(add(left,right,-1),auxiliary)
        self.row(add(left,right),add(auxiliary,output,4))
        if numerator is not None:self.row(add(output,numerator,-1))
        return output
    def table(self):return routing._Rows(self.rows,self.rows,200692)

def precision():
    f=Fixture();input_lc=unit(80);matches=[unit(100+i) for i in range(33)]
    total=()
    for match in matches:total=add(total,match)
    f.row(add(total,routing.ONE,-1))
    for value,zero in enumerate(matches):
        f.row(zero,zero);den=add(input_lc,c([(0,value)]),-1)
        inverse=f.fresh()
        f.product(den,inverse,add(routing.ONE,zero,-1));f.product(den,zero,())
    prefixes=[]
    for i in range(32):
        value=()
        for match in matches[i+1:]:value=add(value,match)
        prefixes.append(value)
    return f,dict(input=input_lc,known_matches=matches[1:],prefix=prefixes)

def permutation():
    f=Fixture();columns=[1000+3*i for i in range(255)]
    output=c([(900,2),(901,3),(902,4)])
    weighted=c((column,pow(2,i,MODULUS)) for i,column in enumerate(columns))
    f.row(add(weighted,output,-1));before=routing.ONE
    for i,column in enumerate(columns):
        left=unit(column);f.row(left,left);right=((MODULUS-1)>>i)&1
        both=add(routing.ONE,left,-1) if right else ()
        factor=add(add(add(routing.ONE,left,-1),c([(0,right)])),both,-2)
        product=factor if i==0 else f.product(before,factor)
        before=add(both,product)
    f.row(before,before);f.row(add(before,routing.ONE,-1))
    return f,dict(output=output,swapped=unit(columns[0]))

class RoutingRowTests(unittest.TestCase):
    def test_precision_derives_missing_match0_and_all_physical_pairs(self):
        f,s=precision();plan,used=routing._precision(s,f.table(),0)
        self.assertEqual(plan['matches'][0],unit(100));self.assertEqual(len(plan['steps']),33)
        self.assertEqual(used,set(f.rows))
        for step in plan['steps']:
            self.assertEqual(len(step['inverse_product']['rows']),3)
            self.assertEqual(len(step['zero_product']['rows']),3)

    def test_precision_duplicate_and_ambiguous_inverse_refused(self):
        for mode in ('onehot','boolean','pair','otherinverse','endpoint'):
            f,s=precision()
            if mode in ('onehot','boolean','pair'):
                f.row(*f.rows[{'onehot':0,'boolean':1,'pair':3}[mode]])
            elif mode=='otherinverse':f.product(s['input'],f.fresh(),add(routing.ONE,unit(100),-1))
            else:del f.rows[max(f.rows)]
            with self.assertRaises(RelationError):routing._precision(s,f.table(),0)

    def test_permutation_255_weight_order_and_exact_source_chain(self):
        f,s=permutation();plan,used=routing._permutation(s,f.table())
        self.assertEqual(plan['columns'],[1000+3*i for i in range(255)])
        self.assertEqual(plan['maximum'],MODULUS-1);self.assertEqual(len(plan['steps']),255)
        self.assertEqual(used,set(f.rows))
        # The derivative preserves tuple/list JSON round trips through typed rechecks.
        persisted=json.loads(json.dumps(plan));self.assertEqual(persisted['columns'],plan['columns'])

    def test_permutation_weight_bit0_endpoint_boolean_and_ambiguity_refused(self):
        for mode in ('weight','bit0','endpoint','boolean','duplicate','pair'):
            f,s=permutation()
            if mode=='weight':
                a,b=f.rows[0];f.rows[0]=(c((col,val+1 if col==1003 else val) for col,val in a),b)
            elif mode=='bit0':s['swapped']=unit(1003)
            elif mode=='endpoint':del f.rows[max(f.rows)]
            elif mode=='boolean':del f.rows[max(f.rows)-1]
            elif mode=='duplicate':f.row(*f.rows[0])
            else:f.row(*f.rows[4])
            with self.assertRaises(RelationError):routing._permutation(s,f.table())

if __name__=='__main__':unittest.main()
