package fiat

import "testing"

func TestFqBoundary(t *testing.T) {
	a := [4]uint64{725501752471715840, 6461107452199829505, 6968279316240510977, 1345280370688173398}
	b := [4]uint64{1}
	var out [4]uint64
	FqAdd(&out, &a, &b)
	if out != [4]uint64{} {
		t.Fatalf("fq boundary witness: %v", out)
	}
}
func TestFieldAliases(t *testing.T) {
	for _, add := range []func(*[4]uint64, *[4]uint64, *[4]uint64){FqAdd, FrAdd} {
		a, b := [4]uint64{2}, [4]uint64{3}
		var out [4]uint64
		add(&out, &a, &b)
		if out != [4]uint64{5} || a != [4]uint64{2} || b != [4]uint64{3} {
			t.Fatal("disjoint")
		}
		add(&a, &a, &b)
		if a != [4]uint64{5} || b != [4]uint64{3} {
			t.Fatal("output aliases left")
		}
		a, b = [4]uint64{2}, [4]uint64{3}
		add(&b, &a, &b)
		if a != [4]uint64{2} || b != [4]uint64{5} {
			t.Fatal("output aliases right")
		}
		a = [4]uint64{2}
		add(&out, &a, &a)
		if out != [4]uint64{4} || a != [4]uint64{2} {
			t.Fatal("equal inputs")
		}
		add(&a, &a, &a)
		if a != [4]uint64{4} {
			t.Fatal("all equal")
		}
		backing := [6]uint64{2, 0, 0, 0, 99, 101}
		b = [4]uint64{3}
		add((*[4]uint64)(backing[1:5]), (*[4]uint64)(backing[0:4]), &b)
		if backing != [6]uint64{2, 5, 0, 0, 0, 101} || b != [4]uint64{3} {
			t.Fatal("offset overlap")
		}
	}
}
