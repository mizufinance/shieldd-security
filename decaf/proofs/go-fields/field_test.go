package fiat

import (
	"math/big"
	"testing"
)

func TestFrBoundary(t *testing.T) {
	a := [4]uint64{0xb95aee9ac33fd9fe, 0x5293a3afc43c8afe, 0x982d1347970dec00, 0x4aad957a68b2955}
	b := [4]uint64{1}
	var out [4]uint64
	FrAdd(&out, &a, &b)
	if out != [4]uint64{} {
		t.Fatalf("fr boundary witness: %v", out)
	}
}

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

// Every relative ordering of two input windows and the output window is
// represented. Compare the entire backing array to check the write frame too.
func TestFieldOffsetWindows(t *testing.T) {
	value := func(words []uint64) *big.Int {
		x := new(big.Int)
		for i := len(words) - 1; i >= 0; i-- {
			x.Lsh(x, 64).Add(x, new(big.Int).SetUint64(words[i]))
		}
		return x
	}
	for _, field := range []struct {
		name    string
		modulus string
		add     func(*[4]uint64, *[4]uint64, *[4]uint64)
	}{
		{"fq", "8444461749428370424248824938781546531375899335154063827935233455917409239041", FqAdd},
		{"fr", "2111115437357092606062206234695386632838870926408408195193685246394721360383", FrAdd},
	} {
		modulus, ok := new(big.Int).SetString(field.modulus, 10)
		if !ok {
			t.Fatal("invalid test modulus")
		}
		top := new(big.Int).Rsh(new(big.Int).Set(modulus), 192).Uint64() - 1
		for p := 0; p <= 6; p++ {
			for q := 0; q <= 6; q++ {
				for out := 0; out <= 6; out++ {
					for pattern := 0; pattern < 3; pattern++ {
						var backing [10]uint64
						for i := range backing {
							switch pattern {
							case 1:
								backing[i] = ^uint64(0)
							case 2:
								backing[i] = 0x9e3779b97f4a7c15 * uint64(i+1)
							}
						}
						if pattern != 0 {
							backing[p+3], backing[q+3] = top, top
						}
						a, b := value(backing[p:p+4]), value(backing[q:q+4])
						if a.Cmp(modulus) >= 0 || b.Cmp(modulus) >= 0 {
							t.Fatal("unreduced fixture")
						}
						sum := new(big.Int).Add(a, b)
						sum.Mod(sum, modulus)
						expected := backing
						for i := 0; i < 4; i++ {
							expected[out+i] = sum.Uint64()
							sum.Rsh(sum, 64)
						}
						field.add((*[4]uint64)(backing[out:out+4]), (*[4]uint64)(backing[p:p+4]), (*[4]uint64)(backing[q:q+4]))
						if backing != expected {
							t.Fatalf("%s offsets out=%d p=%d q=%d pattern=%d: got %v want %v", field.name, out, p, q, pattern, backing, expected)
						}
					}
				}
			}
		}
	}
}
