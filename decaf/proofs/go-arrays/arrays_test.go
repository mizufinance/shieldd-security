package arrays

import "testing"

func TestArrayBehavior(t *testing.T) {
	var a, b [4]uint64
	if Local(11) != 11 || ReadWrite(&a, 2, 17) != 17 {
		t.Fatal("element read/write")
	}
	a = [4]uint64{1, 2, 3, 4}
	Copy(&b, &a)
	if b != a {
		t.Fatal("array copy")
	}
	Copy(&a, &a)
	if a != b || Alias(&a, &a) != 9 || Alias(&a, &b) != 7 {
		t.Fatal("aliasing")
	}
	for name, index := range map[string]int{"negative": -1, "length": 4} {
		t.Run(name, func(t *testing.T) {
			defer func() {
				if recover() == nil {
					t.Fatal("invalid index did not panic")
				}
			}()
			ReadWrite(&a, index, 0)
		})
	}
}
