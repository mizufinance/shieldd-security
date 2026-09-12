package arrays

func ReadWrite(a *[4]uint64, i int, x uint64) uint64 {
	a[i] = x
	return a[i]
}

func Local(x uint64) uint64 {
	var a [4]uint64
	a[1] = x
	return a[1]
}

func Copy(dst, src *[4]uint64) {
	*dst = *src
}

func Alias(a, b *[4]uint64) uint64 {
	a[1] = 7
	b[1] = 9
	return a[1]
}
