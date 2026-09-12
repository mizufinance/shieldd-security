package main

import decaf "github.com/mizufinance/decaf377-go"

var secret [32]byte
var output decaf.Point
var base decaf.Point

//go:noinline
func decafDone() { _ = output }

//go:noinline
func decafEntry() {
    // Both APIs reduce the same fixed-length byte input modulo the scalar order.
    scalar := decaf.ScalarFromUniformBytes(secret[:])
    var err error
    output, err = decaf.ScalarMul(base, scalar)
    if err != nil { panic(err) }
    decafDone()
}

func main() {
    var err error
    base, err = decaf.Generator()
    if err != nil { panic(err) }
    decafEntry()
    if !decaf.Equal(output, decaf.Identity()) { panic("zero scalar") }
}
