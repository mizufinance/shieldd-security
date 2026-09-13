package main

import decaf "github.com/mizufinance/decaf377-go"

var secret [32]byte
var output [32]byte
var base decaf.Point

//go:noinline
func decafDone() { _ = output }

//go:noinline
func decafEntry() {
    scalar := decaf.ScalarFromUniformBytes(secret[:])
    point, err := decaf.ScalarMul(base, scalar)
    if err != nil { panic(err) }
    output, err = decaf.CompressToFieldBytes(point)
    if err != nil { panic(err) }
    decafDone()
}

func main() {
    var err error
    base, err = decaf.Generator()
    if err != nil { panic(err) }
    decafEntry()
    if output != [32]byte{} { panic("zero scalar must encode identity") }
}
