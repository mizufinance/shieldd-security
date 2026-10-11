import ShielddSecurity.CompilerIndexedRecipe38
import ShielddSecurity.ArithmeticCoefficients39
import ShielddSecurity.CompilerIndexedCoverage36
import ShielddSecurity.MerkleBits29
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedIndexedArithmetic40Pilot
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def arithmetic : Array Row := (Array.mk [⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(16,0)]),[(22738,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(17,0)]),[(22739,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22738,2806),(22739,7482)]),[(22741,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22738,2806),(22739,0)]),[(22740,4),(22741,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(16,0)]),[(22742,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(17,0)]),[(22743,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22742,0),(22743,7482)]),[(22745,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22742,0),(22743,0)]),[(22744,4),(22745,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22744,5325)]),[(22747,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(200692,1)]),[(22746,4),(22747,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(18,0),(22746,7482)]),[(22749,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(18,0),(22746,0)]),[(22748,4),(22749,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(16,0),(17,7482)]),[(22751,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(16,0),(17,0)]),[(22750,4),(22751,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(16,7482),(17,0)]),[(22753,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(16,0),(17,0)]),[(22752,4),(22753,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22744,2806),(22750,0),(22752,0),(200692,7482)]),[(22755,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22744,4651),(22750,0),(22752,0),(200692,0)]),[(22754,4),(22755,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(18,7482),(22754,0)]),[(22757,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(18,0),(22754,0)]),[(22756,4),(22757,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22742,0),(22743,0),(22744,4651),(200692,7482)]),[(22759,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22742,0),(22743,0),(22744,2806),(200692,0)]),[(22758,4),(22759,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(18,7482),(22758,0)]),[(22761,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(18,0),(22758,0)]),[(22760,4),(22761,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22756,0)]),[(22762,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22760,0)]),[(22763,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22762,0),(22763,7482)]),[(22765,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22762,0),(22763,0)]),[(22764,4),(22765,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22764,5325)]),[(22767,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(200692,1)]),[(22766,4),(22767,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(19,0),(22766,7482)]),[(22769,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(19,0),(22766,0)]),[(22768,4),(22769,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22756,0),(22760,7482)]),[(22771,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22756,0),(22760,0)]),[(22770,4),(22771,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22756,7482),(22760,0)]),[(22773,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22756,0),(22760,0)]),[(22772,4),(22773,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22764,2806),(22770,0),(22772,0),(200692,7482)]),[(22775,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22764,4651),(22770,0),(22772,0),(200692,0)]),[(22774,4),(22775,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(19,7482),(22774,0)]),[(22777,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(19,0),(22774,0)]),[(22776,4),(22777,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22762,0),(22763,0),(22764,4651),(200692,7482)]),[(22779,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22762,0),(22763,0),(22764,2806),(200692,0)]),[(22778,4),(22779,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(19,7482),(22778,0)]),[(22781,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(19,0),(22778,0)]),[(22780,4),(22781,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22776,0)]),[(22782,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22780,0)]),[(22783,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22782,0),(22783,7482)]),[(22785,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22782,0),(22783,0)]),[(22784,4),(22785,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22784,5325)]),[(22787,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(200692,1)]),[(22786,4),(22787,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(20,0),(22786,7482)]),[(22789,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(20,0),(22786,0)]),[(22788,4),(22789,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22776,0),(22780,7482)]),[(22791,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22776,0),(22780,0)]),[(22790,4),(22791,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22776,7482),(22780,0)]),[(22793,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22776,0),(22780,0)]),[(22792,4),(22793,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22784,2806),(22790,0),(22792,0),(200692,7482)]),[(22795,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22784,4651),(22790,0),(22792,0),(200692,0)]),[(22794,4),(22795,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(20,7482),(22794,0)]),[(22797,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(20,0),(22794,0)]),[(22796,4),(22797,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22782,0),(22783,0),(22784,4651),(200692,7482)]),[(22799,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22782,0),(22783,0),(22784,2806),(200692,0)]),[(22798,4),(22799,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(20,7482),(22798,0)]),[(22801,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(20,0),(22798,0)]),[(22800,4),(22801,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(25,0)]),[(22802,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(26,0)]),[(22803,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22802,2806),(22803,7482)]),[(22805,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22802,2806),(22803,0)]),[(22804,4),(22805,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(25,0)]),[(22806,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(26,0)]),[(22807,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22806,0),(22807,7482)]),[(22809,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22806,0),(22807,0)]),[(22808,4),(22809,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22808,5325)]),[(22811,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(200692,1)]),[(22810,4),(22811,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(27,0),(22810,7482)]),[(22813,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(27,0),(22810,0)]),[(22812,4),(22813,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(25,0),(26,7482)]),[(22815,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(25,0),(26,0)]),[(22814,4),(22815,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(25,7482),(26,0)]),[(22817,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(25,0),(26,0)]),[(22816,4),(22817,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22808,2806),(22814,0),(22816,0),(200692,7482)]),[(22819,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22808,4651),(22814,0),(22816,0),(200692,0)]),[(22818,4),(22819,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(27,7482),(22818,0)]),[(22821,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(27,0),(22818,0)]),[(22820,4),(22821,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22806,0),(22807,0),(22808,4651),(200692,7482)]),[(22823,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22806,0),(22807,0),(22808,2806),(200692,0)]),[(22822,4),(22823,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(27,7482),(22822,0)]),[(22825,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(27,0),(22822,0)]),[(22824,4),(22825,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22820,0)]),[(22826,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22824,0)]),[(22827,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22826,0),(22827,7482)]),[(22829,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22826,0),(22827,0)]),[(22828,4),(22829,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22828,5325)]),[(22831,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(200692,1)]),[(22830,4),(22831,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(28,0),(22830,7482)]),[(22833,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(28,0),(22830,0)]),[(22832,4),(22833,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22820,0),(22824,7482)]),[(22835,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22820,0),(22824,0)]),[(22834,4),(22835,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22820,7482),(22824,0)]),[(22837,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22820,0),(22824,0)]),[(22836,4),(22837,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22828,2806),(22834,0),(22836,0),(200692,7482)]),[(22839,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22828,4651),(22834,0),(22836,0),(200692,0)]),[(22838,4),(22839,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(28,7482),(22838,0)]),[(22841,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(28,0),(22838,0)]),[(22840,4),(22841,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22826,0),(22827,0),(22828,4651),(200692,7482)]),[(22843,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22826,0),(22827,0),(22828,2806),(200692,0)]),[(22842,4),(22843,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(28,7482),(22842,0)]),[(22845,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(28,0),(22842,0)]),[(22844,4),(22845,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22840,0)]),[(22846,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22844,0)]),[(22847,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22846,0),(22847,7482)]),[(22849,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22846,0),(22847,0)]),[(22848,4),(22849,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22848,5325)]),[(22851,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(200692,1)]),[(22850,4),(22851,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(29,0),(22850,7482)]),[(22853,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(29,0),(22850,0)]),[(22852,4),(22853,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22840,0),(22844,7482)]),[(22855,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22840,0),(22844,0)]),[(22854,4),(22855,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22840,7482),(22844,0)]),[(22857,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22840,0),(22844,0)]),[(22856,4),(22857,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22848,2806),(22854,0),(22856,0),(200692,7482)]),[(22859,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22848,4651),(22854,0),(22856,0),(200692,0)]),[(22858,4),(22859,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(29,7482),(22858,0)]),[(22861,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(29,0),(22858,0)]),[(22860,4),(22861,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22846,0),(22847,0),(22848,4651),(200692,7482)]),[(22863,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(22846,0),(22847,0),(22848,2806),(200692,0)]),[(22862,4),(22863,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(29,7482),(22862,0)]),[(22865,1)]⟩,⟨(CompilerIndexedRecipe38.linear ArithmeticCoefficients39.value [(29,0),(22862,0)]),[(22864,4),(22865,1)]⟩])
def actualCopy : Row := ⟨[(0,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
def recipes : List CompilerIndexedRecipe38.Recipe := [.square [(16,0)],.square [(17,0)],.pair [(22738,2806),(22739,7482)] [(22738,2806),(22739,0)],.square [(16,0)],.square [(17,0)],.pair [(22742,0),(22743,7482)] [(22742,0),(22743,0)],.pair [(22744,5325)] [(200692,1)],.pair [(18,0),(22746,7482)] [(18,0),(22746,0)],.pair [(16,0),(17,7482)] [(16,0),(17,0)],.pair [(16,7482),(17,0)] [(16,0),(17,0)],.pair [(22744,2806),(22750,0),(22752,0),(200692,7482)] [(22744,4651),(22750,0),(22752,0),(200692,0)],.pair [(18,7482),(22754,0)] [(18,0),(22754,0)],.pair [(22742,0),(22743,0),(22744,4651),(200692,7482)] [(22742,0),(22743,0),(22744,2806),(200692,0)],.pair [(18,7482),(22758,0)] [(18,0),(22758,0)],.square [(22756,0)],.square [(22760,0)],.pair [(22762,0),(22763,7482)] [(22762,0),(22763,0)],.pair [(22764,5325)] [(200692,1)],.pair [(19,0),(22766,7482)] [(19,0),(22766,0)],.pair [(22756,0),(22760,7482)] [(22756,0),(22760,0)],.pair [(22756,7482),(22760,0)] [(22756,0),(22760,0)],.pair [(22764,2806),(22770,0),(22772,0),(200692,7482)] [(22764,4651),(22770,0),(22772,0),(200692,0)],.pair [(19,7482),(22774,0)] [(19,0),(22774,0)],.pair [(22762,0),(22763,0),(22764,4651),(200692,7482)] [(22762,0),(22763,0),(22764,2806),(200692,0)],.pair [(19,7482),(22778,0)] [(19,0),(22778,0)],.square [(22776,0)],.square [(22780,0)],.pair [(22782,0),(22783,7482)] [(22782,0),(22783,0)],.pair [(22784,5325)] [(200692,1)],.pair [(20,0),(22786,7482)] [(20,0),(22786,0)],.pair [(22776,0),(22780,7482)] [(22776,0),(22780,0)],.pair [(22776,7482),(22780,0)] [(22776,0),(22780,0)],.pair [(22784,2806),(22790,0),(22792,0),(200692,7482)] [(22784,4651),(22790,0),(22792,0),(200692,0)],.pair [(20,7482),(22794,0)] [(20,0),(22794,0)],.pair [(22782,0),(22783,0),(22784,4651),(200692,7482)] [(22782,0),(22783,0),(22784,2806),(200692,0)],.pair [(20,7482),(22798,0)] [(20,0),(22798,0)],.square [(25,0)],.square [(26,0)],.pair [(22802,2806),(22803,7482)] [(22802,2806),(22803,0)],.square [(25,0)],.square [(26,0)],.pair [(22806,0),(22807,7482)] [(22806,0),(22807,0)],.pair [(22808,5325)] [(200692,1)],.pair [(27,0),(22810,7482)] [(27,0),(22810,0)],.pair [(25,0),(26,7482)] [(25,0),(26,0)],.pair [(25,7482),(26,0)] [(25,0),(26,0)],.pair [(22808,2806),(22814,0),(22816,0),(200692,7482)] [(22808,4651),(22814,0),(22816,0),(200692,0)],.pair [(27,7482),(22818,0)] [(27,0),(22818,0)],.pair [(22806,0),(22807,0),(22808,4651),(200692,7482)] [(22806,0),(22807,0),(22808,2806),(200692,0)],.pair [(27,7482),(22822,0)] [(27,0),(22822,0)],.square [(22820,0)],.square [(22824,0)],.pair [(22826,0),(22827,7482)] [(22826,0),(22827,0)],.pair [(22828,5325)] [(200692,1)],.pair [(28,0),(22830,7482)] [(28,0),(22830,0)],.pair [(22820,0),(22824,7482)] [(22820,0),(22824,0)],.pair [(22820,7482),(22824,0)] [(22820,0),(22824,0)],.pair [(22828,2806),(22834,0),(22836,0),(200692,7482)] [(22828,4651),(22834,0),(22836,0),(200692,0)],.pair [(28,7482),(22838,0)] [(28,0),(22838,0)],.pair [(22826,0),(22827,0),(22828,4651),(200692,7482)] [(22826,0),(22827,0),(22828,2806),(200692,0)],.pair [(28,7482),(22842,0)] [(28,0),(22842,0)],.square [(22840,0)],.square [(22844,0)],.pair [(22846,0),(22847,7482)] [(22846,0),(22847,0)],.pair [(22848,5325)] [(200692,1)],.pair [(29,0),(22850,7482)] [(29,0),(22850,0)],.pair [(22840,0),(22844,7482)] [(22840,0),(22844,0)],.pair [(22840,7482),(22844,0)] [(22840,0),(22844,0)],.pair [(22848,2806),(22854,0),(22856,0),(200692,7482)] [(22848,4651),(22854,0),(22856,0),(200692,0)],.pair [(29,7482),(22858,0)] [(29,0),(22858,0)],.pair [(22846,0),(22847,0),(22848,4651),(200692,7482)] [(22846,0),(22847,0),(22848,2806),(200692,0)],.pair [(29,7482),(22862,0)] [(29,0),(22862,0)]]
def selectedRows := arithmetic.toList++[actualCopy]
def decodedRecipes := CompilerIndexedRecipe38.decodeList ArithmeticCoefficients39.value recipes
def expectedRows := CompilerFreshArithmetic35.rows 22738 decodedRecipes++[⟨[(0,1),(copy,-1)],[]⟩]
def mapping : Array Nat := (List.range 129).toArray
def captureIndices := List.range 128++[200769]
theorem support_checked : CompilerIndexedRecipe38.check copy 22738 recipes=true := by decide +kernel
theorem checked : CompilerFreshArithmetic35.check copy 22738 decodedRecipes=true := by rw [CompilerIndexedRecipe38.decode_list_check];exact support_checked
theorem rows_exact : CompilerFreshArithmetic35.rows 22738 decodedRecipes=arithmetic.toList := by rfl
theorem span_exact : CompilerFreshArithmetic35.span decodedRecipes=128 := by rw [CompilerIndexedRecipe38.decode_span];decide +kernel
def production (candidate : List Row) (indices : Array Nat) : Bool :=
  checkOriginalCoverage p 0 candidate.toArray expectedRows.toArray indices &&
  checkOriginalCoverage p 0 expectedRows.toArray candidate.toArray indices
theorem copy_equal : canonical p actualCopy.a=canonical p [(0,1),(copy,-1)] ∧ canonical p actualCopy.b=canonical p ([] : Linear) := by decide +kernel
theorem positive : production selectedRows mapping=true := by
  unfold production expectedRows selectedRows
  rw [rows_exact]
  apply Bool.and_eq_true_iff.mpr
  constructor
  · exact CompilerIndexedCoverage36.append_coverage p arithmetic.toList actualCopy ⟨[(0,1),(copy,-1)],[]⟩ copy_equal.1 copy_equal.2
  · exact CompilerIndexedCoverage36.append_coverage p arithmetic.toList ⟨[(0,1),(copy,-1)],[]⟩ actualCopy copy_equal.1.symm copy_equal.2.symm
theorem every_position : ∀ index : Fin 129,checkOriginalAt p 0 selectedRows.toArray expectedRows.toArray mapping index.val=true := by
  intro index
  have first : checkOriginalCoverage p 0 selectedRows.toArray expectedRows.toArray mapping=true := (Bool.and_eq_true_iff.mp positive).1
  have parts := Bool.and_eq_true_iff.mp first
  apply List.all_eq_true.mp parts.2 index.val
  apply List.mem_range.mpr
  have size : selectedRows.toArray.size=129 := by decide +kernel
  rw [size]
  exact index.isLt
theorem counts : recipes.length=72 ∧ selectedRows.length=129 ∧ captureIndices.length=129 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
def completed (base : Nat → F) := CompilerFreshArithmetic35.run 22738 base decodedRecipes
omit [CharP F p] in
theorem outside (base : Nat → F) (column : Nat) (bound : column<22738 ∨ 22866≤column) : completed base column=base column :=
  CompilerFreshArithmetic35.run_outside decodedRecipes 22738 base column (by rw [span_exact];exact bound)
theorem complete (base : Nat → F) (linked : base copy=base 0) : Satisfies (completed base) selectedRows := by
  have done := CompilerFreshArithmetic35.complete decodedRecipes copy 22738 base checked (by rw [span_exact];decide) (MerkleHash27R0Proof.four_ne_zero (F:=F))
  have reference : Satisfies (completed base) expectedRows := by
    intro row member
    rcases List.mem_append.mp member with member|member
    · exact done row member
    · have eq : row=⟨[(0,1),(copy,-1)],[]⟩ := by simpa only [List.mem_singleton] using member
      subst row
      change Square (eval (completed base) [(0,1),(copy,-1)]) (eval (completed base) [])
      simp only [eval,Int.cast_one,Int.cast_neg,one_mul,neg_one_mul,add_zero,
        outside base 0 (Or.inl (by decide)),outside base copy (Or.inr (by decide)),linked,add_neg_cancel]
      simp [Square]
  apply MerkleBits29.transfer _ selectedRows expectedRows
  · have part:= (Bool.and_eq_true_iff.mp positive).1
    have equal : (List.range selectedRows.length).toArray=mapping := by rw [counts.2.1];rfl
    rw [equal]
    exact part
  · exact reference
omit [CharP F p] in
theorem original_inputs (base : Nat → F) (input : Nat) (bound : input<22735) : completed base (3+input)=base (3+input) :=
  outside base _ (Or.inl (by omega))
omit [CharP F p] in
theorem fixed (base : Nat → F) : completed base 0=base 0 ∧ completed base 1=base 1 ∧ completed base 2=base 2 ∧ completed base copy=base copy :=
  ⟨outside base 0 (Or.inl (by decide)),outside base 1 (Or.inl (by decide)),outside base 2 (Or.inl (by decide)),outside base copy (Or.inr (by decide))⟩
def badCoefficient : List Row := let row := selectedRows.headD ⟨[],[]⟩;⟨row.a.map (fun term => (term.1,term.2+1)),row.b⟩::selectedRows.tail
theorem coefficient_rejected : production badCoefficient mapping=false := by
  have bad : checkOriginalCoverage p 0 badCoefficient.toArray expectedRows.toArray mapping=false :=
    CompilerIndexedCoverage36.reject_position p _ _ _ 0 (by decide +kernel) (by decide +kernel)
  unfold production
  rw [bad]
  rfl
theorem existing_index_rejected : production selectedRows (mapping.set! 0 1)=false := by
  have bad : checkOriginalCoverage p 0 selectedRows.toArray expectedRows.toArray (mapping.set! 0 1)=false :=
    CompilerIndexedCoverage36.reject_position p _ _ _ 0 (by decide +kernel) (by decide +kernel)
  unfold production
  rw [bad]
  rfl
theorem omission_rejected : production selectedRows.tail mapping=false := by decide +kernel
def badCopyRows := arithmetic.toList++[⟨[(0,-1),(copy,2)],[]⟩]
theorem copy_rejected : production badCopyRows mapping=false := by
  have bad : checkOriginalCoverage p 0 badCopyRows.toArray expectedRows.toArray mapping=false :=
    CompilerIndexedCoverage36.reject_position p _ _ _ 128 (by decide +kernel) (by decide +kernel)
  unfold production
  rw [bad]
  rfl
end ShielddSecurity.CapturedIndexedArithmetic40Pilot

set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.arithmetic
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.arithmetic
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.actualCopy
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.actualCopy
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.recipes
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.recipes
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.selectedRows
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.selectedRows
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.decodedRecipes
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.decodedRecipes
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.expectedRows
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.expectedRows
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.mapping
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.mapping
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.captureIndices
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.captureIndices
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.support_checked
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.support_checked
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.checked
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.rows_exact
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.span_exact
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.span_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.production
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.production
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.copy_equal
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.copy_equal
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.positive
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.positive
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.every_position
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.every_position
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.counts
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.counts
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.completed
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.outside
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.complete
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.complete
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.original_inputs
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.original_inputs
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.fixed
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.fixed
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.badCoefficient
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.badCoefficient
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.coefficient_rejected
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.coefficient_rejected
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.existing_index_rejected
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.existing_index_rejected
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.omission_rejected
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.omission_rejected
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.badCopyRows
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.badCopyRows
set_option pp.all true in
#check @ShielddSecurity.CapturedIndexedArithmetic40Pilot.copy_rejected
#print axioms ShielddSecurity.CapturedIndexedArithmetic40Pilot.copy_rejected
