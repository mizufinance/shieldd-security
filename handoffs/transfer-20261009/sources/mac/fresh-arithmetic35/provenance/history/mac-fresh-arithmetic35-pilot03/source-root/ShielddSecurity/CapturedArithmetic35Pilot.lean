import ShielddSecurity.CompilerFreshArithmetic35
import ShielddSecurity.MerkleBits29
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
noncomputable section
namespace ShielddSecurity.CapturedArithmetic35Pilot
open Compiler CompilerIndexed01
open CapturedInitial73419Generic01 (p copy)
def arithmetic : Array Row := (Array.mk [⟨[(16,1)],[(22738,1)]⟩,⟨[(17,1)],[(22739,1)]⟩,⟨[(22738,19257038036680949359750312669786877991949435402254120286184196891950884077233),(22739,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22741,1)]⟩,⟨[(22738,19257038036680949359750312669786877991949435402254120286184196891950884077233),(22739,1)],[(22740,4),(22741,1)]⟩,⟨[(16,1)],[(22742,1)]⟩,⟨[(17,1)],[(22743,1)]⟩,⟨[(22742,1),(22743,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22745,1)]⟩,⟨[(22742,1),(22743,1)],[(22744,4),(22745,1)]⟩,⟨[(22744,38514076073361898719500625339573755983898870804508240572368393783901768154466)],[(22747,1)]⟩,⟨[(200692,2)],[(22746,4),(22747,1)]⟩,⟨[(18,1),(22746,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22749,1)]⟩,⟨[(18,1),(22746,1)],[(22748,4),(22749,1)]⟩,⟨[(16,1),(17,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22751,1)]⟩,⟨[(16,1),(17,1)],[(22750,4),(22751,1)]⟩,⟨[(16,52435875175126190479447740508185965837690552500527637822603658699938581184512),(17,1)],[(22753,1)]⟩,⟨[(16,1),(17,1)],[(22752,4),(22753,1)]⟩,⟨[(22744,19257038036680949359750312669786877991949435402254120286184196891950884077233),(22750,1),(22752,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22755,1)]⟩,⟨[(22744,33178837138445241119697427838399087845741117098273517536419461807987697107280),(22750,1),(22752,1),(200692,1)],[(22754,4),(22755,1)]⟩,⟨[(18,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22754,1)],[(22757,1)]⟩,⟨[(18,1),(22754,1)],[(22756,4),(22757,1)]⟩,⟨[(22742,1),(22743,1),(22744,33178837138445241119697427838399087845741117098273517536419461807987697107280),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22759,1)]⟩,⟨[(22742,1),(22743,1),(22744,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(22758,4),(22759,1)]⟩,⟨[(18,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22758,1)],[(22761,1)]⟩,⟨[(18,1),(22758,1)],[(22760,4),(22761,1)]⟩,⟨[(22756,1)],[(22762,1)]⟩,⟨[(22760,1)],[(22763,1)]⟩,⟨[(22762,1),(22763,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22765,1)]⟩,⟨[(22762,1),(22763,1)],[(22764,4),(22765,1)]⟩,⟨[(22764,38514076073361898719500625339573755983898870804508240572368393783901768154466)],[(22767,1)]⟩,⟨[(200692,2)],[(22766,4),(22767,1)]⟩,⟨[(19,1),(22766,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22769,1)]⟩,⟨[(19,1),(22766,1)],[(22768,4),(22769,1)]⟩,⟨[(22756,1),(22760,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22771,1)]⟩,⟨[(22756,1),(22760,1)],[(22770,4),(22771,1)]⟩,⟨[(22756,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22760,1)],[(22773,1)]⟩,⟨[(22756,1),(22760,1)],[(22772,4),(22773,1)]⟩,⟨[(22764,19257038036680949359750312669786877991949435402254120286184196891950884077233),(22770,1),(22772,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22775,1)]⟩,⟨[(22764,33178837138445241119697427838399087845741117098273517536419461807987697107280),(22770,1),(22772,1),(200692,1)],[(22774,4),(22775,1)]⟩,⟨[(19,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22774,1)],[(22777,1)]⟩,⟨[(19,1),(22774,1)],[(22776,4),(22777,1)]⟩,⟨[(22762,1),(22763,1),(22764,33178837138445241119697427838399087845741117098273517536419461807987697107280),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22779,1)]⟩,⟨[(22762,1),(22763,1),(22764,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(22778,4),(22779,1)]⟩,⟨[(19,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22778,1)],[(22781,1)]⟩,⟨[(19,1),(22778,1)],[(22780,4),(22781,1)]⟩,⟨[(22776,1)],[(22782,1)]⟩,⟨[(22780,1)],[(22783,1)]⟩,⟨[(22782,1),(22783,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22785,1)]⟩,⟨[(22782,1),(22783,1)],[(22784,4),(22785,1)]⟩,⟨[(22784,38514076073361898719500625339573755983898870804508240572368393783901768154466)],[(22787,1)]⟩,⟨[(200692,2)],[(22786,4),(22787,1)]⟩,⟨[(20,1),(22786,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22789,1)]⟩,⟨[(20,1),(22786,1)],[(22788,4),(22789,1)]⟩,⟨[(22776,1),(22780,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22791,1)]⟩,⟨[(22776,1),(22780,1)],[(22790,4),(22791,1)]⟩,⟨[(22776,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22780,1)],[(22793,1)]⟩,⟨[(22776,1),(22780,1)],[(22792,4),(22793,1)]⟩,⟨[(22784,19257038036680949359750312669786877991949435402254120286184196891950884077233),(22790,1),(22792,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22795,1)]⟩,⟨[(22784,33178837138445241119697427838399087845741117098273517536419461807987697107280),(22790,1),(22792,1),(200692,1)],[(22794,4),(22795,1)]⟩,⟨[(20,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22794,1)],[(22797,1)]⟩,⟨[(20,1),(22794,1)],[(22796,4),(22797,1)]⟩,⟨[(22782,1),(22783,1),(22784,33178837138445241119697427838399087845741117098273517536419461807987697107280),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22799,1)]⟩,⟨[(22782,1),(22783,1),(22784,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(22798,4),(22799,1)]⟩,⟨[(20,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22798,1)],[(22801,1)]⟩,⟨[(20,1),(22798,1)],[(22800,4),(22801,1)]⟩,⟨[(25,1)],[(22802,1)]⟩,⟨[(26,1)],[(22803,1)]⟩,⟨[(22802,19257038036680949359750312669786877991949435402254120286184196891950884077233),(22803,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22805,1)]⟩,⟨[(22802,19257038036680949359750312669786877991949435402254120286184196891950884077233),(22803,1)],[(22804,4),(22805,1)]⟩,⟨[(25,1)],[(22806,1)]⟩,⟨[(26,1)],[(22807,1)]⟩,⟨[(22806,1),(22807,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22809,1)]⟩,⟨[(22806,1),(22807,1)],[(22808,4),(22809,1)]⟩,⟨[(22808,38514076073361898719500625339573755983898870804508240572368393783901768154466)],[(22811,1)]⟩,⟨[(200692,2)],[(22810,4),(22811,1)]⟩,⟨[(27,1),(22810,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22813,1)]⟩,⟨[(27,1),(22810,1)],[(22812,4),(22813,1)]⟩,⟨[(25,1),(26,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22815,1)]⟩,⟨[(25,1),(26,1)],[(22814,4),(22815,1)]⟩,⟨[(25,52435875175126190479447740508185965837690552500527637822603658699938581184512),(26,1)],[(22817,1)]⟩,⟨[(25,1),(26,1)],[(22816,4),(22817,1)]⟩,⟨[(22808,19257038036680949359750312669786877991949435402254120286184196891950884077233),(22814,1),(22816,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22819,1)]⟩,⟨[(22808,33178837138445241119697427838399087845741117098273517536419461807987697107280),(22814,1),(22816,1),(200692,1)],[(22818,4),(22819,1)]⟩,⟨[(27,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22818,1)],[(22821,1)]⟩,⟨[(27,1),(22818,1)],[(22820,4),(22821,1)]⟩,⟨[(22806,1),(22807,1),(22808,33178837138445241119697427838399087845741117098273517536419461807987697107280),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22823,1)]⟩,⟨[(22806,1),(22807,1),(22808,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(22822,4),(22823,1)]⟩,⟨[(27,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22822,1)],[(22825,1)]⟩,⟨[(27,1),(22822,1)],[(22824,4),(22825,1)]⟩,⟨[(22820,1)],[(22826,1)]⟩,⟨[(22824,1)],[(22827,1)]⟩,⟨[(22826,1),(22827,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22829,1)]⟩,⟨[(22826,1),(22827,1)],[(22828,4),(22829,1)]⟩,⟨[(22828,38514076073361898719500625339573755983898870804508240572368393783901768154466)],[(22831,1)]⟩,⟨[(200692,2)],[(22830,4),(22831,1)]⟩,⟨[(28,1),(22830,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22833,1)]⟩,⟨[(28,1),(22830,1)],[(22832,4),(22833,1)]⟩,⟨[(22820,1),(22824,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22835,1)]⟩,⟨[(22820,1),(22824,1)],[(22834,4),(22835,1)]⟩,⟨[(22820,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22824,1)],[(22837,1)]⟩,⟨[(22820,1),(22824,1)],[(22836,4),(22837,1)]⟩,⟨[(22828,19257038036680949359750312669786877991949435402254120286184196891950884077233),(22834,1),(22836,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22839,1)]⟩,⟨[(22828,33178837138445241119697427838399087845741117098273517536419461807987697107280),(22834,1),(22836,1),(200692,1)],[(22838,4),(22839,1)]⟩,⟨[(28,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22838,1)],[(22841,1)]⟩,⟨[(28,1),(22838,1)],[(22840,4),(22841,1)]⟩,⟨[(22826,1),(22827,1),(22828,33178837138445241119697427838399087845741117098273517536419461807987697107280),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22843,1)]⟩,⟨[(22826,1),(22827,1),(22828,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(22842,4),(22843,1)]⟩,⟨[(28,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22842,1)],[(22845,1)]⟩,⟨[(28,1),(22842,1)],[(22844,4),(22845,1)]⟩,⟨[(22840,1)],[(22846,1)]⟩,⟨[(22844,1)],[(22847,1)]⟩,⟨[(22846,1),(22847,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22849,1)]⟩,⟨[(22846,1),(22847,1)],[(22848,4),(22849,1)]⟩,⟨[(22848,38514076073361898719500625339573755983898870804508240572368393783901768154466)],[(22851,1)]⟩,⟨[(200692,2)],[(22850,4),(22851,1)]⟩,⟨[(29,1),(22850,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22853,1)]⟩,⟨[(29,1),(22850,1)],[(22852,4),(22853,1)]⟩,⟨[(22840,1),(22844,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22855,1)]⟩,⟨[(22840,1),(22844,1)],[(22854,4),(22855,1)]⟩,⟨[(22840,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22844,1)],[(22857,1)]⟩,⟨[(22840,1),(22844,1)],[(22856,4),(22857,1)]⟩,⟨[(22848,19257038036680949359750312669786877991949435402254120286184196891950884077233),(22854,1),(22856,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22859,1)]⟩,⟨[(22848,33178837138445241119697427838399087845741117098273517536419461807987697107280),(22854,1),(22856,1),(200692,1)],[(22858,4),(22859,1)]⟩,⟨[(29,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22858,1)],[(22861,1)]⟩,⟨[(29,1),(22858,1)],[(22860,4),(22861,1)]⟩,⟨[(22846,1),(22847,1),(22848,33178837138445241119697427838399087845741117098273517536419461807987697107280),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[(22863,1)]⟩,⟨[(22846,1),(22847,1),(22848,19257038036680949359750312669786877991949435402254120286184196891950884077233),(200692,1)],[(22862,4),(22863,1)]⟩,⟨[(29,52435875175126190479447740508185965837690552500527637822603658699938581184512),(22862,1)],[(22865,1)]⟩,⟨[(29,1),(22862,1)],[(22864,4),(22865,1)]⟩])
def actualCopy : Row := ⟨[(0,1),(200692,52435875175126190479447740508185965837690552500527637822603658699938581184512)],[]⟩
def recipes : List CompilerFreshArithmetic35.Recipe := [.square (arithmetic.getD 0 ⟨[],[]⟩).a,.square (arithmetic.getD 1 ⟨[],[]⟩).a,.pair (arithmetic.getD 2 ⟨[],[]⟩).a (arithmetic.getD 3 ⟨[],[]⟩).a,.square (arithmetic.getD 4 ⟨[],[]⟩).a,.square (arithmetic.getD 5 ⟨[],[]⟩).a,.pair (arithmetic.getD 6 ⟨[],[]⟩).a (arithmetic.getD 7 ⟨[],[]⟩).a,.pair (arithmetic.getD 8 ⟨[],[]⟩).a (arithmetic.getD 9 ⟨[],[]⟩).a,.pair (arithmetic.getD 10 ⟨[],[]⟩).a (arithmetic.getD 11 ⟨[],[]⟩).a,.pair (arithmetic.getD 12 ⟨[],[]⟩).a (arithmetic.getD 13 ⟨[],[]⟩).a,.pair (arithmetic.getD 14 ⟨[],[]⟩).a (arithmetic.getD 15 ⟨[],[]⟩).a,.pair (arithmetic.getD 16 ⟨[],[]⟩).a (arithmetic.getD 17 ⟨[],[]⟩).a,.pair (arithmetic.getD 18 ⟨[],[]⟩).a (arithmetic.getD 19 ⟨[],[]⟩).a,.pair (arithmetic.getD 20 ⟨[],[]⟩).a (arithmetic.getD 21 ⟨[],[]⟩).a,.pair (arithmetic.getD 22 ⟨[],[]⟩).a (arithmetic.getD 23 ⟨[],[]⟩).a,.square (arithmetic.getD 24 ⟨[],[]⟩).a,.square (arithmetic.getD 25 ⟨[],[]⟩).a,.pair (arithmetic.getD 26 ⟨[],[]⟩).a (arithmetic.getD 27 ⟨[],[]⟩).a,.pair (arithmetic.getD 28 ⟨[],[]⟩).a (arithmetic.getD 29 ⟨[],[]⟩).a,.pair (arithmetic.getD 30 ⟨[],[]⟩).a (arithmetic.getD 31 ⟨[],[]⟩).a,.pair (arithmetic.getD 32 ⟨[],[]⟩).a (arithmetic.getD 33 ⟨[],[]⟩).a,.pair (arithmetic.getD 34 ⟨[],[]⟩).a (arithmetic.getD 35 ⟨[],[]⟩).a,.pair (arithmetic.getD 36 ⟨[],[]⟩).a (arithmetic.getD 37 ⟨[],[]⟩).a,.pair (arithmetic.getD 38 ⟨[],[]⟩).a (arithmetic.getD 39 ⟨[],[]⟩).a,.pair (arithmetic.getD 40 ⟨[],[]⟩).a (arithmetic.getD 41 ⟨[],[]⟩).a,.pair (arithmetic.getD 42 ⟨[],[]⟩).a (arithmetic.getD 43 ⟨[],[]⟩).a,.square (arithmetic.getD 44 ⟨[],[]⟩).a,.square (arithmetic.getD 45 ⟨[],[]⟩).a,.pair (arithmetic.getD 46 ⟨[],[]⟩).a (arithmetic.getD 47 ⟨[],[]⟩).a,.pair (arithmetic.getD 48 ⟨[],[]⟩).a (arithmetic.getD 49 ⟨[],[]⟩).a,.pair (arithmetic.getD 50 ⟨[],[]⟩).a (arithmetic.getD 51 ⟨[],[]⟩).a,.pair (arithmetic.getD 52 ⟨[],[]⟩).a (arithmetic.getD 53 ⟨[],[]⟩).a,.pair (arithmetic.getD 54 ⟨[],[]⟩).a (arithmetic.getD 55 ⟨[],[]⟩).a,.pair (arithmetic.getD 56 ⟨[],[]⟩).a (arithmetic.getD 57 ⟨[],[]⟩).a,.pair (arithmetic.getD 58 ⟨[],[]⟩).a (arithmetic.getD 59 ⟨[],[]⟩).a,.pair (arithmetic.getD 60 ⟨[],[]⟩).a (arithmetic.getD 61 ⟨[],[]⟩).a,.pair (arithmetic.getD 62 ⟨[],[]⟩).a (arithmetic.getD 63 ⟨[],[]⟩).a,.square (arithmetic.getD 64 ⟨[],[]⟩).a,.square (arithmetic.getD 65 ⟨[],[]⟩).a,.pair (arithmetic.getD 66 ⟨[],[]⟩).a (arithmetic.getD 67 ⟨[],[]⟩).a,.square (arithmetic.getD 68 ⟨[],[]⟩).a,.square (arithmetic.getD 69 ⟨[],[]⟩).a,.pair (arithmetic.getD 70 ⟨[],[]⟩).a (arithmetic.getD 71 ⟨[],[]⟩).a,.pair (arithmetic.getD 72 ⟨[],[]⟩).a (arithmetic.getD 73 ⟨[],[]⟩).a,.pair (arithmetic.getD 74 ⟨[],[]⟩).a (arithmetic.getD 75 ⟨[],[]⟩).a,.pair (arithmetic.getD 76 ⟨[],[]⟩).a (arithmetic.getD 77 ⟨[],[]⟩).a,.pair (arithmetic.getD 78 ⟨[],[]⟩).a (arithmetic.getD 79 ⟨[],[]⟩).a,.pair (arithmetic.getD 80 ⟨[],[]⟩).a (arithmetic.getD 81 ⟨[],[]⟩).a,.pair (arithmetic.getD 82 ⟨[],[]⟩).a (arithmetic.getD 83 ⟨[],[]⟩).a,.pair (arithmetic.getD 84 ⟨[],[]⟩).a (arithmetic.getD 85 ⟨[],[]⟩).a,.pair (arithmetic.getD 86 ⟨[],[]⟩).a (arithmetic.getD 87 ⟨[],[]⟩).a,.square (arithmetic.getD 88 ⟨[],[]⟩).a,.square (arithmetic.getD 89 ⟨[],[]⟩).a,.pair (arithmetic.getD 90 ⟨[],[]⟩).a (arithmetic.getD 91 ⟨[],[]⟩).a,.pair (arithmetic.getD 92 ⟨[],[]⟩).a (arithmetic.getD 93 ⟨[],[]⟩).a,.pair (arithmetic.getD 94 ⟨[],[]⟩).a (arithmetic.getD 95 ⟨[],[]⟩).a,.pair (arithmetic.getD 96 ⟨[],[]⟩).a (arithmetic.getD 97 ⟨[],[]⟩).a,.pair (arithmetic.getD 98 ⟨[],[]⟩).a (arithmetic.getD 99 ⟨[],[]⟩).a,.pair (arithmetic.getD 100 ⟨[],[]⟩).a (arithmetic.getD 101 ⟨[],[]⟩).a,.pair (arithmetic.getD 102 ⟨[],[]⟩).a (arithmetic.getD 103 ⟨[],[]⟩).a,.pair (arithmetic.getD 104 ⟨[],[]⟩).a (arithmetic.getD 105 ⟨[],[]⟩).a,.pair (arithmetic.getD 106 ⟨[],[]⟩).a (arithmetic.getD 107 ⟨[],[]⟩).a,.square (arithmetic.getD 108 ⟨[],[]⟩).a,.square (arithmetic.getD 109 ⟨[],[]⟩).a,.pair (arithmetic.getD 110 ⟨[],[]⟩).a (arithmetic.getD 111 ⟨[],[]⟩).a,.pair (arithmetic.getD 112 ⟨[],[]⟩).a (arithmetic.getD 113 ⟨[],[]⟩).a,.pair (arithmetic.getD 114 ⟨[],[]⟩).a (arithmetic.getD 115 ⟨[],[]⟩).a,.pair (arithmetic.getD 116 ⟨[],[]⟩).a (arithmetic.getD 117 ⟨[],[]⟩).a,.pair (arithmetic.getD 118 ⟨[],[]⟩).a (arithmetic.getD 119 ⟨[],[]⟩).a,.pair (arithmetic.getD 120 ⟨[],[]⟩).a (arithmetic.getD 121 ⟨[],[]⟩).a,.pair (arithmetic.getD 122 ⟨[],[]⟩).a (arithmetic.getD 123 ⟨[],[]⟩).a,.pair (arithmetic.getD 124 ⟨[],[]⟩).a (arithmetic.getD 125 ⟨[],[]⟩).a,.pair (arithmetic.getD 126 ⟨[],[]⟩).a (arithmetic.getD 127 ⟨[],[]⟩).a]
def selectedRows := arithmetic.toList++[actualCopy]
def expectedRows := CompilerFreshArithmetic35.rows 22738 recipes++[⟨[(0,1),(copy,-1)],[]⟩]
def mapping : Array Nat := (List.range 129).toArray
def captureIndices := List.range 128++[200769]
theorem checked : CompilerFreshArithmetic35.check copy 22738 recipes=true := by decide +kernel
theorem rows_exact : CompilerFreshArithmetic35.rows 22738 recipes=arithmetic.toList := by decide +kernel
theorem span_exact : CompilerFreshArithmetic35.span recipes=128 := by decide +kernel
def production (candidate : List Row) (indices : Array Nat) : Bool :=
  checkOriginalCoverage p 0 candidate.toArray expectedRows.toArray indices &&
  checkOriginalCoverage p 0 expectedRows.toArray candidate.toArray indices
theorem positive : production selectedRows mapping=true := by decide +kernel
theorem every_position : ∀ index : Fin 129,checkOriginalAt p 0 selectedRows.toArray expectedRows.toArray mapping index.val=true := by decide +kernel
theorem counts : recipes.length=72 ∧ selectedRows.length=129 ∧ captureIndices.length=129 := by decide +kernel
variable {F : Type} [Field F] [CharP F p]
def completed (base : Nat → F) := CompilerFreshArithmetic35.run 22738 base recipes
omit [CharP F p] in
theorem outside (base : Nat → F) (column : Nat) (bound : column<22738 ∨ 22866≤column) : completed base column=base column :=
  CompilerFreshArithmetic35.run_outside recipes 22738 base column (by rw [span_exact];exact bound)
theorem complete (base : Nat → F) (linked : base copy=base 0) : Satisfies (completed base) selectedRows := by
  have done := CompilerFreshArithmetic35.complete recipes copy 22738 base checked (by rw [span_exact];decide) (MerkleHash27R0Proof.four_ne_zero (F:=F))
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
theorem coefficient_rejected : production badCoefficient mapping=false := by decide +kernel
theorem existing_index_rejected : production selectedRows (mapping.set! 0 1)=false := by decide +kernel
theorem omission_rejected : production selectedRows.tail mapping=false := by decide +kernel
theorem copy_rejected : production (arithmetic.toList++[⟨[(0,-1),(copy,2)],[]⟩]) mapping=false := by decide +kernel
end ShielddSecurity.CapturedArithmetic35Pilot

set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.arithmetic
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.arithmetic
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.actualCopy
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.actualCopy
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.recipes
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.recipes
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.selectedRows
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.selectedRows
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.expectedRows
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.expectedRows
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.mapping
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.mapping
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.captureIndices
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.captureIndices
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.checked
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.checked
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.rows_exact
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.rows_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.span_exact
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.span_exact
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.production
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.production
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.positive
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.positive
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.every_position
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.every_position
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.counts
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.counts
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.completed
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.completed
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.outside
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.outside
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.complete
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.complete
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.original_inputs
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.original_inputs
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.fixed
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.fixed
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.badCoefficient
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.badCoefficient
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.coefficient_rejected
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.coefficient_rejected
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.existing_index_rejected
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.existing_index_rejected
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.omission_rejected
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.omission_rejected
set_option pp.all true in
#check @ShielddSecurity.CapturedArithmetic35Pilot.copy_rejected
#print axioms ShielddSecurity.CapturedArithmetic35Pilot.copy_rejected
