import ShielddGnarkFormal.Deployed.NoteReshape1x8BalanceCompressRunX0
import ShielddGnarkFormal.Deployed.NoteReshape1x8BalanceCompressRunX1
import ShielddGnarkFormal.Deployed.NoteReshape1x8BalanceCompressRunY0
import ShielddGnarkFormal.Deployed.NoteReshape1x8BalanceCompressRunY1

namespace Shieldd.GnarkFormal.Deployed.NoteReshape1x8BalanceCompressRuns

open Shieldd.GnarkFormal
open Contracts.NoteReshape1x8

theorem x0 (rho : Nat → Seg78.F) :
    StrideRun.sumAux (Seg78.localRho rho) 2 1 149 =
      StrideRun.sumAux rho 43177 5 149 :=
  NoteReshape1x8BalanceCompressRunX0.seated rho

theorem x1 (rho : Nat → Seg78.F) :
    StrideRun.sumAux (Seg78.localRho rho) 151 1 101 =
      StrideRun.sumAux rho 43925 8 101 :=
  NoteReshape1x8BalanceCompressRunX1.seated rho

theorem y0 (rho : Nat → Seg78.F) :
    StrideRun.sumAux (Seg78.localRho rho) 253 1 149 =
      StrideRun.sumAux rho 43178 5 149 :=
  NoteReshape1x8BalanceCompressRunY0.seated rho

theorem y1 (rho : Nat → Seg78.F) :
    StrideRun.sumAux (Seg78.localRho rho) 402 1 101 =
      StrideRun.sumAux rho 43926 8 101 :=
  NoteReshape1x8BalanceCompressRunY1.seated rho

end Shieldd.GnarkFormal.Deployed.NoteReshape1x8BalanceCompressRuns
