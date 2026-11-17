import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1Coordinates
import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Curry
import Tengoku.Seed.Algebra.Order.Archimedean.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Every Banach space is a quotient of ℓ¹

For a Banach space `H`, the map `ℓ¹(B_H, K) → H`, `a ↦ ∑_v a_v v`, indexed by the closed
unit ball `B_H`, has norm at most one, is surjective, and is open. Each `h` lifts to a
single coordinate of norm at most `‖c‖ ‖h‖`, for any `c` with `1 < ‖c‖`. This is used in
`QuotientParameterCounterexample.lean`.
-/

open scoped lp BigOperators

noncomputable section

namespace AlternatingAnalytic

/-- The closed unit ball of `H`, used as the index set.-/
abbrev L1UnitBallIndex (H : Type*) [NormedAddCommGroup H] := {h : H // ‖h‖ ≤ 1}

variable (K H : Type*) [NontriviallyNormedField K]
  [NormedAddCommGroup H] [NormedSpace K H] [CompleteSpace H]

local instance : DecidableEq (L1UnitBallIndex H) := Classical.decEq _

/-- The quotient map `a ↦ ∑_v a_v v` from `ℓ¹` over the closed unit ball.-/
def unitBallL1Quotient : lp (fun _ : L1UnitBallIndex H => K) 1 →L[K] H :=
  continuousMultilinearCurryFin1 K (lp (fun _ : L1UnitBallIndex H => K) 1) H
    (L1Coordinates.continuousMultilinearOfBounded
      (fun v : Fin 1 → L1UnitBallIndex H => (v 0 : H)) 1 (fun v => (v 0).property))

variable {K H}

/-- The quotient map is the unconditional sum `∑_v a_v v`.
@isnad1 id=hassum.0h3v.s12.7eaa5e825c52 from=translated src=- shape=a3b20bfe vocab=2eaf4107
-/
theorem unitBallL1Quotient_hasSum (a : lp (fun _ : L1UnitBallIndex H => K) 1) :
    HasSum (fun v : L1UnitBallIndex H => a v • (v : H)) (unitBallL1Quotient K H a) := by
  have hs := L1Coordinates.continuousMultilinearOfBounded_hasSum
    (K := K) (fun v : Fin 1 → L1UnitBallIndex H => (v 0 : H)) 1
    (fun v => (v 0).property) (Fin.snoc 0 a)
  apply (Equiv.funUnique (Fin 1) (L1UnitBallIndex H)).hasSum_iff.mp
  simpa [unitBallL1Quotient, continuousMultilinearCurryFin1_apply, Function.comp_def] using hs

/--
@isnad1 id=eq.0h3v.s12.58a5a409ca0b from=translated src=- shape=609c9b66 vocab=c77e2d89
-/
theorem unitBallL1Quotient_apply (a : lp (fun _ : L1UnitBallIndex H => K) 1) :
    unitBallL1Quotient K H a = ∑' v : L1UnitBallIndex H, a v • (v : H) :=
  (unitBallL1Quotient_hasSum a).tsum_eq.symm

/-- The quotient map sends `a e_v` to `a v`.
@isnad1 id=eq.0h4v.s12.25ed002e0c42 from=translated src=- shape=b534198b vocab=e7534af6
-/
@[simp]
theorem unitBallL1Quotient_single (v : L1UnitBallIndex H) (a : K) :
    unitBallL1Quotient K H (lp.single 1 v a) = a • (v : H) := by
  classical
  rw [unitBallL1Quotient_apply, tsum_eq_single v]
  · simp
  · intro w hw
    rw [lp.single_apply_ne _ _ _ hw, zero_smul]

end AlternatingAnalytic
