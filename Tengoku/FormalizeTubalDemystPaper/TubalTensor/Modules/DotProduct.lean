import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Modules.OrientedMatrix
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.RingStructure.StarRing
import Tengoku.FormalizeTubalDemystPaper.TubalTensor.RingStructure.PartialOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Modules/DotProduct.lean
  The ⋆_M-dot product on oriented matrices (Eq. (8), Theorem 20).

  For U, V ∈ K_M^m, the dot product is:
    U ·_M V := ∑ᵢ (U i)* ⋆_M (V i)
  where (U i)* is the ⋆_M-conjugation.
-/

namespace TubalTensor

open BigOperators

variable {n : ℕ} {td : TubalData n} {m : ℕ}

/-- The ⋆_M-dot product on oriented matrices:
    `dotM U V = ∑ᵢ star (U i) * V i`.-/
noncomputable def dotM (U V : OrientedMatrix m n td) : KM n td :=
  ∑ i : Fin m, star (U i) * V i

theorem dotM_apply (U V : OrientedMatrix m n td) :
    dotM U V = ∑ i : Fin m, star (U i) * V i := rfl

/-! ## Theorem 20, Part 1: Conjugate symmetry -/

/-- **Theorem 20 (conjugate symmetry)**: `dotM U V = star (dotM V U)`.-/
theorem dotM_conj_symm (U V : OrientedMatrix m n td) :
    dotM U V = star (dotM V U) := by
  simp only [dotM_apply, star_sum, star_mul, star_star, mul_comm]

/-! ## Theorem 20, Part 2: ⋆_M-linearity in the second argument -/

/-! ## Theorem 20, Part 3: Positive definiteness

  The key identity at tube level: M(u* ⋆_M u) = conj(Mu) • Mu,
  whose j-th entry is |y_j|² where y = Mu. -/

section PositiveDefiniteness

open Complex Matrix

end PositiveDefiniteness

end TubalTensor
