import Tengoku.FormalizeTubalDemystPaper.TubalTensor.LinearMaps.HermitianTranspose

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/SVD/Unitary.lean
  Definition 28 (⋆_M-unitary tensor).

  A tensor U ∈ K_M^{m×m} is ⋆_M-unitary if U^H ⋆_M U = I_m.
  The reverse U ⋆_M U^H = I_m follows automatically for square matrices
  over a commutative ring.
-/

namespace TubalTensor

open Matrix

variable {n : ℕ} {td : TubalData n} {m : ℕ}

/-! ## Definition 28: ⋆_M-unitary tensor -/

/-- **Definition 28.** A square tubal matrix U ∈ K_M^{m×m} is ⋆_M-unitary
    if Uᴴ ⋆_M U = I_m. (The reverse U ⋆_M Uᴴ = I_m follows automatically
    for square matrices over a commutative ring.)-/
def IsStarMUnitary (U : TubalMatrix m m n td) : Prop :=
  Uᴴ * U = 1

/-- A ⋆_M-unitary tensor has Uᴴ * U = 1.
@isnad1 id=eq.1h4v.s6.d412dc520cd9 from=translated src=- shape=11425dea vocab=e42b8ff5
-/
theorem IsStarMUnitary.conjTranspose_mul_self {U : TubalMatrix m m n td}
    (h : IsStarMUnitary U) : Uᴴ * U = 1 := h

/-- A ⋆_M-unitary tensor has U * Uᴴ = 1.
@isnad1 id=eq.1h4v.s6.ff8403a3a7b5 from=translated src=- shape=5523aaa4 vocab=e42b8ff5
-/
theorem IsStarMUnitary.mul_conjTranspose_self {U : TubalMatrix m m n td}
    (h : IsStarMUnitary U) : U * Uᴴ = 1 :=
  (mul_eq_one_comm_of_card_eq (Fin m) (Fin m) (KM n td) rfl).mp h

end TubalTensor
