import Tengoku.AbelFormalization.AbelFormalization.IdealHeight
import Tengoku.Seed.Algebra.MvPolynomial.Equiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Height under specialization of a saturated one-parameter ideal

This is the height step needed after identifying a full weighted initial
ideal with the zero-parameter specialization of its Laurent contraction.
The saturation hypothesis is actual cancellation of multiplication by the
parameter in ideal membership. It does not assume a height conclusion.
-/

noncomputable section

namespace AbelFormalization

variable {R : Type*} [CommRing R]

/-- An element cancellable modulo an ideal avoids each minimal prime over it.-/
theorem ideal_notMem_minimalPrimes_of_cancel (J : Ideal R) (x : R)
    (hcancel : ∀ f, x * f ∈ J → f ∈ J) {q : Ideal R}
    (hq : q ∈ J.minimalPrimes) : x ∉ q := by
  intro hx
  obtain ⟨y, hy, hxy⟩ := Ideal.exists_mul_mem_of_mem_minimalPrimes hq hx
  exact hy (hcancel y hxy)

end AbelFormalization
