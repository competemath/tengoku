import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.EulerSurplus
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.GradedIntervalSurplus

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Surplus in terms of vertex, arrow and projective counts -/
set_option autoImplicit false
namespace MagnitudeConjecture.ARCount
universe u
variable {ι : Type u} [Fintype ι]

/-- The surplus is twice the vertex count, less arrows and twice the
projective count.
@isnad1 id=eq.0h3v.s6.87a8a498452b from=translated src=- shape=b276f70b vocab=f475e4d0
-/
theorem surplus_eq_counts (a : ι → ι → ℕ) (P : ι → Prop) [DecidablePred P] :
    surplus a P = 2 * vertexCount (ι := ι) - arrowCount a - 2 * projectiveCount P := by
  rw [surplus_eq_two_mul_meshCount_sub_arrowCount,
    vertexCount_eq_projectiveCount_add_meshCount P]
  ring

end MagnitudeConjecture.ARCount

namespace MagnitudeConjecture.GradedInterval

/-- Exact object and simple counts together with the arrow error give the
surplus error, with a fixed support-width correction.
@isnad1 id=le.3h9v.s8.eafcb950d520 from=translated src=- shape=f11ac108 vocab=94c1d9df
-/
theorem surplus_error_of_exact_counts
    (N Nm p pm m : ℕ) (a am W C : ℤ)
    (hN : (Nm : ℤ) = (N : ℤ) * ((m : ℤ) + 1) - W)
    (ha : |am - ((m : ℤ) + 1) * a| ≤ C)
    (hp : pm = p * (m + 1)) :
    |(2 * (Nm : ℤ) - am - 2 * pm) -
      ((m : ℤ) + 1) * (2 * N - a - 2 * p)| ≤ 2 * |W| + C := by
  have hNe : |(Nm : ℤ) - ((m : ℤ) + 1) * N| ≤ |W| := by
    have he : (Nm : ℤ) - ((m : ℤ) + 1) * N = -W := by nlinarith [hN]
    rw [he, abs_neg]
  have hpe : (pm : ℤ) = ((m : ℤ) + 1) * p := by
    exact_mod_cast hp.trans (Nat.mul_comm _ _)
  exact surplus_error_bound N a p Nm am pm ((m : ℤ) + 1) |W| C hNe ha hpe

end MagnitudeConjecture.GradedInterval
