import Tengoku.Seed.LinearAlgebra.Trace
import Tengoku.Seed.Data.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rank-one endomorphism square law

The scalar contribution in the convention-fixed EMD Einstein equation is a
rank-one mixed tensor.  This file proves, without choosing a basis, the square
law used by the reconstruction equation.
-/

namespace RainichKaluza

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- The rank-one endomorphism `y ↦ f(y) • x`.  The normalization factor in the
EMD scalar tensor can be absorbed into either `f` or `x`.-/
def rankOneEndomorphism (f : E →ₗ[ℝ] ℝ) (x : E) : Module.End ℝ E :=
  f.smulRight x

/--
@isnad1 id=eq.0h4v.s7.6f8d106c0935 from=translated src=- shape=361304b9 vocab=29eebce2
-/
@[simp]
theorem rankOneEndomorphism_apply
    (f : E →ₗ[ℝ] ℝ) (x y : E) :
    rankOneEndomorphism f x y = f y • x :=
  rfl

/-- **Basis-independent rank-one square law.**
@isnad1 id=eq.0h3v.s7.fb685629ea66 from=translated src=- shape=b0c9b885 vocab=ec58da5d
-/
theorem rankOneEndomorphism_sq
    (f : E →ₗ[ℝ] ℝ) (x : E) :
    rankOneEndomorphism f x * rankOneEndomorphism f x =
      f x • rankOneEndomorphism f x := by
  ext y
  simp [rankOneEndomorphism, smul_smul, mul_comm]

/-- In finite free dimension, the coefficient in the square law is exactly the
endomorphism trace.
@isnad1 id=eq.0h3v.s8.1ba02a517ab5 from=translated src=- shape=772fde0b vocab=84f68456
-/
theorem rankOneEndomorphism_sq_eq_trace_smul
    [Module.Free ℝ E] [Module.Finite ℝ E]
    (f : E →ₗ[ℝ] ℝ) (x : E) :
    rankOneEndomorphism f x * rankOneEndomorphism f x =
      LinearMap.trace ℝ E (rankOneEndomorphism f x) •
        rankOneEndomorphism f x := by
  rw [rankOneEndomorphism_sq]
  simp [rankOneEndomorphism]

end RainichKaluza
