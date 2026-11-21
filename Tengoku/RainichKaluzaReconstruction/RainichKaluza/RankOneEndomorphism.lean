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

@[simp]
theorem rankOneEndomorphism_apply
    (f : E →ₗ[ℝ] ℝ) (x y : E) :
    rankOneEndomorphism f x y = f y • x :=
  rfl

/-- **Basis-independent rank-one square law.**-/
theorem rankOneEndomorphism_sq
    (f : E →ₗ[ℝ] ℝ) (x : E) :
    rankOneEndomorphism f x * rankOneEndomorphism f x =
      f x • rankOneEndomorphism f x := by
  ext y
  simp [rankOneEndomorphism, smul_smul, mul_comm]

/-- In finite free dimension, the coefficient in the square law is exactly the
endomorphism trace.-/
theorem rankOneEndomorphism_sq_eq_trace_smul
    [Module.Free ℝ E] [Module.Finite ℝ E]
    (f : E →ₗ[ℝ] ℝ) (x : E) :
    rankOneEndomorphism f x * rankOneEndomorphism f x =
      LinearMap.trace ℝ E (rankOneEndomorphism f x) •
        rankOneEndomorphism f x := by
  rw [rankOneEndomorphism_sq]
  simp [rankOneEndomorphism]

end RainichKaluza
