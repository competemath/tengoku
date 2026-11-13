import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.LinearAlgebra.Pi
import Tengoku.Seed.Analysis.Normed.Module.FiniteDimension
import Tengoku.Seed.LinearAlgebra.Complex.FiniteDimensional

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real and imaginary coordinates of complex vectors

The real-linear equivalence uses disjoint finite coordinate copies. It is
algebraic for any index type and continuous when the index type is finite.
-/

noncomputable section
namespace Complex

/-- Real and imaginary coordinates as a real-linear equivalence.-/
def realCoordinates (ι : Type*) : (ι → ℂ) ≃ₗ[ℝ] (ι ⊕ ι → ℝ) where
  toFun z := Sum.elim (fun i => (z i).re) (fun i => (z i).im)
  invFun x i := (x (Sum.inl i) : ℂ) + (x (Sum.inr i) : ℂ) * I
  left_inv z := by funext i; exact re_add_im (z i)
  right_inv x := by funext s; cases s <;> simp
  map_add' z w := by funext s; cases s <;> simp
  map_smul' c z := by funext s; cases s <;> simp

/--
@isnad1 id=eq.0h3v.s8.37534ec5a4ce from=translated src=- shape=a3b87602 vocab=c2367543
-/
@[simp] theorem realCoordinates_inl {ι : Type*} (z : ι → ℂ) (i : ι) :
    realCoordinates ι z (Sum.inl i) = (z i).re := rfl

/--
@isnad1 id=eq.0h3v.s8.16c738f900d9 from=translated src=- shape=a3b87602 vocab=3ab29059
-/
@[simp] theorem realCoordinates_inr {ι : Type*} (z : ι → ℂ) (i : ι) :
    realCoordinates ι z (Sum.inr i) = (z i).im := rfl

/-- In finite dimensions the coordinate equivalence is continuous in both
 directions for the ordinary product topologies.-/
def realCoordinatesContinuousLinearEquiv (ι : Type*) [Fintype ι] :
    (ι → ℂ) ≃L[ℝ] (ι ⊕ ι → ℝ) := (realCoordinates ι).toContinuousLinearEquiv

end Complex
