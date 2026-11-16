import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_IdealSheafData_ofIdealTop_mul
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry

open TopologicalSpace Opposite
universe u

theorem solution {X : Scheme.{u}} (I J : Ideal Γ(X, ⊤)) :
    Scheme.IdealSheafData.ofIdealTop (I * J) = Scheme.IdealSheafData.ofIdealTop I * Scheme.IdealSheafData.ofIdealTop J := by
  apply Scheme.IdealSheafData.ext
  funext U
  simp only [Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_mul]
