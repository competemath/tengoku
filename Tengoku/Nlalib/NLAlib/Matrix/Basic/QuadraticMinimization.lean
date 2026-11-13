import Tengoku.Nlalib.NLAlib.Matrix.Basic.QuadForm
import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-!
# Finite Hermitian quadratic minimization

Completing the square gives the unique minimizer of a positive definite
Hermitian quadratic. The objective is real-valued over either real or
complex coordinates. Supports Tikhonov regularization and reduced-Hessian
constrained optimization.
-/
noncomputable section
open Matrix
open scoped Matrix ComplexOrder
namespace NLAlib
variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The real Hermitian quadratic objective `xᴴHx/2 - Re(fᴴx)`.-/
def quadraticObjective (H : Matrix n n 𝕜) (f x : n → 𝕜) : ℝ :=
  (1 / 2 : ℝ) * RCLike.re (quadForm H x) - RCLike.re (star f ⬝ᵥ x)

/-- Completing the square at a solution of the Hermitian normal equation.
@isnad1 id=eq.2h6v.s8.a998f2768631 from=translated src=- shape=800af310 vocab=80959d3b
-/
theorem quadraticObjective_add_of_mulVec_eq {H : Matrix n n 𝕜} (hH : H.IsHermitian)
    {f x : n → 𝕜} (hx : H *ᵥ x = f) (y : n → 𝕜) :
    quadraticObjective H f (x + y) = quadraticObjective H f x +
      (1 / 2 : ℝ) * RCLike.re (quadForm H y) := by
  have hc : star f ⬝ᵥ y = star x ⬝ᵥ (H *ᵥ y) := by
    rw [← hx, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, hH.eq]
  have hq := hH.re_quadForm_smul_add_smul x y 1 1
  simp only [RCLike.ofReal_one, one_smul, one_pow, one_mul] at hq
  unfold quadraticObjective
  rw [hq, dotProduct_add, map_add, hc]
  ring

/-- A positive definite quadratic has a strict, unique minimum at each
solution of its normal equation.
@isnad1 id=and.2h5v.s7.ea0e5c98ba00 from=translated src=- shape=598c8a3d vocab=704a3ef0
-/
theorem quadraticObjective_minimizer_of_posDef {H : Matrix n n 𝕜} (hH : H.PosDef)
    {f x : n → 𝕜} (hx : H *ᵥ x = f) :
    (∀ y, quadraticObjective H f x ≤ quadraticObjective H f y) ∧
      ∀ y, quadraticObjective H f y ≤ quadraticObjective H f x → y = x := by
  have he (y : n → 𝕜) : quadraticObjective H f y = quadraticObjective H f x +
      (1 / 2 : ℝ) * RCLike.re (quadForm H (y - x)) := by
    simpa only [add_sub_cancel] using
      quadraticObjective_add_of_mulVec_eq hH.isHermitian hx (y - x)
  constructor
  · intro y
    rw [he y]
    have hn := hH.posSemidef.re_quadForm_nonneg (y - x)
    linarith
  · intro y hy
    by_contra hne
    have hpos : 0 < RCLike.re (quadForm H (y - x)) :=
      (RCLike.pos_iff.mp (hH.quadForm_pos (sub_ne_zero.mpr hne))).1
    rw [he y] at hy
    linarith

/-- The unique minimizer of a positive definite Hermitian quadratic is
`H⁻¹f`, with the total matrix inverse justified by positive definiteness.
@isnad1 id=and.1h4v.s7.bf5bd67a3b9e from=translated src=- shape=fa22e1b5 vocab=410505af
-/
theorem quadraticObjective_inv_mulVec_minimizer {H : Matrix n n 𝕜} (hH : H.PosDef)
    (f : n → 𝕜) :
    (∀ y, quadraticObjective H f (H⁻¹ *ᵥ f) ≤ quadraticObjective H f y) ∧
      ∀ y, quadraticObjective H f y ≤ quadraticObjective H f (H⁻¹ *ᵥ f) → y = H⁻¹ *ᵥ f := by
  apply quadraticObjective_minimizer_of_posDef hH
  rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _
    ((Matrix.isUnit_iff_isUnit_det _).mp hH.isUnit), Matrix.one_mulVec]

end NLAlib
