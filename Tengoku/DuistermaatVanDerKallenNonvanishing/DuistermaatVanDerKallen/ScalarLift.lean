import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Algebra.BigOperators.Field
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Algebraic identities for the scalar normalized-gradient lift in the
manuscript's weighted metric. The separate geometric identification with the
restricted differential operator norm is not assumed or asserted here. -/

open scoped BigOperators ComplexConjugate

namespace DuistermaatVanDerKallen

noncomputable def differentialNormSq {ι : Type*} [Fintype ι]
    (g : ι → ℂ) (h : ι → ℝ) : ℝ := ∑ i, Complex.normSq (g i) / h i

noncomputable def scalarLift {ι : Type*} [Fintype ι]
    (g : ι → ℂ) (h : ι → ℝ) (a : ℂ) (i : ι) : ℂ :=
  a * conj (g i) / ((h i : ℂ) * (differentialNormSq g h : ℂ))

theorem differentialNormSq_nonneg {ι : Type*} [Fintype ι]
    (g : ι → ℂ) (h : ι → ℝ) (hh : ∀ i, 0 < h i) :
    0 ≤ differentialNormSq g h := by
  exact Finset.sum_nonneg fun i _ => div_nonneg (Complex.normSq_nonneg _) (hh i).le

/-- Exact right-inverse identity for a scalar complex differential.-/
theorem scalarLift_right_inverse {ι : Type*} [Fintype ι]
    (g : ι → ℂ) (h : ι → ℝ) (a : ℂ)
    (hnorm : differentialNormSq g h ≠ 0) :
    ∑ i, g i * scalarLift g h a i = a := by
  have hnormc : (differentialNormSq g h : ℂ) ≠ 0 := by exact_mod_cast hnorm
  calc
    ∑ i, g i * scalarLift g h a i =
        ∑ i, a * ((Complex.normSq (g i) : ℂ) / h i) /
          (differentialNormSq g h : ℂ) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [scalarLift, ← Complex.mul_conj]
      ring
    _ = a * (differentialNormSq g h : ℂ) / (differentialNormSq g h : ℂ) := by
      simp [differentialNormSq, Finset.sum_div, Finset.mul_sum]
    _ = a := mul_div_cancel_right₀ a hnormc

/-- Squared metric norm of the lift. All weights are positive.-/
theorem scalarLift_weighted_normSq {ι : Type*} [Fintype ι]
    (g : ι → ℂ) (h : ι → ℝ) (a : ℂ)
    (hh : ∀ i, 0 < h i) (hnorm : differentialNormSq g h ≠ 0) :
    ∑ i, h i * Complex.normSq (scalarLift g h a i) =
      Complex.normSq a / differentialNormSq g h := by
  calc
    ∑ i, h i * Complex.normSq (scalarLift g h a i) =
        ∑ i, (Complex.normSq a / differentialNormSq g h ^ 2) *
          (Complex.normSq (g i) / h i) := by
      apply Finset.sum_congr rfl
      intro i _
      simp only [scalarLift, Complex.normSq_div, Complex.normSq_mul,
        Complex.normSq_conj, Complex.normSq_ofReal]
      field_simp [ne_of_gt (hh i)]
    _ = (Complex.normSq a / differentialNormSq g h ^ 2) *
        differentialNormSq g h := by
      rw [← Finset.mul_sum]
      rfl
    _ = Complex.normSq a / differentialNormSq g h := by
      field_simp

/-- The induced torus-coordinate weights are everywhere positive.-/
theorem torus_weight_pos (z : ℂ) : 0 < (1 : ℝ) + ‖z‖⁻¹ ^ 4 := by positivity

end DuistermaatVanDerKallen
