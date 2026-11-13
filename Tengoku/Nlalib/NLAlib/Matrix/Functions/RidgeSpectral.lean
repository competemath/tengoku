import Tengoku.Nlalib.NLAlib.Matrix.Functions.RidgeKernel
import Tengoku.Nlalib.NLAlib.Matrix.Functions.CFCTrace
import Tengoku.Nlalib.NLAlib.Matrix.Spectral.GramSpectralSums

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The finite spectral formula for ridge effective dimension

The ridge kernel is the scalar filter `x / (x + ρ)` applied to the row Gram matrix.
Consequently the effective dimension is a finite sum of
`σ_i(A)² / (σ_i(A)² + ρ)`, is at most `rank A`, and is invariant under transposition.
No singular-vector selector or rank assumption is used.

Source: Cohen–Musco–Musco 2017, ridge scores and Lemma 4, in the transposed general-ρ form;
`sketching_lowrank_routes_2026_10_24/sketching.tex`, ridge derivation.
Atlas: `ridge-leverage-effective-dimension`.
-/

noncomputable section

open scoped Matrix MatrixOrder

namespace NLAlib

variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The ridge kernel is the finite functional calculus filter `x / (x + ρ)` of the row Gram
matrix. This identifies its spectral values without selecting individual singular vectors.
@isnad1 id=eq.1h4v.s7.fdcdcf49fc36 from=translated src=- shape=18f5868a vocab=a8e0f98a
-/
theorem ridgeKernel_eq_cfc (A : Matrix m n ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ridgeKernel A ρ = cfc (fun x : ℝ => x / (x + ρ)) (A * Aᵀ) := by
  let G := A * Aᵀ
  have hG : G.PosSemidef := by
    simpa only [G, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.transpose_transpose] using Matrix.posSemidef_conjTranspose_mul_self Aᵀ
  have hfin (f : ℝ → ℝ) : ContinuousOn f (spectrum ℝ G) := by
    rw [hG.isHermitian.spectrum_real_eq_range_eigenvalues]
    exact (Set.finite_range _).continuousOn f
  have hshift : cfc (fun x : ℝ => x + ρ) G = ridgeGram Aᵀ ρ := by
    have hs := cfc_add_const ρ (fun x : ℝ => x) G (hfin _) hG.isHermitian
    calc
      cfc (fun x : ℝ => x + ρ) G =
          cfc (fun x : ℝ => x) G + algebraMap ℝ (Matrix m m ℝ) ρ := hs
      _ = G + algebraMap ℝ (Matrix m m ℝ) ρ :=
        congrArg (fun X : Matrix m m ℝ => X + algebraMap ℝ (Matrix m m ℝ) ρ)
          (cfc_id' ℝ G hG.isHermitian)
      _ = ridgeGram Aᵀ ρ := by
        simp only [Algebra.algebraMap_eq_smul_one, G, ridgeGram, Matrix.transpose_transpose]
  have hprod : ridgeGram Aᵀ ρ * cfc (fun x : ℝ => x / (x + ρ)) G = G := by
    rw [← hshift, ← cfc_mul _ _ G (hfin _) (hfin _)]
    calc
      cfc (fun x : ℝ => (x + ρ) * (x / (x + ρ))) G = cfc (fun x : ℝ => x) G := by
        apply cfc_congr
        intro x hx
        rw [hG.isHermitian.spectrum_real_eq_range_eigenvalues] at hx
        obtain ⟨i, rfl⟩ := hx
        have hden : hG.isHermitian.eigenvalues i + ρ ≠ 0 :=
          ne_of_gt (add_pos_of_nonneg_of_pos (hG.eigenvalues_nonneg i) hρ)
        field_simp
      _ = G := cfc_id' ℝ G hG.isHermitian
  have hi := (Matrix.isUnit_iff_isUnit_det _).mp (posDef_ridgeGram Aᵀ hρ).isUnit
  have hK : ridgeGram Aᵀ ρ * ridgeKernel A ρ = G := by
    rw [ridgeKernel_eq_one_sub_smul_inv A hρ, Matrix.mul_sub, Matrix.mul_one,
      Matrix.mul_smul, Matrix.mul_nonsing_inv _ hi]
    simp only [ridgeGram, Matrix.transpose_transpose, G]
    abel
  have hh := congrArg (fun X => (ridgeGram Aᵀ ρ)⁻¹ * X) (hK.trans hprod.symm)
  simpa only [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hi, Matrix.one_mul] using hh

end NLAlib
