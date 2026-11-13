/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.Bands.Directional.RestrictedBounds
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.Bands.CoefficientBounds
import Tengoku.Nlalib.NLAlib.Matrix.Norms.Core
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Normalized directional mixed-band estimates

This module transports the concrete directional estimates to the named
adjoint operators and then inserts the exact normalization
`sqrt (b - 1) / (s*b)` used by the sparse-stack model.
-/

namespace NLAlib.SparseSketch

namespace Directional

open scoped Matrix.Norms.L2Operator

noncomputable section

variable {d m n : ℕ}

/-- The paper's named `Y₊†` is literally the matrix transpose of `Y₊`.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s5.f6565a79ad78 from=translated src=- shape=f73be4a9 vocab=fa4befdb
-/
@[simp] theorem transpose_Yplus (u : Fin n → Fin d → ℝ) :
    (Yplus m u).transpose = YplusAdj m u := by
  simpa [Yplus, YplusAdj, wordSum, Word.orderedAdjoint, Leg.adjoint] using
    transpose_physicalWordSum (m := m) u (.rUp, .pUp)

/-- Transposing the directional mixed raising adjoint gives the raising band.
Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s5.eb35f5ebe46b from=translated src=- shape=f73be4a9 vocab=fa4befdb
-/
@[simp] theorem transpose_YplusAdj (u : Fin n → Fin d → ℝ) :
    (YplusAdj m u).transpose = Yplus m u := by
  rw [← transpose_Yplus (m := m) u, Matrix.transpose_transpose]

/-- The paper's named `Y₀†` is literally the matrix transpose of `Y₀`.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s5.fa4d3d7fe3bf from=translated src=- shape=f73be4a9 vocab=38b69211
-/
@[simp] theorem transpose_Yzero (u : Fin n → Fin d → ℝ) :
    (Yzero m u).transpose = YzeroAdj m u := by
  simpa [Yzero, YzeroAdj, wordSum, Word.orderedAdjoint, Leg.adjoint] using
    transpose_physicalWordSum (m := m) u (.rDown, .pUp)

/-- Transposing the directional mixed preserving adjoint gives the preserving band.
Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h4v.s5.5a5f27f94a41 from=translated src=- shape=f73be4a9 vocab=38b69211
-/
@[simp] theorem transpose_YzeroAdj (u : Fin n → Fin d → ℝ) :
    (YzeroAdj m u).transpose = Yzero m u := by
  rw [← transpose_Yzero (m := m) u, Matrix.transpose_transpose]

/-- The directional mixed raising adjoint has grade shift minus two.
Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=isfullgr.0h4v.s4.6f47bba2e4b4 from=translated src=- shape=d9805cfa vocab=f1517fe2
-/
theorem YplusAdj_homogeneous (F : Frame n d) :
    IsFullGradeShift (-2) (YplusAdj m (Frame.rows F)) := by
  simpa [YplusAdj, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous (m := m) (Frame.rows F) (.pDown, .rDown)

/-- The directional mixed preserving adjoint has grade shift zero.
Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=isfullgr.0h4v.s4.1fb6955195f9 from=translated src=- shape=22f4b803 vocab=107ba7a9
-/
theorem YzeroAdj_homogeneous (F : Frame n d) :
    IsFullGradeShift 0 (YzeroAdj m (Frame.rows F)) := by
  simpa [YzeroAdj, wordSum, Word.degree, Leg.degree] using
    physicalWordSum_homogeneous (m := m) (Frame.rows F) (.pDown, .rUp)

/-- A homogeneous matrix intertwines the two compatible exact-grade
projections.  This is stronger than merely inserting an output projection
after an already restricted operator.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.2h7v.s7.72d43b304987 from=translated src=- shape=95be8c5b vocab=7d51840c
-/
theorem gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
    {delta : ℤ} {A : FullOp d m n}
    (hA : IsFullGradeShift delta A) (mu nu : ℕ)
    (hcompatible : (mu : ℤ) = (nu : ℤ) + delta) :
    gradeProjection (d := d) mu * A = A * gradeProjection nu := by
  classical
  ext out inp
  simp only [gradeProjection, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hentry : A out inp = 0
  · simp [hentry]
  · have hrel := homogeneous_grade_relation hA hentry
    have hiff : out.2.grade = mu ↔ inp.2.grade = nu := by
      constructor
      · intro hout
        have hinInt : (inp.2.grade : ℤ) = (nu : ℤ) := by
          rw [hout] at hrel
          omega
        exact_mod_cast hinInt
      · intro hin
        have houtInt : (out.2.grade : ℤ) = (mu : ℤ) := by
          rw [hin] at hrel
          omega
        exact_mod_cast houtInt
    by_cases hout : out.2.grade = mu
    · simp [hout, hiff.mp hout]
    · have hin : inp.2.grade ≠ nu := fun h ↦ hout (hiff.mpr h)
      simp [hout, hin]

/-- Exact shifted adjoint bound: on grade `nu+2`, `Y₊†` has the same norm as
`Y₊` on grade `nu`.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h5v.s7.4464eb60883d from=translated src=- shape=151f7750 vocab=e5ed9d09
-/
theorem norm_YplusAdj_restricted_add_two_le (F : Frame n d) (nu : ℕ) :
    ‖YplusAdj m (Frame.rows F) * gradeProjection (d := d) (nu + 2)‖ ≤
      (nu : ℝ) := by
  calc
    ‖YplusAdj m (Frame.rows F) * gradeProjection (d := d) (nu + 2)‖ =
        ‖(YplusAdj m (Frame.rows F) *
          gradeProjection (d := d) (nu + 2)).transpose‖ := by
      exact (specNorm_transpose
        (YplusAdj m (Frame.rows F) *
          gradeProjection (d := d) (nu + 2))).symm
    _ = ‖gradeProjection (d := d) (nu + 2) *
          Yplus m (Frame.rows F)‖ := by
      rw [Matrix.transpose_mul, transpose_YplusAdj,
        gradeProjection_transpose]
    _ = ‖Yplus m (Frame.rows F) * gradeProjection (d := d) nu‖ := by
      rw [gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
        (Yplus_homogeneous (m := m) F) (nu + 2) nu (by norm_num)]
    _ ≤ (nu : ℝ) := norm_Yplus_restricted_le (m := m) F nu

/-- Uniform same-grade notation for the adjoint bound.  The two bottom grades
vanish; above them the exact shifted estimate is even smaller than `nu`.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h5v.s7.968f2c1be907 from=translated src=- shape=ec2b5777 vocab=5ced1dba
-/
theorem norm_YplusAdj_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖YplusAdj m (Frame.rows F) * gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) := by
  by_cases hnu : 2 ≤ nu
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hnu
    have h := norm_YplusAdj_restricted_add_two_le (m := m) F k
    calc
      ‖YplusAdj m (Frame.rows F) * gradeProjection (d := d) (2 + k)‖ =
          ‖YplusAdj m (Frame.rows F) * gradeProjection (d := d) (k + 2)‖ := by
        rw [Nat.add_comm]
      _ ≤ (k : ℝ) := h
      _ ≤ ((2 + k : ℕ) : ℝ) := by
        exact_mod_cast (show k ≤ 2 + k by omega)
  · have himpossible : ∀ mu : ℕ,
        (mu : ℤ) ≠ (nu : ℤ) + (-2) := by
      intro mu hmu
      have hnuLt : nu < 2 := Nat.lt_of_not_ge hnu
      have hmuNonneg : (0 : ℤ) ≤ (mu : ℤ) := by positivity
      omega
    have hz := input_grade_vanishes_of_no_output
      (YplusAdj_homogeneous (m := m) F) nu himpossible
    rw [hz]
    simp

/-- Since `Y₀` preserves grade, transpose invariance gives exactly the same
restricted norm for its named adjoint.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h5v.s7.20298ee99753 from=translated src=- shape=3a966061 vocab=1bfa9870
-/
theorem norm_YzeroAdj_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖YzeroAdj m (Frame.rows F) * gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) / Real.sqrt 2 := by
  calc
    ‖YzeroAdj m (Frame.rows F) * gradeProjection (d := d) nu‖ =
        ‖(YzeroAdj m (Frame.rows F) *
          gradeProjection (d := d) nu).transpose‖ := by
      exact (specNorm_transpose
        (YzeroAdj m (Frame.rows F) *
          gradeProjection (d := d) nu)).symm
    _ = ‖gradeProjection (d := d) nu * Yzero m (Frame.rows F)‖ := by
      rw [Matrix.transpose_mul, transpose_YzeroAdj,
        gradeProjection_transpose]
    _ = ‖Yzero m (Frame.rows F) * gradeProjection (d := d) nu‖ := by
      rw [gradeProjection_mul_eq_mul_gradeProjection_of_homogeneous
        (Yzero_homogeneous (m := m) F) nu nu (by norm_num)]
    _ ≤ (nu : ℝ) / Real.sqrt 2 := norm_Yzero_restricted_le (m := m) F nu

/-- Exact L2-norm scaling for the normalized heavy-light coefficient.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h7v.s9.8b0093ffa371 from=translated src=- shape=de7eae87 vocab=7b90ecf2
-/
theorem norm_normalized_directional_term_eq {s b : ℕ}
    (A : FullOp d m n) (P : FullOp d m n) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • A)) * P‖ =
      (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ))) * ‖A * P‖ := by
  simp only [Matrix.smul_mul, norm_smul, Real.norm_eq_abs]
  rw [abs_of_nonneg (by positivity :
      0 ≤ (1 : ℝ) / (((s * b : ℕ) : ℝ))),
    abs_of_nonneg (Real.sqrt_nonneg _)]
  ring

/-- Normalized `Y₊` contribution at exactly the paper constant `nu/s`.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h6v.s9.39d9658d637c from=translated src=- shape=f1e4d97a vocab=c634ef08
-/
theorem norm_normalized_Yplus_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • Yplus (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) / s := by
  rw [norm_normalized_directional_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖Yplus (s * b) (Frame.rows F) * gradeProjection (d := d) nu‖ ≤
        Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) * (nu : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (norm_Yplus_restricted_le (m := s * b) F nu)
        rho_div_stack_nonneg
    _ ≤ (nu : ℝ) / s := directional_absorb hs hb

/-- Normalized `Y₊†` contribution, with the same uniform paper constant.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h6v.s9.c6e51c5e867b from=translated src=- shape=f1e4d97a vocab=b2adfd23
-/
theorem norm_normalized_YplusAdj_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • YplusAdj (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) / s := by
  rw [norm_normalized_directional_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖YplusAdj (s * b) (Frame.rows F) * gradeProjection (d := d) nu‖ ≤
        Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) * (nu : ℝ) := by
      exact mul_le_mul_of_nonneg_left
        (norm_YplusAdj_restricted_le (m := s * b) F nu)
        rho_div_stack_nonneg
    _ ≤ (nu : ℝ) / s := directional_absorb hs hb

/-- Each normalized `Y₀` orientation contributes at most
`(nu/s)/sqrt 2`.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h6v.s9.41bf68825ba4 from=translated src=- shape=adf07b4c vocab=a69afa75
-/
theorem norm_normalized_Yzero_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • Yzero (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu‖ ≤
      ((nu : ℝ) / s) / Real.sqrt 2 := by
  rw [norm_normalized_directional_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖Yzero (s * b) (Frame.rows F) * gradeProjection (d := d) nu‖ ≤
        Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
          ((nu : ℝ) / Real.sqrt 2) := by
      exact mul_le_mul_of_nonneg_left
        (norm_Yzero_restricted_le (m := s * b) F nu)
        rho_div_stack_nonneg
    _ = (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
          (nu : ℝ)) / Real.sqrt 2 := by ring
    _ ≤ ((nu : ℝ) / s) / Real.sqrt 2 := by
      exact div_le_div_of_nonneg_right (directional_absorb hs hb)
        (Real.sqrt_nonneg 2)

/-- The named normalized `Y₀†` orientation has the identical constant.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h6v.s9.db008eec0469 from=translated src=- shape=adf07b4c vocab=d484d1da
-/
theorem norm_normalized_YzeroAdj_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) • YzeroAdj (s * b) (Frame.rows F))) *
          gradeProjection (d := d) nu‖ ≤
      ((nu : ℝ) / s) / Real.sqrt 2 := by
  rw [norm_normalized_directional_term_eq]
  calc
    Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
        ‖YzeroAdj (s * b) (Frame.rows F) * gradeProjection (d := d) nu‖ ≤
        Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
          ((nu : ℝ) / Real.sqrt 2) := by
      exact mul_le_mul_of_nonneg_left
        (norm_YzeroAdj_restricted_le (m := s * b) F nu)
        rho_div_stack_nonneg
    _ = (Real.sqrt ((b : ℝ) - 1) / (((s * b : ℕ) : ℝ)) *
          (nu : ℝ)) / Real.sqrt 2 := by ring
    _ ≤ ((nu : ℝ) / s) / Real.sqrt 2 := by
      exact div_le_div_of_nonneg_right (directional_absorb hs hb)
        (Real.sqrt_nonneg 2)

/-- The two grade-preserving `Y` orientations together contribute exactly the
paper's `sqrt 2 * nu/s` allowance.

Source: ported from `SparseFockFormal.DirectionalNormalized`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h6v.s9.5658e4a53830 from=translated src=- shape=87c753d4 vocab=f5516492
-/
theorem norm_normalized_Yzero_pair_restricted_le (F : Frame n d)
    (s b nu : ℕ) (hs : 0 < s) (hb : 1 < b) :
    ‖((1 / (((s * b : ℕ) : ℝ))) •
        (Real.sqrt ((b : ℝ) - 1) •
          (Yzero (s * b) (Frame.rows F) +
            YzeroAdj (s * b) (Frame.rows F)))) *
          gradeProjection (d := d) nu‖ ≤
      Real.sqrt 2 * ((nu : ℝ) / s) := by
  have hsplit :
      ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) •
            (Yzero (s * b) (Frame.rows F) +
              YzeroAdj (s * b) (Frame.rows F)))) *
            gradeProjection (d := d) nu =
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) • Yzero (s * b) (Frame.rows F))) *
            gradeProjection (d := d) nu +
        ((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) • YzeroAdj (s * b) (Frame.rows F))) *
            gradeProjection (d := d) nu := by
    simp only [smul_add, add_mul]
  rw [hsplit]
  calc
    _ ≤
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) • Yzero (s * b) (Frame.rows F))) *
            gradeProjection (d := d) nu‖ +
        ‖((1 / (((s * b : ℕ) : ℝ))) •
          (Real.sqrt ((b : ℝ) - 1) • YzeroAdj (s * b) (Frame.rows F))) *
            gradeProjection (d := d) nu‖ := norm_add_le _ _
    _ ≤ 2 * (((nu : ℝ) / s) / Real.sqrt 2) := by
      have h₁ := norm_normalized_Yzero_restricted_le F s b nu hs hb
      have h₂ := norm_normalized_YzeroAdj_restricted_le F s b nu hs hb
      linarith
    _ = Real.sqrt 2 * ((nu : ℝ) / s) := by
      have hsqrtPos : 0 < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
      have hsqrtSq : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
        Real.sq_sqrt (by norm_num)
      field_simp [ne_of_gt hsqrtPos]
      nlinarith

end

end Directional

end NLAlib.SparseSketch
