/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.Bands.Directional.OutputEnergy
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.Bands.Directional.OccupationProfiles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Directional exact-grade operator bounds

The supported-vector and restricted matrix norm bounds for all three directional bands.
Ported from `SparseFockFormal.DirectionalConcrete` at commit
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
-/

namespace NLAlib.SparseSketch

namespace Directional

open scoped Matrix.Norms.L2Operator InnerProductSpace

noncomputable section

variable {d m n : ℕ}

/-- Sharp squared-energy estimate for `Y₊` on an exactly supported vector.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h6v.s8.034272a293f4 from=translated src=- shape=60c4fca7 vocab=681a9d6b
-/
theorem Yplus_energy_of_supported (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    sumSq
      (Matrix.mulVec (Yplus m (Frame.rows F)) x) ≤
      (nu : ℝ) ^ 2 * sumSq x := by
  exact directional_energy_sq_bound
    (Nat.cast_nonneg nu) (sumSq_nonneg x)
    (Yplus_output_energy_le_marked F hx)
    (markedEnergy_one_zero_le F hx)

/-- Sharp denominator-free squared-energy estimate for `Y₀` on an exactly
supported vector.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h6v.s8.a1c3e315c5c2 from=translated src=- shape=9b0dd85b vocab=d7c3ded0
-/
theorem Yzero_two_mul_energy_of_supported (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    2 * sumSq
      (Matrix.mulVec (Yzero m (Frame.rows F)) x) ≤
      (nu : ℝ) ^ 2 * sumSq x := by
  exact directional_energy_half_sq_bound
    (Nat.cast_nonneg nu) (Yzero_output_energy_le_marked F hx)
    (two_mul_markedEnergy_two_zero_le F hx)

/-- Sharp squared-energy estimate for the transpose light hop on an exactly
supported vector.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h6v.s8.f72ca0995dac from=translated src=- shape=60c4fca7 vocab=3cf91638
-/
theorem Hprime_energy_of_supported (F : Frame n d) {nu : ℕ}
    {x : Fin d × Pattern m n → ℝ} (hx : SupportedAtGrade nu x) :
    sumSq
      (Matrix.mulVec (Hprime m (Frame.rows F)) x) ≤
      (nu : ℝ) ^ 2 * sumSq x := by
  exact directional_energy_sq_bound
    (Nat.cast_nonneg nu) (sumSq_nonneg x)
    (Hprime_output_energy_le_marked F hx)
    (markedEnergy_one_zero_le F hx)

/-- Coordinate energy of the genuine restricted `Y₊` matrix.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h6v.s8.04bda9f463f5 from=translated src=- shape=be3ecdcc vocab=5531c8a2
-/
theorem Yplus_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    sumSq
      (Matrix.mulVec
        (Yplus m (Frame.rows F) * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * sumSq x := by
  have h := Yplus_energy_of_supported (m := m) F
    (gradeProjection_supported (d := d) (m := m) (n := n) nu x)
  rw [Matrix.mulVec_mulVec] at h
  calc
    sumSq
        (Matrix.mulVec
          (Yplus m (Frame.rows F) * gradeProjection (d := d) nu) x) ≤
        (nu : ℝ) ^ 2 * sumSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := h
    _ ≤ (nu : ℝ) ^ 2 * sumSq x := by
      exact mul_le_mul_of_nonneg_left
        (gradeProjection_normSq_le nu x) (sq_nonneg (nu : ℝ))

/-- Denominator-free coordinate energy of the genuine restricted `Y₀`
matrix.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h6v.s8.0aa38035c543 from=translated src=- shape=7b520c23 vocab=8ea1c00e
-/
theorem Yzero_restricted_two_mul_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    2 * sumSq
      (Matrix.mulVec
        (Yzero m (Frame.rows F) * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * sumSq x := by
  have h := Yzero_two_mul_energy_of_supported (m := m) F
    (gradeProjection_supported (d := d) (m := m) (n := n) nu x)
  rw [Matrix.mulVec_mulVec] at h
  calc
    2 * sumSq
        (Matrix.mulVec
          (Yzero m (Frame.rows F) * gradeProjection (d := d) nu) x) ≤
        (nu : ℝ) ^ 2 * sumSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := h
    _ ≤ (nu : ℝ) ^ 2 * sumSq x := by
      exact mul_le_mul_of_nonneg_left
        (gradeProjection_normSq_le nu x) (sq_nonneg (nu : ℝ))

/-- Coordinate energy of the genuine restricted transpose-hop matrix.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h6v.s8.f91689d1582a from=translated src=- shape=be3ecdcc vocab=f446291d
-/
theorem Hprime_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    sumSq
      (Matrix.mulVec
        (Hprime m (Frame.rows F) * gradeProjection (d := d) nu) x) ≤
      (nu : ℝ) ^ 2 * sumSq x := by
  have h := Hprime_energy_of_supported (m := m) F
    (gradeProjection_supported (d := d) (m := m) (n := n) nu x)
  rw [Matrix.mulVec_mulVec] at h
  calc
    sumSq
        (Matrix.mulVec
          (Hprime m (Frame.rows F) * gradeProjection (d := d) nu) x) ≤
        (nu : ℝ) ^ 2 * sumSq
          (Matrix.mulVec (gradeProjection (d := d) nu) x) := h
    _ ≤ (nu : ℝ) ^ 2 * sumSq x := by
      exact mul_le_mul_of_nonneg_left
        (gradeProjection_normSq_le nu x) (sq_nonneg (nu : ℝ))

/-- Restricting the mixed preserving band to one grade gives its occupation-energy estimate.
Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h6v.s8.71e7f6a5acad from=translated src=- shape=b3bf47e5 vocab=f57bd7c6
-/
theorem Yzero_restricted_energy (F : Frame n d) (nu : ℕ)
    (x : Fin d × Pattern m n → ℝ) :
    sumSq
      (Matrix.mulVec
        (Yzero m (Frame.rows F) * gradeProjection (d := d) nu) x) ≤
      ((nu : ℝ) / Real.sqrt 2) ^ 2 * sumSq x := by
  have htwo := Yzero_restricted_two_mul_energy (m := m) F nu x
  have hsqrt : (Real.sqrt 2) ^ 2 = (2 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hconstant : ((nu : ℝ) / Real.sqrt 2) ^ 2 =
      (nu : ℝ) ^ 2 / 2 := by
    rw [div_pow, hsqrt]
  rw [hconstant]
  nlinarith [sumSq_nonneg
    (Matrix.mulVec
      (Yzero m (Frame.rows F) * gradeProjection (d := d) nu) x)]

/-- The first directional row-local bound from the paper, as an actual L2
matrix operator norm.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h5v.s7.c0d00d820233 from=translated src=- shape=ec2b5777 vocab=932b6876
-/
theorem norm_Yplus_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Yplus m (Frame.rows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) := by
  exact norm_le_of_normSq_mulVec_le (Nat.cast_nonneg nu)
    (Yplus_restricted_energy (m := m) F nu)

/-- The second directional row-local bound, including the sharp `sqrt 2`
denominator.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h5v.s7.0c7219591034 from=translated src=- shape=3a966061 vocab=04f1556d
-/
theorem norm_Yzero_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Yzero m (Frame.rows F) * gradeProjection (d := d) nu‖ ≤
      (nu : ℝ) / Real.sqrt 2 := by
  exact norm_le_of_normSq_mulVec_le
    (div_nonneg (Nat.cast_nonneg nu) (Real.sqrt_nonneg 2))
    (Yzero_restricted_energy (m := m) F nu)

/-- The transpose light-hop directional row-local bound, as an actual L2
matrix operator norm.

Source: ported from `SparseFockFormal.DirectionalConcrete`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.0h5v.s7.f7f6aaec530c from=translated src=- shape=ec2b5777 vocab=6a18becc
-/
theorem norm_Hprime_restricted_le (F : Frame n d) (nu : ℕ) :
    ‖Hprime m (Frame.rows F) * gradeProjection (d := d) nu‖ ≤ (nu : ℝ) := by
  exact norm_le_of_normSq_mulVec_le (Nat.cast_nonneg nu)
    (Hprime_restricted_energy (m := m) F nu)

end

end Directional

end NLAlib.SparseSketch
