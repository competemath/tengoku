import Tengoku.MagicSquaresFieldsLean.MagicSquares.Weil.SharpInterface
import Tengoku.MagicSquaresFieldsLean.MagicSquares.QuadraticCharacterSums

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The real absolute value of the quadratic character is at most one.
@isnad1 id=le.0h2v.s5.31c593d9dc13 from=translated src=- shape=e7b0a4c6 vocab=0bcd64c4
-/
theorem quadraticChar_abs_le_one (a : F) : |(quadraticChar F a : ℝ)| ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  · rcases quadraticChar_dichotomy ha with h | h <;> simp [h]

/-- Factoring the leading coefficients out of a product of affine forms.
@isnad1 id=eq.1h3v.s8.64d42cf5974e from=translated src=- shape=d3701991 vocab=d091dbda
-/
theorem quadraticChar_affine_product_sum {ι : Type*} [Fintype ι]
    (coeff : ι → F) (hcoeff : ∀ i, coeff i ≠ 0) :
    (∑ t : F, quadraticChar F (∏ i, (1 + coeff i * t))) =
      quadraticChar F (∏ i, coeff i) *
        ∑ t : F, quadraticChar F (∏ i, (t - -(coeff i)⁻¹)) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  rw [← map_mul, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  simp [sub_neg_eq_add, mul_add, mul_inv_cancel₀ (hcoeff i), add_comm]

/-- A single nonconstant affine quadratic-character sum vanishes.
@isnad1 id=eq.2h2v.s7.92d0a577fb9b from=translated src=- shape=59b9747e vocab=13207fad
-/
theorem quadraticChar_affine_sum (hodd : ringChar F ≠ 2)
    {a : F} (ha : a ≠ 0) :
    ∑ t : F, quadraticChar F (1 + a * t) = 0 := by
  have hfactor (t : F) : 1 + a * t = a * (t - -a⁻¹) := by
    simp [sub_neg_eq_add, mul_add, mul_inv_cancel₀ ha, add_comm]
  simp_rw [hfactor, map_mul, ← Finset.mul_sum,
    quadraticChar_linear_shift_sum hodd, mul_zero]

/-- Exact quadratic contribution of two distinct nonconstant affine forms.
@isnad1 id=eq.4h3v.s8.250759bbad0a from=translated src=- shape=891ee562 vocab=275268f7
-/
theorem quadraticChar_affine_pair_sum (hodd : ringChar F ≠ 2)
    {a b : F} (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∑ t : F, quadraticChar F ((1 + a * t) * (1 + b * t)) =
      -quadraticChar F (a * b) := by
  have hfactor (t : F) : (1 + a * t) * (1 + b * t) =
      (a * b) * ((t - -a⁻¹) * (t - -b⁻¹)) := by
    have h1 : 1 + a * t = a * (t - -a⁻¹) := by
      simp [sub_neg_eq_add, mul_add, mul_inv_cancel₀ ha, add_comm]
    have h2 : 1 + b * t = b * (t - -b⁻¹) := by
      simp [sub_neg_eq_add, mul_add, mul_inv_cancel₀ hb, add_comm]
    rw [h1, h2]
    ring
  have hne : -a⁻¹ ≠ -b⁻¹ := by simpa using hab
  simp_rw [hfactor, map_mul]
  rw [← Finset.mul_sum]
  simp_rw [← map_mul]
  rw [quadraticChar_two_root_sum hodd hne]
  ring

/-- The sharp split bound transfers to any nonempty family of distinct,
nonzero affine coefficients.
@isnad1 id=le.4h3v.s7.63c48f5a4908 from=translated src=- shape=8077d83f vocab=fa0379b2
-/
theorem HasSplitQuadraticWeilBound.affine
    (hWeil : HasSplitQuadraticWeilBound F)
    {ι : Type*} [Fintype ι] (coeff : ι → F)
    (hpos : 0 < Fintype.card ι) (hinj : Function.Injective coeff)
    (hcoeff : ∀ i, coeff i ≠ 0) :
    |((∑ t : F, quadraticChar F (∏ i, (1 + coeff i * t)) : ℤ) : ℝ)| ≤
      (Fintype.card ι - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ) := by
  classical
  let e := (Fintype.equivFin ι).symm
  have hrootinj : Function.Injective (fun i : Fin (Fintype.card ι) => -(coeff (e i))⁻¹) := by
    intro i j hij
    apply e.injective
    apply hinj
    simpa using hij
  have h := hWeil (Fintype.card ι) (fun i => -(coeff (e i))⁻¹) hpos hrootinj
  have hprod (t : F) :
      (∏ i : Fin (Fintype.card ι), (t - -(coeff (e i))⁻¹)) =
        ∏ i : ι, (t - -(coeff i)⁻¹) := e.prod_comp (fun i : ι => t - -(coeff i)⁻¹)
  simp_rw [hprod] at h
  have hnorm :
      |((∑ t : F, quadraticChar F (∏ i, (t - -(coeff i)⁻¹)) : ℤ) : ℝ)| ≤
        (Fintype.card ι - 1 : ℕ) * Real.sqrt (Fintype.card F : ℝ) := by
    simpa only [← Int.cast_sum, Complex.norm_intCast] using h
  rw [quadraticChar_affine_product_sum coeff hcoeff, Int.cast_mul, abs_mul]
  calc
    _ ≤ 1 * |((∑ t : F, quadraticChar F (∏ i, (t - -(coeff i)⁻¹)) : ℤ) : ℝ)| :=
      mul_le_mul_of_nonneg_right (quadraticChar_abs_le_one _) (abs_nonneg _)
    _ ≤ _ := by simpa using hnorm

end MagicSquares
