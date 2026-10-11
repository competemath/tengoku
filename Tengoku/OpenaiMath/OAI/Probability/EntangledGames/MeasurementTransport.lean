import Tengoku.OpenaiMath.OAI.Probability.EntangledGames.Purification

namespace OAI

universe u_n u_m u_A

open scoped BigOperators ComplexOrder
open scoped MatrixOrder
open Matrix
open MeasureTheory Filter Set
open scoped Topology
open scoped Matrix.Norms.Elementwise

noncomputable section
open scoped BigOperators MatrixOrder ComplexOrder
open Matrix

namespace ThresholdParallelRepetition.MeasurementTransport
variable {n : Type u_n} [Fintype n] [DecidableEq n]

def supportInverse (T : Matrix n n ℂ) : Matrix n n ℂ := cfc (fun t : ℝ => t⁻¹) T

lemma supportInverse_isHermitian (T : Matrix n n ℂ) : (supportInverse T).IsHermitian :=
  (cfc_predicate (fun t : ℝ => t⁻¹) T).isHermitian

lemma supportInverse_mul_self_mul {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    supportInverse T * T * supportInverse T = supportInverse T := by
  have hid : cfc (fun t : ℝ => t) T = T := cfc_id' ℝ T hT
  change cfc (fun t : ℝ => t⁻¹) T * T * cfc (fun t : ℝ => t⁻¹) T = _
  calc
    _ = cfc (fun t : ℝ => t⁻¹) T * cfc (fun t : ℝ => t) T *
        cfc (fun t : ℝ => t⁻¹) T := by rw [hid]
    _ = cfc (fun t : ℝ => t⁻¹ * t * t⁻¹) T := by
      erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _),
        ← cfc_mul (fun t : ℝ => t⁻¹ * t) (fun t : ℝ => t⁻¹) T
          (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = _ := by apply cfc_congr; intro t _; by_cases ht : t = 0 <;> simp [ht]

lemma self_mul_supportInverse_mul {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    T * supportInverse T * T = T := by
  have hid : cfc (fun t : ℝ => t) T = T := cfc_id' ℝ T hT
  change T * cfc (fun t : ℝ => t⁻¹) T * T = T
  calc
    _ = cfc (fun t : ℝ => t) T * cfc (fun t : ℝ => t⁻¹) T *
        cfc (fun t : ℝ => t) T := by rw [hid]
    _ = cfc (fun t : ℝ => t * t⁻¹ * t) T := by
      erw [← cfc_mul (fun t : ℝ => t) (fun t : ℝ => t⁻¹) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _),
        ← cfc_mul (fun t : ℝ => t * t⁻¹) (fun t : ℝ => t) T
          (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = cfc (fun t : ℝ => t) T := by apply cfc_congr; intro t _; simp
    _ = T := hid

lemma supportInverse_commute {T : Matrix n n ℂ} (hT : T.IsHermitian) :
    supportInverse T * T = T * supportInverse T := by
  have hid : cfc (fun t : ℝ => t) T = T := cfc_id' ℝ T hT
  change cfc (fun t : ℝ => t⁻¹) T * T = T * cfc (fun t : ℝ => t⁻¹) T
  calc
    _ = cfc (fun t : ℝ => t⁻¹) T * cfc (fun t : ℝ => t) T := by rw [hid]
    _ = cfc (fun t : ℝ => t⁻¹ * t) T := by
      erw [← cfc_mul (fun t : ℝ => t⁻¹) (fun t : ℝ => t) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = cfc (fun t : ℝ => t * t⁻¹) T := by
      apply cfc_congr; intro t _; exact mul_comm _ _
    _ = cfc (fun t : ℝ => t) T * cfc (fun t : ℝ => t⁻¹) T := by
      erw [cfc_mul (fun t : ℝ => t) (fun t : ℝ => t⁻¹) T
        (T.finite_real_spectrum.continuousOn _) (T.finite_real_spectrum.continuousOn _)]
    _ = _ := by rw [hid]

variable {m : Type u_m} [Fintype m] [DecidableEq m]

def rangeProjection (F : Matrix m n ℂ) : Matrix m m ℂ :=
  F * supportInverse (Fᴴ * F) * Fᴴ

omit [DecidableEq m] in
lemma rangeProjection_isHermitian (F : Matrix m n ℂ) :
    (rangeProjection F).IsHermitian := by
  unfold Matrix.IsHermitian
  simp only [rangeProjection, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    (supportInverse_isHermitian _).eq, Matrix.mul_assoc]

omit [DecidableEq m] in
lemma rangeProjection_sq (F : Matrix m n ℂ) :
    rangeProjection F * rangeProjection F = rangeProjection F := by
  have h := supportInverse_mul_self_mul (Matrix.isHermitian_conjTranspose_mul_self F)
  unfold rangeProjection
  calc
    _ = F * (supportInverse (Fᴴ * F) * (Fᴴ * F) * supportInverse (Fᴴ * F)) * Fᴴ := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [h]

lemma complement_posSemidef (F : Matrix m n ℂ) : (1 - rangeProjection F).PosSemidef := by
  have h : (1 - rangeProjection F)ᴴ * (1 - rangeProjection F) = 1 - rangeProjection F := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, (rangeProjection_isHermitian F).eq,
      Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
      Matrix.mul_one, rangeProjection_sq]
    abel
  rw [← h]
  exact Matrix.posSemidef_conjTranspose_mul_self _

lemma complement_pullback (F : Matrix m n ℂ) :
    Fᴴ * (1 - rangeProjection F) * F = 0 := by
  have h := self_mul_supportInverse_mul (Matrix.isHermitian_conjTranspose_mul_self F)
  rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul]
  change Fᴴ * F - Fᴴ * (F * supportInverse (Fᴴ * F) * Fᴴ) * F = 0
  rw [show Fᴴ * (F * supportInverse (Fᴴ * F) * Fᴴ) * F =
      (Fᴴ * F) * supportInverse (Fᴴ * F) * (Fᴴ * F) by simp only [Matrix.mul_assoc], h,
    sub_self]

variable {A : Type u_A} [Fintype A] [DecidableEq A]

def transportedEffect (F : Matrix m n ℂ) (G : A → Matrix n n ℂ) (a₀ a : A) : Matrix m m ℂ :=
  (F * supportInverse (Fᴴ * F)) * G a * (F * supportInverse (Fᴴ * F))ᴴ +
    if a = a₀ then 1 - rangeProjection F else 0

omit [Fintype A] in
lemma transportedEffect_pos (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∀ a, (G a).PosSemidef) (a₀ a : A) : (transportedEffect F G a₀ a).PosSemidef := by
  apply ((hG a).mul_mul_conjTranspose_same _).add
  split_ifs
  · exact complement_posSemidef F
  · exact Matrix.PosSemidef.zero

lemma transportedEffect_sum (F : Matrix m n ℂ) (G : A → Matrix n n ℂ)
    (hG : ∑ a, G a = Fᴴ * F) (a₀ : A) : ∑ a, transportedEffect F G a₀ a = 1 := by
  have h := supportInverse_mul_self_mul (Matrix.isHermitian_conjTranspose_mul_self F)
  simp only [transportedEffect, Finset.sum_add_distrib, ← Matrix.sum_mul, ← Matrix.mul_sum,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true, hG, Matrix.conjTranspose_mul,
    (supportInverse_isHermitian _).eq]
  rw [show (F * supportInverse (Fᴴ * F)) * (Fᴴ * F) * (supportInverse (Fᴴ * F) * Fᴴ) =
      F * (supportInverse (Fᴴ * F) * (Fᴴ * F) * supportInverse (Fᴴ * F)) * Fᴴ by
      simp only [Matrix.mul_assoc], h]
  unfold rangeProjection
  abel

end ThresholdParallelRepetition.MeasurementTransport

end

end OAI
