/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.Cutoff.Ball
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian
public import Tengoku

/-!
# Kernels Basic

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped BigOperators Topology
open Filter MeasureTheory

namespace CKN.Foundation.Harmonic.Commutator

noncomputable section

/-- Squared Euclidean radius used in Newtonian derivative formulas. -/
def q (x : CKN.Vec 3) : ℝ := CKN.vecNormSq x

/-- The inverse Euclidean radius, extended by zero at the origin. -/
def radialInverse (x : CKN.Vec 3) : ℝ :=
  if x = 0 then 0 else q x ^ (-(1 : ℝ) / 2)

/-- First derivative formula for the inverse Euclidean radius. -/
def firstFormula (i : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -x i * q x ^ (-(3 : ℝ) / 2)

/-- Second derivative formula for the inverse Euclidean radius. -/
def secondFormula (i j : Fin 3) (x : CKN.Vec 3) : ℝ :=
  3 * x i * x j * q x ^ (-(5 : ℝ) / 2) -
    (if i = j then 1 else 0) * q x ^ (-(3 : ℝ) / 2)

/-- Continuous linear differential of a power of the squared radius. -/
def qDerivative (p : ℝ) (x : CKN.Vec 3) : CKN.Vec 3 →L[ℝ] ℝ :=
  (p * q x ^ (p - 1)) •
    ∑ k : Fin 3, (2 * x k) •
      (ContinuousLinearMap.proj k : CKN.Vec 3 →L[ℝ] ℝ)

/-- Continuous linear differential of the second inverse-radius derivative formula. -/
def secondDerivative (i j : Fin 3) (x : CKN.Vec 3) : CKN.Vec 3 →L[ℝ] ℝ :=
  3 • ((x i * x j) • qDerivative (-(5 : ℝ) / 2) x +
    (q x ^ (-(5 : ℝ) / 2)) •
      (x i • (ContinuousLinearMap.proj j : CKN.Vec 3 →L[ℝ] ℝ) +
        x j • (ContinuousLinearMap.proj i : CKN.Vec 3 →L[ℝ] ℝ))) -
    (if i = j then 1 else 0) • qDerivative (-(3 : ℝ) / 2) x

private theorem q_rpow_eq_norm_rpow {x : CKN.Vec 3} (_ : x ≠ 0)
    (p : ℝ) : q x ^ p = (CKN.vecEuclideanNorm x) ^ (2 * p) := by
  rw [q, ← CKN.vecEuclideanNorm_sq]
  rw [← Real.rpow_natCast]
  rw [Real.rpow_mul (CKN.vecEuclideanNorm_nonneg x)]
  norm_num

private theorem q_rpow_neg_five {x : CKN.Vec 3} (hx : x ≠ 0) :
    q x ^ (-(5 : ℝ) / 2) = (CKN.vecEuclideanNorm x ^ 5)⁻¹ := by
  rw [q_rpow_eq_norm_rpow hx (-(5 : ℝ) / 2)]
  rw [show 2 * (-(5 : ℝ) / 2) = -(5 : ℝ) by ring]
  rw [Real.rpow_neg (CKN.vecEuclideanNorm_nonneg x)]
  norm_num

private theorem q_rpow_neg_seven {x : CKN.Vec 3} (hx : x ≠ 0) :
    q x ^ (-(7 : ℝ) / 2) = (CKN.vecEuclideanNorm x ^ 7)⁻¹ := by
  rw [q_rpow_eq_norm_rpow hx (-(7 : ℝ) / 2)]
  rw [show 2 * (-(7 : ℝ) / 2) = -(7 : ℝ) by ring]
  rw [Real.rpow_neg (CKN.vecEuclideanNorm_nonneg x)]
  norm_num

private theorem q_rpow_neg_nine {x : CKN.Vec 3} (hx : x ≠ 0) :
    q x ^ (-(9 : ℝ) / 2) = (CKN.vecEuclideanNorm x ^ 9)⁻¹ := by
  rw [q_rpow_eq_norm_rpow hx (-(9 : ℝ) / 2)]
  rw [show 2 * (-(9 : ℝ) / 2) = -(9 : ℝ) by ring]
  rw [Real.rpow_neg (CKN.vecEuclideanNorm_nonneg x)]
  norm_num

/-- The third derivative of the inverse Euclidean radius, in the convention
used by the Newtonian kernel. -/
def inverseThirdFormula (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -15 * x m * x j * x l * (CKN.vecEuclideanNorm x ^ 7)⁻¹ +
    3 * ((if m = l then 1 else 0) * x j +
      (if m = j then 1 else 0) * x l +
      (if l = j then 1 else 0) * x m) *
      (CKN.vecEuclideanNorm x ^ 5)⁻¹

/-- Third inverse-radius derivative expressed using powers of the squared radius. -/
def inverseThirdFormulaQ (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -15 * x m * x j * x l * q x ^ (-(7 : ℝ) / 2) +
    3 * ((if m = l then 1 else 0) * x j +
      (if m = j then 1 else 0) * x l +
      (if l = j then 1 else 0) * x m) * q x ^ (-(5 : ℝ) / 2)

/-- Continuous linear differential of the third inverse-radius derivative formula. -/
def inverseThirdFormulaQDerivative (m j l : Fin 3) (x : CKN.Vec 3) :
    CKN.Vec 3 →L[ℝ] ℝ :=
  (-15 : ℝ) • (
      q x ^ (-(7 : ℝ) / 2) •
          ((x j * x l) • (ContinuousLinearMap.proj m : CKN.Vec 3 →L[ℝ] ℝ) +
            (x m * x l) • (ContinuousLinearMap.proj j : CKN.Vec 3 →L[ℝ] ℝ) +
            (x m * x j) • (ContinuousLinearMap.proj l : CKN.Vec 3 →L[ℝ] ℝ)) +
        (x m * x j * x l) • qDerivative (-(7 : ℝ) / 2) x) +
    (3 : ℝ) • (
      q x ^ (-(5 : ℝ) / 2) •
          ((if m = l then 1 else 0) •
              (ContinuousLinearMap.proj j : CKN.Vec 3 →L[ℝ] ℝ) +
            (if m = j then 1 else 0) •
              (ContinuousLinearMap.proj l : CKN.Vec 3 →L[ℝ] ℝ) +
            (if l = j then 1 else 0) •
              (ContinuousLinearMap.proj m : CKN.Vec 3 →L[ℝ] ℝ)) +
        ((if m = l then 1 else 0) * x j +
          (if m = j then 1 else 0) * x l +
          (if l = j then 1 else 0) * x m) •
          qDerivative (-(5 : ℝ) / 2) x)

private theorem hasFDerivAt_inverseThirdFormulaQ {x : CKN.Vec 3} (hx : x ≠ 0)
    (m j l : Fin 3) :
    HasFDerivAt (inverseThirdFormulaQ m j l)
      (inverseThirdFormulaQDerivative m j l x) x := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- The Newtonian potential and its third-derivative kernel. -/
def newtonianPotential (x : CKN.Vec 3) : ℝ :=
  -(4 * Real.pi)⁻¹ * radialInverse x

/-- Normalized third Newtonian derivative kernel used in the commutator estimates. -/
def newtonianKernel (m j l : Fin 3) (x : CKN.Vec 3) : ℝ :=
  -(4 * Real.pi)⁻¹ * inverseThirdFormula m j l x

private lemma newtonianKernel_spatialDeriv_size_bound_habs8_1 :
    ∀ (a b c d e f g h : ℝ),
      |a + b + c + d + e + f + g + h| ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| + |h|
    := by
  intro a b c d e f g h
  calc
    |a + b + c + d + e + f + g + h| ≤
        |a| + |b + c + d + e + f + g + h| := by
      simpa [add_assoc] using (abs_add_le a (b + c + d + e + f + g + h))
    _ ≤ |a| + (|b| + |c + d + e + f + g + h|) := by
      gcongr
      simpa [add_assoc] using (abs_add_le b (c + d + e + f + g + h))
    _ ≤ |a| + (|b| + (|c| + |d + e + f + g + h|)) := by
      gcongr
      simpa [add_assoc] using (abs_add_le c (d + e + f + g + h))
    _ ≤ |a| + (|b| + (|c| + (|d| + |e + f + g + h|))) := by
      gcongr
      simpa [add_assoc] using (abs_add_le d (e + f + g + h))
    _ ≤ |a| + (|b| + (|c| + (|d| + (|e| + |f + g + h|)))) := by
      gcongr
      simpa [add_assoc] using (abs_add_le e (f + g + h))
    _ ≤ |a| + (|b| + (|c| + (|d| + (|e| + (|f| + |g + h|))))) := by
      gcongr
      simpa [add_assoc] using (abs_add_le f (g + h))
    _ ≤ |a| + |b| + |c| + |d| + |e| + |f| + |g| + |h| := by
      calc
        _ ≤ |a| + (|b| + (|c| + (|d| + (|e| + (|f| + (|g| + |h|)))))) := by
          gcongr
          exact abs_add_le g h
        _ = _ := by ring

private lemma newtonianKernel_spatialDeriv_size_bound_hA4_2 :
    ∀ {x : Vec 3} (m j l n : Fin 3) (r : ℝ),
      0 < r →
        (∀ (i : Fin 3), |x i| ≤ r) →
          |(-(15 * (x m * x j * x l * (-7 / 2 * (r ^ 9)⁻¹ * (2 * x n)))))| ≤ 105 * (r ^ 5)⁻¹
    := by
  intro x m j l n r hr hcoord
  rw [abs_neg, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul, abs_mul]
  norm_num [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
  calc
    15 * (|x m| * |x j| * |x l| *
          ((7 / 2 : ℝ) * (r ^ 9)⁻¹ * (2 * |x n|))) ≤
        15 * (r * r * r * ((7 / 2 : ℝ) * (r ^ 9)⁻¹ * (2 * r))) := by
      gcongr
      · exact hcoord m
      · exact hcoord j
      · exact hcoord l
      · exact hcoord n
    _ = 105 * (r ^ 5)⁻¹ := by
      field_simp [hr.ne']
      ring

private lemma newtonianKernel_spatialDeriv_size_bound_hS_3 :
    ∀ {x : Vec 3} (m j l : Fin 3) (r : ℝ),
      (∀ (i : Fin 3), |x i| ≤ r) →
        (∀ (p : Prop) [Decidable p] (a : ℝ), |if p then a else 0| ≤ |a|) →
          (∀ (a b c : ℝ), |a + b + c| ≤ |a| + |b| + |c|) →
            |((if m = l then x j else 0) + if m = j then x l else 0) + if l = j then x m else 0| ≤
              3 * r
    := by
  intro x m j l r hcoord hdelta habs3
  have hml : |if m = l then x j else 0| ≤ |x j| := hdelta _ _
  have hmj : |if m = j then x l else 0| ≤ |x l| := hdelta _ _
  have hlj : |if l = j then x m else 0| ≤ |x m| := hdelta _ _
  calc
    _ ≤ |if m = l then x j else 0| +
        |if m = j then x l else 0| +
        |if l = j then x m else 0| := habs3 _ _ _
    _ ≤ |x j| + |x l| + |x m| := by
      exact add_le_add (add_le_add hml hmj) hlj
    _ ≤ r + r + r := by gcongr <;> exact hcoord _
    _ = 3 * r := by ring

private lemma newtonianKernel_spatialDeriv_size_bound_hB4_4 :
    ∀ {x : Vec 3} (m j l n : Fin 3) (r : ℝ),
      0 < r →
        (∀ (i : Fin 3), |x i| ≤ r) →
          |((if m = l then x j else 0) + if m = j then x l else 0) + if l = j then x m else 0| ≤
              3 * r →
            |3 *
                    (((if m = l then x j else 0) + if m = j then x l else 0) +
                      if l = j then x m else 0) *
                  (-5 / 2 * (r ^ 7)⁻¹ * (2 * x n))| ≤
              45 * (r ^ 5)⁻¹
    := by
  intro x m j l n r hr hcoord hS
  rw [abs_mul, abs_mul]
  norm_num [abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
  have hfactor : 0 ≤ (5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * |x n|) := by
    positivity
  calc
    3 * |((if m = l then x j else 0) + if m = j then x l else 0) +
          if l = j then x m else 0| *
          ((5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * |x n|)) ≤
        3 * (3 * r * ((5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * r))) := by
      calc
        _ ≤ 3 * (3 * r) *
            ((5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * |x n|)) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hS (by norm_num)) hfactor
        _ ≤ _ := by
          have hc : 0 ≤ (5 / 2 : ℝ) * (r ^ 7)⁻¹ := by positivity
          have hfactor_le :
              (5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * |x n|) ≤
                (5 / 2 : ℝ) * (r ^ 7)⁻¹ * (2 * r) := by
            exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left (hcoord n) (by norm_num)) hc
          have houter : 0 ≤ 3 * (3 * r) := by positivity
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hfactor_le houter
    _ = 45 * (r ^ 5)⁻¹ := by
      field_simp [hr.ne']
      ring

theorem newtonianKernel_spatialDeriv_size_bound {x : CKN.Vec 3} (hx : x ≠ 0)
    (m j l n : Fin 3) :
    |CKN.spatialDeriv (newtonianKernel m j l) n x| ≤
      (204 / (4 * Real.pi)) * CKN.vecEuclideanNorm x ^ (-5 : ℝ) := by
  have hEq : (fun y => inverseThirdFormula m j l y) =ᶠ[𝓝 x]
      (fun y => inverseThirdFormulaQ m j l y) := by
    filter_upwards [isOpen_ne.mem_nhds hx] with y hy
    simp only [inverseThirdFormula, inverseThirdFormulaQ]
    rw [← q_rpow_neg_five hy, ← q_rpow_neg_seven hy]
  have hbase := (hasFDerivAt_inverseThirdFormulaQ hx m j l).congr_of_eventuallyEq hEq
  have hscaled := hbase.const_mul (-(4 * Real.pi)⁻¹)
  have hkernelEq : (fun y => newtonianKernel m j l y) =ᶠ[𝓝 x]
      (fun y => -(4 * Real.pi)⁻¹ * inverseThirdFormula m j l y) := by
    filter_upwards [] with y
    rfl
  have hkernel := hscaled.congr_of_eventuallyEq hkernelEq
  have hn := congrArg (fun L : CKN.Vec 3 →L[ℝ] ℝ => L (CKN.basisVec n)) hkernel.fderiv
  rw [CKN.spatialDeriv, hn]
  have hite (p : Prop) [Decidable p] (L : CKN.Vec 3 →L[ℝ] ℝ) :
      (if p then L else 0) (CKN.basisVec n) =
        if p then L (CKN.basisVec n) else 0 := by
    by_cases hp : p <;> simp [hp]
  have hinner :
      |inverseThirdFormulaQDerivative m j l x (CKN.basisVec n)| ≤
        204 * CKN.vecEuclideanNorm x ^ (-5 : ℝ) := by
    let r := CKN.vecEuclideanNorm x
    have hr : 0 < r := by
      dsimp [r]
      apply lt_of_le_of_ne (CKN.vecEuclideanNorm_nonneg x)
      intro h
      apply hx
      exact CKN.vecEuclideanNorm_eq_zero_iff.mp h.symm
    have hcoord (i : Fin 3) : |x i| ≤ r := by
      exact abs_apply_le_vecEuclideanNorm x i
    have hq5 : q x ^ (-(5 : ℝ) / 2) = (r ^ 5)⁻¹ := by
      simpa [r] using q_rpow_neg_five hx
    have hq7 : q x ^ (-(7 : ℝ) / 2) = (r ^ 7)⁻¹ := by
      simpa [r] using q_rpow_neg_seven hx
    have hq9 : q x ^ (-(9 : ℝ) / 2) = (r ^ 9)⁻¹ := by
      simpa [r] using q_rpow_neg_nine hx
    have hq7' : q x ^ (-(7 : ℝ) / 2 - 1) = (r ^ 9)⁻¹ := by
      rw [show -(7 : ℝ) / 2 - 1 = -(9 : ℝ) / 2 by norm_num, hq9]
    have hq5' : q x ^ (-(5 : ℝ) / 2 - 1) = (r ^ 7)⁻¹ := by
      rw [show -(5 : ℝ) / 2 - 1 = -(7 : ℝ) / 2 by norm_num, hq7]
    simp only [inverseThirdFormulaQDerivative, smul_add, qDerivative, neg_smul, ite_smul,
      one_smul, zero_nsmul,
      smul_ite, smul_zero, ite_mul, one_mul, zero_mul, add_apply, neg_apply, smul_apply,
        ContinuousLinearMap.proj_apply,
      basisVec_apply, smul_eq_mul, mul_ite, mul_one, mul_zero, sum_apply, Finset.sum_ite_eq',
        Finset.mem_univ, ↓reduceIte,
      hite, Real.rpow_neg_ofNat, Int.reduceNeg, zpow_neg, zpow_ofNat, ge_iff_le]
    rw [hq5, hq7, hq7', hq5']
    rw [show CKN.vecEuclideanNorm x = r by rfl]
    have hdelta (p : Prop) [Decidable p] (a : ℝ) :
        |if p then a else 0| ≤ |a| := by
      by_cases hp : p <;> simp [hp]
    have hA (a b : Fin 3) :
        |15 * ((r ^ 7)⁻¹ * (x a * x b))| ≤ 15 * (r ^ 5)⁻¹ := by
      rw [abs_mul, abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 15),
        abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hr.le _))]
      calc
        15 * ((r ^ 7)⁻¹ * (|x a| * |x b|)) ≤
            15 * ((r ^ 7)⁻¹ * (r * r)) := by
          gcongr
          · exact hcoord a
          · exact hcoord b
        _ = 15 * (r ^ 5)⁻¹ := by
          field_simp [hr.ne']
    have hB (p q' : Prop) [Decidable p] [Decidable q'] :
        |if p then if q' then 3 * (r ^ 5)⁻¹ else 0 else 0| ≤
          3 * (r ^ 5)⁻¹ := by
      by_cases hp : p
      · by_cases hq' : q'
        · simp [hp, hq', abs_of_pos hr]
        · simp only [hp, ↓reduceIte, hq', abs_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left,
          inv_nonneg]
          positivity
      · by_cases hq' : q'
        · simp only [hp, ↓reduceIte, abs_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left,
          inv_nonneg]
          positivity
        · simp only [hp, ↓reduceIte, abs_zero, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left,
          inv_nonneg]
          positivity
    have habs8 (a b c d e f g h : ℝ) := @newtonianKernel_spatialDeriv_size_bound_habs8_1 a b c d e
      f g h
    have hsum := habs8
      (-if m = n then 15 * ((r ^ 7)⁻¹ * (x j * x l)) else 0)
      (-if j = n then 15 * ((r ^ 7)⁻¹ * (x m * x l)) else 0)
      (-if l = n then 15 * ((r ^ 7)⁻¹ * (x m * x j)) else 0)
      (-(15 * (x m * x j * x l * (-7 / 2 * (r ^ 9)⁻¹ * (2 * x n)))))
      (if m = l then if j = n then 3 * (r ^ 5)⁻¹ else 0 else 0)
      (if m = j then if l = n then 3 * (r ^ 5)⁻¹ else 0 else 0)
      (if l = j then if m = n then 3 * (r ^ 5)⁻¹ else 0 else 0)
      (3 * (((if m = l then x j else 0) + if m = j then x l else 0) +
        if l = j then x m else 0) * (-5 / 2 * (r ^ 7)⁻¹ * (2 * x n)))
    have hA1 :
        |-if m = n then 15 * ((r ^ 7)⁻¹ * (x j * x l)) else 0| ≤
          15 * (r ^ 5)⁻¹ := by
      calc
        _ = |if m = n then 15 * ((r ^ 7)⁻¹ * (x j * x l)) else 0| := abs_neg _
        _ ≤ |15 * ((r ^ 7)⁻¹ * (x j * x l))| := hdelta _ _
        _ ≤ _ := hA j l
    have hA2 :
        |-if j = n then 15 * ((r ^ 7)⁻¹ * (x m * x l)) else 0| ≤
          15 * (r ^ 5)⁻¹ := by
      calc
        _ = |if j = n then 15 * ((r ^ 7)⁻¹ * (x m * x l)) else 0| := abs_neg _
        _ ≤ |15 * ((r ^ 7)⁻¹ * (x m * x l))| := hdelta _ _
        _ ≤ _ := hA m l
    have hA3 :
        |-if l = n then 15 * ((r ^ 7)⁻¹ * (x m * x j)) else 0| ≤
          15 * (r ^ 5)⁻¹ := by
      calc
        _ = |if l = n then 15 * ((r ^ 7)⁻¹ * (x m * x j)) else 0| := abs_neg _
        _ ≤ |15 * ((r ^ 7)⁻¹ * (x m * x j))| := hdelta _ _
        _ ≤ _ := hA m j
    have hA4 := @newtonianKernel_spatialDeriv_size_bound_hA4_2 x m j l n r hr hcoord
    have habs3 (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
      calc
        |a + b + c| ≤ |a + b| + |c| := abs_add_le _ _
        _ ≤ (|a| + |b|) + |c| := by
          gcongr
          exact abs_add_le _ _
        _ = |a| + |b| + |c| := by ring
    have hS := @newtonianKernel_spatialDeriv_size_bound_hS_3 x m j l r hcoord hdelta habs3
    have hB4 := @newtonianKernel_spatialDeriv_size_bound_hB4_4 x m j l n r hr hcoord hS
    have hB1 := hB (m = l) (j = n)
    have hB2 := hB (m = j) (l = n)
    have hB3 := hB (l = j) (m = n)
    calc
      _ ≤
          |(-if m = n then 15 * ((r ^ 7)⁻¹ * (x j * x l)) else 0)| +
            |(-if j = n then 15 * ((r ^ 7)⁻¹ * (x m * x l)) else 0)| +
            |(-if l = n then 15 * ((r ^ 7)⁻¹ * (x m * x j)) else 0)| +
            |-(15 * (x m * x j * x l * (-7 / 2 * (r ^ 9)⁻¹ * (2 * x n))))| +
            |if m = l then if j = n then 3 * (r ^ 5)⁻¹ else 0 else 0| +
            |if m = j then if l = n then 3 * (r ^ 5)⁻¹ else 0 else 0| +
            |if l = j then if m = n then 3 * (r ^ 5)⁻¹ else 0 else 0| +
            |3 * (((if m = l then x j else 0) + if m = j then x l else 0) +
              if l = j then x m else 0) *
              (-5 / 2 * (r ^ 7)⁻¹ * (2 * x n))| := by
        convert hsum using 1
        all_goals congr 1
        all_goals ring
      _ ≤ 204 * (r ^ 5)⁻¹ := by
        calc
          _ ≤
              15 * (r ^ 5)⁻¹ + 15 * (r ^ 5)⁻¹ + 15 * (r ^ 5)⁻¹ +
                105 * (r ^ 5)⁻¹ + 3 * (r ^ 5)⁻¹ + 3 * (r ^ 5)⁻¹ +
                3 * (r ^ 5)⁻¹ + 45 * (r ^ 5)⁻¹ := by
            linarith only [hA1, hA2, hA3, hA4, hB1, hB2, hB3, hB4]
          _ = 204 * (r ^ 5)⁻¹ := by ring
  change |-(4 * Real.pi)⁻¹ * inverseThirdFormulaQDerivative m j l x
      (CKN.basisVec n)| ≤ _
  rw [abs_mul]
  have hscale : |-(4 * Real.pi)⁻¹| = (4 * Real.pi)⁻¹ := by
    rw [abs_neg, abs_of_nonneg]
    positivity
  rw [hscale]
  calc
    (4 * Real.pi)⁻¹ *
          |inverseThirdFormulaQDerivative m j l x (CKN.basisVec n)| ≤
        (4 * Real.pi)⁻¹ *
          (204 * CKN.vecEuclideanNorm x ^ (-5 : ℝ)) := by
      exact mul_le_mul_of_nonneg_left hinner (by positivity)
    _ = (204 / (4 * Real.pi)) * CKN.vecEuclideanNorm x ^ (-5 : ℝ) := by
      ring

end
end CKN.Foundation.Harmonic.Commutator
