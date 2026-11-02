/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.CharacteristicClasses.Formal
import Tengoku.Seed.Algebra.Polynomial.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Characteristic series for finite families of formal Chern roots

The splitting-principle formulas for a finite root family are independent of geometry:
the Chern character is the sum of the exponential root series, while the Todd class is the
product of the Todd root factors.  This file constructs those expressions and checks their
direct-sum laws and normalizations.
-/

noncomputable section

open PowerSeries

universe u v

namespace CharacteristicClasses

variable (A : Type u) [CommRing A]
variable {I : Type v}

/-- Total Chern polynomial of a finite family of formal Chern roots.-/
def totalChernRoots (s : Finset I) (root : I → A) : Polynomial A :=
  ∏ i ∈ s, (1 + Polynomial.C (root i) * Polynomial.X)

/-- The `n`-th Chern class of a split root family, extracted from its total Chern polynomial.-/
def chernClassRoots (n : ℕ) (s : Finset I) (root : I → A) : A :=
  (totalChernRoots A s root).coeff n

@[simp]
theorem totalChernRoots_empty (root : I → A) :
    totalChernRoots A ∅ root = 1 := by
  simp [totalChernRoots]

@[simp]
theorem totalChernRoots_insert [DecidableEq I] (s : Finset I) (root : I → A)
    {i : I} (hi : i ∉ s) :
    totalChernRoots A (insert i s) root =
      (1 + Polynomial.C (root i) * Polynomial.X) * totalChernRoots A s root := by
  simp [totalChernRoots, hi]

/-- The degree-zero total Chern class is one.-/
@[simp]
theorem coeff_zero_totalChernRoots (s : Finset I) (root : I → A) :
    (totalChernRoots A s root).coeff 0 = 1 := by
  classical
  simp [totalChernRoots, Polynomial.coeff_zero_prod]

/-- The degree-one total Chern class is the sum of the formal roots.-/
theorem coeff_one_totalChernRoots (s : Finset I) (root : I → A) :
    (totalChernRoots A s root).coeff 1 = ∑ i ∈ s, root i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [totalChernRoots, Polynomial.coeff_one]
  | @insert i s hi ih =>
      rw [totalChernRoots_insert A s root hi, Polynomial.mul_coeff_one]
      simp [ih, hi, Polynomial.coeff_one, add_comm]

@[simp]
theorem chernClassRoots_zero (s : Finset I) (root : I → A) :
    chernClassRoots A 0 s root = 1 :=
  coeff_zero_totalChernRoots A s root

theorem chernClassRoots_one (s : Finset I) (root : I → A) :
    chernClassRoots A 1 s root = ∑ i ∈ s, root i :=
  coeff_one_totalChernRoots A s root

/-- Inserting one root adds its product with the old first Chern class to the old second
Chern class.-/
theorem chernClassRoots_two_insert [DecidableEq I] (s : Finset I) (root : I → A)
    {i : I} (hi : i ∉ s) :
    chernClassRoots A 2 (insert i s) root =
      root i * chernClassRoots A 1 s root + chernClassRoots A 2 s root := by
  rw [chernClassRoots, totalChernRoots_insert A s root hi, Polynomial.coeff_mul]
  have h : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    exact rfl
  rw [h]
  simp [chernClassRoots, Polynomial.coeff_one, Polynomial.coeff_X]
  ring

variable [Algebra ℚ A]

/-- Chern-character series of a finite family of formal Chern roots.-/
def chRoots (s : Finset I) (root : I → A) : PowerSeries A :=
  ∑ i ∈ s, chRoot A (root i)

/-- Todd series of a finite family of formal Chern roots.-/
def toddRoots (s : Finset I) (root : I → A) : PowerSeries A :=
  ∏ i ∈ s, toddRoot A (root i)

@[simp]
theorem chRoots_empty (root : I → A) :
    chRoots A ∅ root = 0 := by
  simp [chRoots]

@[simp]
theorem toddRoots_empty (root : I → A) :
    toddRoots A ∅ root = 1 := by
  simp [toddRoots]

@[simp]
theorem chRoots_insert [DecidableEq I] (s : Finset I) (root : I → A)
    {i : I} (hi : i ∉ s) :
    chRoots A (insert i s) root = chRoot A (root i) + chRoots A s root := by
  simp [chRoots, hi]

@[simp]
theorem toddRoots_insert [DecidableEq I] (s : Finset I) (root : I → A)
    {i : I} (hi : i ∉ s) :
    toddRoots A (insert i s) root = toddRoot A (root i) * toddRoots A s root := by
  simp [toddRoots, hi]

/-- A singleton root family contributes exactly its one-root Chern character.-/
@[simp]
theorem chRoots_singleton (i : I) (root : I → A) :
    chRoots A {i} root = chRoot A (root i) := by
  simp [chRoots]

/-- Negating a formal root inverts its Chern-character factor.-/
theorem chRoots_singleton_neg (i : I) (root : I → A) :
    chRoots A {i} (fun j ↦ -root j) * chRoots A {i} root = 1 := by
  simp [chRoot_neg_mul]

/-- Chern character of a virtual difference of disjoint split root families.-/
def chRootsDiff [DecidableEq I] (s t : Finset I) (root : I → A) : PowerSeries A :=
  chRoots A s root - chRoots A t root

/-- Tensor products pair the two finite root families and add the corresponding roots.-/
def tensorRoot {J : Type*} (root : I → A) (root' : J → A) (ij : I × J) : A :=
  root ij.1 + root' ij.2

/-- On split root families the Chern character sends tensor products to multiplication.-/
theorem chRoots_product {J : Type*} (s : Finset I) (t : Finset J)
    (root : I → A) (root' : J → A) :
    chRoots A (s ×ˢ t) (tensorRoot A root root') =
      chRoots A s root * chRoots A t root' := by
  classical
  simp only [chRoots, Finset.sum_product, tensorRoot]
  simp_rw [← chRoot_add]
  rw [Finset.sum_mul]
  congr 1
  funext i
  rw [Finset.mul_sum]

/-- The degree-zero Chern character of a split rank-`r` object is its rank.-/
@[simp]
theorem constantCoeff_chRoots (s : Finset I) (root : I → A) :
    PowerSeries.constantCoeff (chRoots A s root) = (s.card : A) := by
  simp [chRoots]

/-- Every finite Todd root product is normalized to constant coefficient one.-/
@[simp]
theorem constantCoeff_toddRoots (s : Finset I) (root : I → A) :
    PowerSeries.constantCoeff (toddRoots A s root) = 1 := by
  simp [toddRoots]

/-- Every coefficient of the split Chern character is the corresponding sum of powers of its
formal roots.-/
theorem coeff_chRoots (s : Finset I) (root : I → A) (n : ℕ) :
    PowerSeries.coeff n (chRoots A s root) =
      ∑ i ∈ s, root i ^ n * algebraMap ℚ A ((1 : ℚ) / Nat.factorial n) := by
  simp [chRoots, coeff_chRoot]

/-- Newton's degree-two identity for a finite family of formal roots.-/
theorem sum_sq_roots_eq (s : Finset I) (root : I → A) :
    ∑ i ∈ s, root i ^ 2 =
      (∑ i ∈ s, root i) ^ 2 - 2 * chernClassRoots A 2 s root := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chernClassRoots, totalChernRoots, Polynomial.coeff_one]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi,
        chernClassRoots_two_insert A s root hi, chernClassRoots_one]
      rw [ih]
      ring

/-- The degree-one Chern-character term of a split object is its first Chern class.-/
theorem coeff_one_chRoots_eq_c1 (s : Finset I) (root : I → A) :
    PowerSeries.coeff 1 (chRoots A s root) = chernClassRoots A 1 s root := by
  rw [coeff_chRoots, chernClassRoots_one]
  norm_num

/-- The degree-two Chern-character term of a split object is `(c₁² - 2c₂) / 2`.-/
theorem coeff_two_chRoots_eq (s : Finset I) (root : I → A) :
    PowerSeries.coeff 2 (chRoots A s root) =
      ((∑ i ∈ s, root i) ^ 2 - 2 * chernClassRoots A 2 s root) *
        algebraMap ℚ A ((1 : ℚ) / 2) := by
  rw [coeff_chRoots]
  norm_num [Nat.factorial]
  rw [← Finset.sum_mul, sum_sq_roots_eq]

/-- The degree-one Todd term of a split object is one half of the sum of its formal roots.-/
theorem coeff_one_toddRoots (s : Finset I) (root : I → A) :
    PowerSeries.coeff 1 (toddRoots A s root) =
      ∑ i ∈ s, root i * algebraMap ℚ A ((1 : ℚ) / 2) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [toddRoots_insert A s root hi, PowerSeries.coeff_one_mul]
      simp [ih, hi]

/-- The second coefficient of a product of two power series.-/
lemma coeff_two_mul (φ ψ : PowerSeries A) :
    PowerSeries.coeff 2 (φ * ψ) =
      PowerSeries.coeff 2 φ * PowerSeries.constantCoeff ψ +
        PowerSeries.coeff 1 φ * PowerSeries.coeff 1 ψ +
          PowerSeries.constantCoeff φ * PowerSeries.coeff 2 ψ := by
  have h : Finset.antidiagonal 2 = {(0, 2), (1, 1), (2, 0)} := by
    exact rfl
  rw [PowerSeries.coeff_mul, h]
  simp [PowerSeries.coeff_zero_eq_constantCoeff]
  ring

/-- The degree-two Todd term of a split object is `(c₁² + c₂) / 12`.-/
theorem coeff_two_toddRoots (s : Finset I) (root : I → A) :
    PowerSeries.coeff 2 (toddRoots A s root) =
      ((∑ i ∈ s, root i) ^ 2 + chernClassRoots A 2 s root) *
        algebraMap ℚ A ((1 : ℚ) / 12) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [chernClassRoots, totalChernRoots, Polynomial.coeff_one]
  | @insert i s hi ih =>
      rw [toddRoots_insert A s root hi, coeff_two_mul]
      rw [constantCoeff_toddRoot, constantCoeff_toddRoots,
        coeff_one_toddRoot, coeff_one_toddRoots, coeff_two_toddRoot, ih,
        chernClassRoots_two_insert A s root hi]
      simp only [Finset.sum_insert, hi, not_false_eq_true]
      rw [chernClassRoots_one]
      rw [← Finset.sum_mul]
      push_cast
      have hrat : (algebraMap ℚ A ((1 : ℚ) / 2)) ^ 2 =
          algebraMap ℚ A ((1 : ℚ) / 12) + algebraMap ℚ A ((1 : ℚ) / 12) +
            algebraMap ℚ A ((1 : ℚ) / 12) := by
        calc
          _ = algebraMap ℚ A (((1 : ℚ) / 2) ^ 2) := by rw [map_pow]
          _ = algebraMap ℚ A
              (((1 : ℚ) / 12) + (1 : ℚ) / 12 + (1 : ℚ) / 12) := by norm_num
          _ = _ := by rw [map_add, map_add]
      ring_nf
      rw [hrat]
      ring

/-- Degree-two characteristic integrand for a split bundle on a split tangent object.  This is
the universal surface term in `ch(E) · td(T)`.-/
theorem coeff_two_chRoots_mul_toddRoots {J : Type*} (s : Finset I) (t : Finset J)
    (root : I → A) (tangentRoot : J → A) :
    PowerSeries.coeff 2 (chRoots A s root * toddRoots A t tangentRoot) =
      ((∑ i ∈ s, root i) ^ 2 - 2 * chernClassRoots A 2 s root) *
          algebraMap ℚ A ((1 : ℚ) / 2) +
        (∑ i ∈ s, root i) * (∑ j ∈ t, tangentRoot j) *
          algebraMap ℚ A ((1 : ℚ) / 2) +
        (s.card : A) *
          (((∑ j ∈ t, tangentRoot j) ^ 2 + chernClassRoots A 2 t tangentRoot) *
            algebraMap ℚ A ((1 : ℚ) / 12)) := by
  rw [coeff_two_mul, constantCoeff_toddRoots, coeff_two_chRoots_eq,
    coeff_one_chRoots_eq_c1, chernClassRoots_one, coeff_one_toddRoots,
    constantCoeff_chRoots, coeff_two_toddRoots]
  rw [← Finset.sum_mul]
  ring

/-- Degree-one characteristic integrand for a split bundle on a split tangent object.  This is
the universal curve term in `ch(E) · td(T)`.-/
theorem coeff_one_chRoots_mul_toddRoots {J : Type*} (s : Finset I) (t : Finset J)
    (root : I → A) (tangentRoot : J → A) :
    PowerSeries.coeff 1 (chRoots A s root * toddRoots A t tangentRoot) =
      (∑ i ∈ s, root i) +
        (s.card : A) * (∑ j ∈ t, tangentRoot j) *
          algebraMap ℚ A ((1 : ℚ) / 2) := by
  rw [PowerSeries.coeff_one_mul, constantCoeff_toddRoots,
    coeff_one_chRoots_eq_c1, chernClassRoots_one, coeff_one_toddRoots,
    constantCoeff_chRoots]
  rw [← Finset.sum_mul]
  ring

end CharacteristicClasses
