/-
Copyright (c) 2026 Alok Singh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alok Singh
-/
import Tengoku.JacobianTwo.JacobianTwo.FractionRingDerivative
import Tengoku.JacobianTwo.JacobianTwo.QuadraticRecurrence
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A polynomial primitive for the quadratic recurrence

For a polynomial `S`, the downward quadratic recurrence asks for a polynomial
`T` satisfying

`T' = X * S' + (1/2) * S`.

In characteristic zero this file constructs `T` coefficientwise and proves
the identity.  The next descent layer evaluates this identity at the centered
residual `F`.
-/

noncomputable section

open Polynomial

namespace JacobianTwo.QuadraticRecurrencePrimitive

open JacobianTwo.FractionRingDerivative
open JacobianTwo.QuadraticRecurrence

variable {K : Type*} [Field K] [CharZero K]

/-- The coefficientwise primitive of `X*S' + S/2`.  A monomial `a*X^n`
is sent to `((n+1/2)/(n+1))*a*X^(n+1)`.-/
def recurrencePrimitive (S : K[X]) : K[X] :=
  S.sum fun n a ↦
    monomial (n + 1)
      ((((n : K) + (1 / 2 : K)) / (n + 1 : K)) * a)

omit [CharZero K] in
/--
@isnad1 id=eq.0h3v.s7.e922e7c47852 from=translated src=- shape=667c5061 vocab=57ec5229
-/
theorem recurrencePrimitive_add (S T : K[X]) :
    recurrencePrimitive (S + T) =
      recurrencePrimitive S + recurrencePrimitive T := by
  rw [recurrencePrimitive, recurrencePrimitive, recurrencePrimitive]
  apply sum_add_index
  · intro n
    simp
  · intro n a b
    simp [mul_add]

omit [CharZero K] in
/--
@isnad1 id=eq.0h3v.s9.9c294622cbbe from=translated src=- shape=32029b15 vocab=583fe1b1
-/
theorem recurrencePrimitive_monomial (n : ℕ) (a : K) :
    recurrencePrimitive (monomial n a) =
      monomial (n + 1)
        ((((n : K) + (1 / 2 : K)) / (n + 1 : K)) * a) := by
  rw [recurrencePrimitive]
  exact sum_monomial_index a _ (by simp)

omit [CharZero K] in
/--
@isnad1 id=eq.0h2v.s5.76a89a729fdf from=translated src=- shape=f81c630a vocab=44d22409
-/
@[simp]
theorem coeff_zero_recurrencePrimitive (S : K[X]) :
    (recurrencePrimitive S).coeff 0 = 0 := by
  induction S using Polynomial.induction_on' with
  | add P Q hP hQ => simp [recurrencePrimitive_add, hP, hQ]
  | monomial n a => simp [recurrencePrimitive_monomial, coeff_monomial]

omit [CharZero K] in
/--
@isnad1 id=eq.0h3v.s7.c4fde7805fe6 from=translated src=- shape=c78bc73d vocab=98bc9abc
-/
theorem coeff_succ_recurrencePrimitive (S : K[X]) (n : ℕ) :
    (recurrencePrimitive S).coeff (n + 1) =
      (((n : K) + (1 / 2 : K)) / (n + 1 : K)) * S.coeff n := by
  induction S using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [recurrencePrimitive_add, coeff_add, hP, hQ, coeff_add]
      ring
  | monomial m a =>
      rw [recurrencePrimitive_monomial]
      by_cases hmn : m = n
      · subst m
        simp
      · simp [coeff_monomial, hmn]

/--
@isnad1 id=ne.0h2v.s7.0bb285a03682 from=translated src=- shape=7b4c9757 vocab=58cf8b6d
-/
theorem recurrenceMultiplier_ne_zero (n : ℕ) :
    ((n : K) + (1 / 2 : K)) / (n + 1 : K) ≠ 0 := by
  have hden : (n + 1 : K) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero n
  have hodd : ((2 * n + 1 : ℕ) : K) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero (2 * n)
  have hnum : (n : K) + (1 / 2 : K) ≠ 0 := by
    intro hzero
    apply hodd
    push_cast
    linear_combination 2 * hzero
  exact div_ne_zero hnum hden

/-- The recurrence primitive raises the degree of every nonzero polynomial by
exactly one.
@isnad1 id=eq.1h2v.s6.a78f9ca80bbd from=translated src=- shape=d10968a2 vocab=e4b65848
-/
theorem natDegree_recurrencePrimitive (S : K[X]) (hS : S ≠ 0) :
    (recurrencePrimitive S).natDegree = S.natDegree + 1 := by
  have hle : (recurrencePrimitive S).natDegree ≤ S.natDegree + 1 := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro N hN
    cases N with
    | zero => omega
    | succ n =>
        rw [coeff_succ_recurrencePrimitive]
        have hn : S.natDegree < n := by omega
        rw [coeff_eq_zero_of_natDegree_lt hn, mul_zero]
  apply natDegree_eq_of_le_of_coeff_ne_zero hle
  rw [coeff_succ_recurrencePrimitive, coeff_natDegree]
  exact mul_ne_zero (recurrenceMultiplier_ne_zero S.natDegree)
    (leadingCoeff_ne_zero.mpr hS)

/-- Exact leading coefficient of the recurrence primitive.
@isnad1 id=eq.1h2v.s8.dc117fbb182d from=translated src=- shape=55fecdca vocab=f3ff3c8f
-/
theorem leadingCoeff_recurrencePrimitive (S : K[X]) (hS : S ≠ 0) :
    (recurrencePrimitive S).leadingCoeff =
      ((S.natDegree : K) + (1 / 2 : K)) /
          (S.natDegree + 1 : K) * S.leadingCoeff := by
  rw [leadingCoeff, natDegree_recurrencePrimitive S hS,
    coeff_succ_recurrencePrimitive, coeff_natDegree]

/--
@isnad1 id=eq.1h3v.s8.ad92c7e1d74b from=translated src=- shape=d2eb0108 vocab=08e7f340
-/
theorem natDegree_recurrencePrimitive_add_C
    (S : K[X]) (hS : S ≠ 0) (c : K) :
    (recurrencePrimitive S + C c).natDegree = S.natDegree + 1 := by
  have hprimitiveDegree := natDegree_recurrencePrimitive S hS
  have hprimitiveNe : recurrencePrimitive S ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hprimitiveDegree
    omega
  have hdegree : degree (C c) < degree (recurrencePrimitive S) := by
    apply degree_C_le.trans_lt
    rw [degree_eq_natDegree hprimitiveNe, hprimitiveDegree]
    exact_mod_cast Nat.zero_lt_succ S.natDegree
  rw [natDegree_add_eq_left_of_degree_lt hdegree, hprimitiveDegree]

/--
@isnad1 id=eq.1h3v.s8.d0145b460a3e from=translated src=- shape=3f0acd87 vocab=cc988ec4
-/
theorem leadingCoeff_recurrencePrimitive_add_C
    (S : K[X]) (hS : S ≠ 0) (c : K) :
    (recurrencePrimitive S + C c).leadingCoeff =
      ((S.natDegree : K) + (1 / 2 : K)) /
          (S.natDegree + 1 : K) * S.leadingCoeff := by
  have hprimitiveDegree := natDegree_recurrencePrimitive S hS
  have hprimitiveNe : recurrencePrimitive S ≠ 0 := by
    intro hzero
    rw [hzero, natDegree_zero] at hprimitiveDegree
    omega
  have hdegree : degree (C c) < degree (recurrencePrimitive S) := by
    apply degree_C_le.trans_lt
    rw [degree_eq_natDegree hprimitiveNe, hprimitiveDegree]
    exact_mod_cast Nat.zero_lt_succ S.natDegree
  rw [leadingCoeff_add_of_degree_lt' hdegree,
    leadingCoeff_recurrencePrimitive S hS]

/-- The constructed polynomial has the required derivative.
@isnad1 id=eq.0h2v.s9.c309b1d53876 from=translated src=- shape=b188021f vocab=999e5384
-/
theorem derivative_recurrencePrimitive (S : K[X]) :
    derivative (recurrencePrimitive S) =
      X * derivative S + C (1 / 2 : K) * S := by
  induction S using Polynomial.induction_on' with
  | add P Q hP hQ =>
      rw [recurrencePrimitive_add, derivative_add, hP, hQ, derivative_add]
      ring
  | monomial n a =>
      cases n with
      | zero =>
          rw [recurrencePrimitive_monomial, derivative_monomial_succ,
            derivative_monomial]
          simp only [Nat.cast_zero, mul_zero, monomial_zero_right, mul_zero,
            zero_add, C_mul_monomial]
          ext m
          simp only [coeff_monomial]
          split_ifs <;> norm_num
      | succ n =>
          have hden : (n + 2 : K) ≠ 0 := by
            exact_mod_cast Nat.succ_ne_zero (n + 1)
          have hden' : (2 + n : K) ≠ 0 := by
            simpa [add_comm] using hden
          have hden'' : (n : K) + 1 + 1 ≠ 0 := by
            simpa only [show (2 : K) = 1 + 1 by norm_num, add_assoc]
              using hden
          rw [recurrencePrimitive_monomial, derivative_monomial_succ,
            derivative_monomial_succ]
          rw [X_mul_monomial, C_mul_monomial]
          ext m
          simp only [coeff_add, coeff_monomial]
          split_ifs
          · push_cast
            field_simp [hden, hden', hden'']
          · ring

/-- One downward recurrence step preserves membership in the polynomial
subalgebra generated by `F`.
@isnad1 id=ex.3h6v.s10.3c1bd14c9cb9 from=translated src=- shape=9b5552af vocab=56e6ccd6
-/
theorem aeval_of_recurrence_step
    {L : Type*} [Field L] [Algebra K L]
    (D : Derivation K L L) (F b bnext : L)
    (hker : ∀ z : L, D z = 0 → ∃ c : K, z = algebraMap K L c)
    (hrec : D b = F * D bnext + (D F / 2) * bnext)
    (hnext : ∃ S : K[X], bnext = aeval F S) :
    ∃ T : K[X], b = aeval F T := by
  obtain ⟨S, rfl⟩ := hnext
  let T := recurrencePrimitive S
  have hT :
      derivative T = X * derivative S + C (1 / 2 : K) * S := by
    simpa only [T] using derivative_recurrencePrimitive S
  have hzero : D (b - aeval F T) = 0 := by
    rw [map_sub, hrec, D.map_aeval, D.map_aeval, hT]
    simp only [aeval_add, aeval_mul, aeval_X, aeval_C, smul_eq_mul]
    rw [map_div₀, map_one, map_ofNat]
    ring
  obtain ⟨c, hc⟩ := hker _ hzero
  refine ⟨T + C c, ?_⟩
  simp only [aeval_add, aeval_C]
  rw [← hc]
  ring

/-- A recurrence step from a nonzero witness raises its degree by one and
multiplies its leading coefficient by the explicit nonzero recurrence
multiplier.
@isnad1 id=ex.4h7v.s10.5a4edb74a1d4 from=translated src=- shape=cc3b8bc3 vocab=2086c6d5
-/
theorem aeval_of_recurrence_step_with_degree
    {L : Type*} [Field L] [Algebra K L]
    (D : Derivation K L L) (F b bnext : L)
    (hker : ∀ z : L, D z = 0 → ∃ c : K, z = algebraMap K L c)
    (hrec : D b = F * D bnext + (D F / 2) * bnext)
    (S : K[X]) (hS : S ≠ 0) (hnext : bnext = aeval F S) :
    ∃ T : K[X],
      b = aeval F T ∧
      T.natDegree = S.natDegree + 1 ∧
      T.leadingCoeff =
        ((S.natDegree : K) + (1 / 2 : K)) /
          (S.natDegree + 1 : K) * S.leadingCoeff := by
  let T₀ := recurrencePrimitive S
  have hT₀ :
      derivative T₀ = X * derivative S + C (1 / 2 : K) * S := by
    simpa only [T₀] using derivative_recurrencePrimitive S
  have hzero : D (b - aeval F T₀) = 0 := by
    rw [map_sub, hrec, hnext, D.map_aeval, D.map_aeval, hT₀]
    simp only [aeval_add, aeval_mul, aeval_X, aeval_C, smul_eq_mul]
    rw [map_div₀, map_one, map_ofNat]
    ring
  obtain ⟨c, hc⟩ := hker _ hzero
  refine ⟨T₀ + C c, ?_, ?_, ?_⟩
  · simp only [aeval_add, aeval_C]
    rw [← hc]
    ring
  · exact natDegree_recurrencePrimitive_add_C S hS c
  · exact leadingCoeff_recurrencePrimitive_add_C S hS c

/-- Starting from a top coefficient in `K[F]`, the downward recurrence puts
every lower coefficient in `K[F]`.
@isnad1 id=ex.4h7v.s10.4d6dc453dd53 from=translated src=- shape=42979e04 vocab=05090695
-/
theorem coeff_aeval_of_downward_recurrence
    {L : Type*} [Field L] [Algebra K L]
    (D : Derivation K L L) (F : L) (B : L[X]) (n : ℕ)
    (hker : ∀ z : L, D z = 0 → ∃ c : K, z = algebraMap K L c)
    (hrec : ∀ j < n, D (B.coeff j) =
      F * D (B.coeff (j + 1)) + (D F / 2) * B.coeff (j + 1))
    (htop : ∃ S : K[X], B.coeff n = aeval F S)
    (j : ℕ) (hj : j ≤ n) :
    ∃ S : K[X], B.coeff j = aeval F S := by
  induction hj using Nat.decreasingInduction with
  | self => exact htop
  | of_succ j hj ih =>
      exact aeval_of_recurrence_step D F (B.coeff j) (B.coeff (j + 1))
        hker (hrec j hj) ih

/-- Exact degree and nonvanishing control for the downward recurrence.  A
nonzero scalar top coefficient produces a degree-`n-j` witness for coefficient
`j`, with nonzero leading coefficient.
@isnad1 id=ex.4h7v.s10.bba128be00c0 from=translated src=- shape=39e5b6bf vocab=0e32d2b6
-/
theorem coeff_aeval_with_degree_of_downward_recurrence
    {L : Type*} [Field L] [Algebra K L]
    (D : Derivation K L L) (F : L) (B : L[X]) (n : ℕ)
    (hker : ∀ z : L, D z = 0 → ∃ c : K, z = algebraMap K L c)
    (hrec : ∀ j < n, D (B.coeff j) =
      F * D (B.coeff (j + 1)) + (D F / 2) * B.coeff (j + 1))
    (htop : ∃ c : K, c ≠ 0 ∧ B.coeff n = algebraMap K L c)
    (j : ℕ) (hj : j ≤ n) :
    ∃ S : K[X],
      B.coeff j = aeval F S ∧
      S.natDegree = n - j ∧
      S.leadingCoeff ≠ 0 := by
  induction hj using Nat.decreasingInduction with
  | self =>
      obtain ⟨c, hc, hcoeff⟩ := htop
      refine ⟨C c, ?_, ?_, ?_⟩
      · simpa using hcoeff
      · simp
      · simp [hc]
  | of_succ j hj ih =>
      obtain ⟨S, hcoeffS, hdegreeS, hleadS⟩ := ih
      have hSne : S ≠ 0 := leadingCoeff_ne_zero.mp hleadS
      obtain ⟨T, hcoeffT, hdegreeT, hleadT⟩ :=
        aeval_of_recurrence_step_with_degree
          D F (B.coeff j) (B.coeff (j + 1)) hker (hrec j hj)
          S hSne hcoeffS
      refine ⟨T, hcoeffT, ?_, ?_⟩
      · rw [hdegreeT, hdegreeS]
        omega
      · rw [hleadT]
        exact mul_ne_zero (recurrenceMultiplier_ne_zero S.natDegree) hleadS

/-- Every coefficient of a solution to the fraction-field recurrence is a
polynomial in the centered residual `F` with coefficients in `K`.
@isnad1 id=ex.1h5v.s11.343bf076523a from=translated src=- shape=f93d8c3e vocab=a7b111b2
-/
theorem coeff_aeval_of_fraction_recurrencePolynomial_eq_C
    (F C₀ : FractionRing K[X]) (B : (FractionRing K[X])[X])
    (h : recurrencePolynomial
      (fractionRingDerivative (K := K)) F B = C C₀)
    (j : ℕ) :
    ∃ S : K[X], B.coeff j = aeval F S := by
  by_cases hj : j ≤ B.natDegree
  · have htopD :
        fractionRingDerivative (K := K) (B.coeff B.natDegree) = 0 :=
      top_coefficient_derivative_eq_zero
        (R := K) (L := FractionRing K[X])
        (fractionRingDerivative (K := K)) F C₀ B h
    obtain ⟨c, hc⟩ :=
      (fractionRingDerivative_eq_zero_iff
        (K := K) (B.coeff B.natDegree)).1 htopD
    have htop : ∃ S : K[X], B.coeff B.natDegree = aeval F S := by
      exact ⟨C c, by simp [hc]⟩
    exact coeff_aeval_of_downward_recurrence
      (fractionRingDerivative (K := K)) F B B.natDegree
      (fun z hz ↦ (fractionRingDerivative_eq_zero_iff (K := K) z).1 hz)
      (fun i _ ↦ coefficient_recurrence
        (R := K) (L := FractionRing K[X])
        (fractionRingDerivative (K := K)) F C₀ B h i)
      htop j hj
  · refine ⟨0, ?_⟩
    rw [coeff_eq_zero_of_natDegree_lt (Nat.lt_of_not_ge hj)]
    exact (map_zero (aeval F)).symm

/-- Exact degree form of the fraction-field recurrence solver.
@isnad1 id=ex.3h5v.s12.407610bc9b3e from=translated src=- shape=715b7110 vocab=54a2f9cf
-/
theorem coeff_aeval_with_degree_of_fraction_recurrencePolynomial_eq_C
    (F C₀ : FractionRing K[X]) (B : (FractionRing K[X])[X])
    (hB : B ≠ 0)
    (h : recurrencePolynomial
      (fractionRingDerivative (K := K)) F B = C C₀)
    (j : ℕ) (hj : j ≤ B.natDegree) :
    ∃ S : K[X],
      B.coeff j = aeval F S ∧
      S.natDegree = B.natDegree - j ∧
      S.leadingCoeff ≠ 0 := by
  have htopD :
      fractionRingDerivative (K := K) (B.coeff B.natDegree) = 0 :=
    top_coefficient_derivative_eq_zero
      (R := K) (L := FractionRing K[X])
      (fractionRingDerivative (K := K)) F C₀ B h
  obtain ⟨c, hc⟩ :=
    (fractionRingDerivative_eq_zero_iff
      (K := K) (B.coeff B.natDegree)).1 htopD
  have hcne : c ≠ 0 := by
    intro hczero
    apply leadingCoeff_ne_zero.mpr hB
    rw [← coeff_natDegree, hc, hczero, map_zero]
  exact coeff_aeval_with_degree_of_downward_recurrence
    (fractionRingDerivative (K := K)) F B B.natDegree
    (fun z hz ↦ (fractionRingDerivative_eq_zero_iff (K := K) z).1 hz)
    (fun i _ ↦ coefficient_recurrence
      (R := K) (L := FractionRing K[X])
      (fractionRingDerivative (K := K)) F C₀ B h i)
    ⟨c, hcne, hc⟩ j hj

end JacobianTwo.QuadraticRecurrencePrimitive
