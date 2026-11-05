/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.Seed.RingTheory.DedekindDomain.Basic
import Tengoku.AclGeom.AclGeom.Curves.Places

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Toward weak approximation for places

The independence machinery for finitely many places of a one-variable
function field (Stichtenoth Theorem 1.3.1), needed for the finiteness of
zeros and poles in the divisor theory. This file provides the pairwise
bricks:

* distinct places are incomparable (`Place.not_le_of_ne`) — an overring
  of a discrete valuation subring is the whole field;
* the **pair separation** lemma: for distinct places there is an element
  small at one and large at the other (`Place.exists_lt_one_gt_one`);
* the **indicator estimates** for `y^n/(1+y^n)`, the ultrametric
  approximation to the indicator function of `{v y > 1}`
  (`valuation_indicator_of_lt_one`, `valuation_indicator_of_gt_one`);
* the **Archimedean property** of a place's values
  (`Place.exists_pow_valuation_lt`), from the uniformizer
  classification: powers of a small value eventually drop below any
  nonzero value.

The full approximation induction assembles these in the next layer.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, toward P2).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]

namespace Place

@[ext]
theorem ext {P Q : Place k F} (h : P.val = Q.val) : P = Q := by
  cases P; cases Q; simpa using h

variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- Distinct places are incomparable: an overring of a discrete valuation
subring of its fraction field is everything.-/
theorem not_le_of_ne {P Q : Place k F} (h : P ≠ Q) : ¬ P.val ≤ Q.val := by
  intro hle
  haveI := P.isDiscreteValuationRing
  haveI : Ring.DimensionLEOne (↥P.val) :=
    Ring.DimensionLEOne.principal_ideal_ring _
  exact Q.ne_top (ValuationSubring.eq_of_le_of_ne_self P.val hle
    fun hv ↦ h (Place.ext hv))

/-- **Pair separation**: for distinct places there is an element that is
small at the first and large at the second.-/
theorem exists_lt_one_gt_one {P Q : Place k F} (h : P ≠ Q) :
    ∃ z : F, P.val.valuation z < 1 ∧ 1 < Q.val.valuation z := by
  obtain ⟨a, haP, haQ⟩ : ∃ a : F, a ∈ P.val ∧ a ∉ Q.val := by
    by_contra hc
    push Not at hc
    exact not_le_of_ne h hc
  obtain ⟨b, hbQ, hbP⟩ : ∃ b : F, b ∈ Q.val ∧ b ∉ P.val := by
    by_contra hc
    push Not at hc
    exact not_le_of_ne h.symm hc
  have hb0 : b ≠ 0 := fun h0 ↦ hbP (h0 ▸ zero_mem P.val)
  refine ⟨a / b, ?_, ?_⟩
  · have h1 : P.val.valuation a ≤ 1 := (P.val.valuation_le_one_iff a).2 haP
    have h2 : 1 < P.val.valuation b := by
      rcases lt_or_ge 1 (P.val.valuation b) with h' | h'
      · exact h'
      · exact absurd (P.val.mem_of_valuation_le_one b h') hbP
    rw [map_div₀, div_lt_one₀ (lt_trans zero_lt_one h2)]
    exact lt_of_le_of_lt h1 h2
  · have h1 : Q.val.valuation b ≤ 1 := (Q.val.valuation_le_one_iff b).2 hbQ
    have h2 : 1 < Q.val.valuation a := by
      rcases lt_or_ge 1 (Q.val.valuation a) with h' | h'
      · exact h'
      · exact absurd (Q.val.mem_of_valuation_le_one a h') haQ
    rw [map_div₀, lt_div_iff₀ (zero_lt_iff.2 ?_), one_mul]
    · exact lt_of_le_of_lt h1 h2
    · rw [Valuation.ne_zero_iff]
      exact hb0

/-- **Archimedean property of a place's values**: powers of a value below
one eventually drop below any nonzero value. From the uniformizer
classification of P1.-/
theorem exists_pow_valuation_lt (P : Place k F) {y w : F} (hy0 : y ≠ 0)
    (hylt : P.val.valuation y < 1) (hw0 : w ≠ 0) :
    ∃ n : ℕ, P.val.valuation y ^ n < P.val.valuation w := by
  classical
  rcases lt_or_ge (P.val.valuation w) 1 with hwlt | hwge
  · -- Both small: compare through uniformizer exponents.
    obtain ⟨z, hz0, hz⟩ := exists_valuation_lt_one_of_ne_top P.ne_top
    have htr := transcendental_of_valuation_lt_one P.algebraMap_mem
      (fun v hv ↦ exists_algebraMap_eq_of_isAlgebraic hv) hz0 hz
    haveI := finiteDimensional_adjoin_of_transcendental (k := k) htr
    obtain ⟨t, ht0, htlt, htmax⟩ :=
      exists_valuation_uniformizer P.algebraMap_mem hz0 hz
    have hyv : P.val.valuation y ≠ 0 := (Valuation.ne_zero_iff _).2 hy0
    have hwv : P.val.valuation w ≠ 0 := (Valuation.ne_zero_iff _).2 hw0
    obtain ⟨j, hj0, hj⟩ := valuation_eq_pow_uniformizer P.algebraMap_mem
      hz0 hz ht0 htlt htmax hyv hylt
    obtain ⟨m, hm0, hm⟩ := valuation_eq_pow_uniformizer P.algebraMap_mem
      hz0 hz ht0 htlt htmax hwv hwlt
    refine ⟨m + 1, ?_⟩
    rw [hj, hm, ← pow_mul]
    have hlt : m < j * (m + 1) := by
      have := Nat.one_le_iff_ne_zero.2 hj0.ne'
      calc m < m + 1 := Nat.lt_succ_self m
        _ ≤ j * (m + 1) := Nat.le_mul_of_pos_left _ hj0
    exact pow_lt_pow_right_of_lt_one₀ (zero_lt_iff.2 ht0) htlt hlt
  · -- `w` is not small: the first power below one already works.
    refine ⟨1, ?_⟩
    rw [pow_one]
    exact lt_of_lt_of_le hylt hwge

end Place

section Indicator

variable {O : ValuationSubring F}

/-- Indicator estimate, small case: where `v y < 1`, the element
`y^n / (1 + y^n)` has value `(v y)^n` (for positive `n`; at `n = 0` the
expression degenerates in characteristic two).-/
theorem valuation_indicator_of_lt_one {y : F} (hy : O.valuation y < 1)
    {n : ℕ} (hn : n ≠ 0) :
    O.valuation (y ^ n / (1 + y ^ n)) = O.valuation y ^ n := by
  have h2 : O.valuation (1 + y ^ n) = 1 := by
    have h3 : O.valuation (y ^ n) < 1 := by
      rw [Valuation.map_pow]
      exact pow_lt_one₀ zero_le hy hn
    have h4 := Valuation.map_add_eq_of_lt_left O.valuation
      (x := (1 : F)) (y := y ^ n) (by rwa [Valuation.map_one])
    rwa [Valuation.map_one] at h4
  rw [map_div₀, h2, div_one, Valuation.map_pow]

/-- Indicator estimate, large case: where `1 < v y`, the element
`y^n / (1 + y^n)` is a unit for positive `n`.-/
theorem valuation_indicator_of_gt_one {y : F} (hy : 1 < O.valuation y)
    {n : ℕ} (hn : n ≠ 0) :
    O.valuation (y ^ n / (1 + y ^ n)) = 1 := by
  have h2 : O.valuation (1 + y ^ n) = O.valuation (y ^ n) := by
    have h3 : O.valuation (1 : F) < O.valuation (y ^ n) := by
      rw [Valuation.map_one, Valuation.map_pow]
      exact one_lt_pow₀ hy hn
    exact Valuation.map_add_eq_of_lt_right O.valuation h3
  have hy0 : y ≠ 0 := by
    intro h0
    rw [h0, Valuation.map_zero] at hy
    simp at hy
  have h4 : O.valuation (y ^ n) ≠ 0 := by
    rw [Valuation.ne_zero_iff]
    exact pow_ne_zero n hy0
  rw [map_div₀, h2, div_self h4]

end Indicator

section WeakApproximation

variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- **Weak approximation, existence form** (Stichtenoth Theorem 1.3.1,
the core induction): given a place `P₀` distinct from each of finitely
many places `Ps j`, some element is large at `P₀` and small at every
`Ps j`. The boundary case `v y = 1` at the new place is handled by
multiplying with a separator; the case `v y > 1` by the ultrametric
indicator `y^n/(1+y^n)`; the Archimedean property supplies the power.-/
theorem Place.exists_one_lt_forall_lt_one {r : ℕ} (P₀ : Place k F)
    (Ps : Fin r → Place k F) (hne : ∀ j, P₀ ≠ Ps j) :
    ∃ z : F, 1 < P₀.val.valuation z ∧
      ∀ j, (Ps j).val.valuation z < 1 := by
  classical
  induction r with
  | zero =>
    obtain ⟨x, hx⟩ : ∃ x : F, x ∉ P₀.val := by
      by_contra hc
      push Not at hc
      exact P₀.ne_top (by ext y; simpa using hc y)
    refine ⟨x, ?_, fun j ↦ j.elim0⟩
    exact lt_of_not_ge fun h ↦ hx (P₀.val.mem_of_valuation_le_one x h)
  | succ r ih =>
    obtain ⟨y, hy₀, hyj⟩ := ih (fun j ↦ Ps j.castSucc)
      (fun j ↦ hne j.castSucc)
    obtain ⟨w, hwlast, hw₀⟩ := exists_lt_one_gt_one (hne (Fin.last r)).symm
    have hy0 : y ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hy₀
      simp at hy₀
    have hw0 : w ≠ 0 := by
      intro h0
      rw [h0, Valuation.map_zero] at hw₀
      simp at hw₀
    -- A uniform power making `y`-smallness beat `w` at the old places.
    have harch : ∀ j : Fin r, ∃ n : ℕ,
        (Ps j.castSucc).val.valuation y ^ n <
          (Ps j.castSucc).val.valuation w⁻¹ := fun j ↦
      (Ps j.castSucc).exists_pow_valuation_lt hy0 (hyj j)
        (inv_ne_zero hw0)
    choose ns hns using harch
    set n : ℕ := (Finset.univ.sup ns) + 1 with hn
    have hn0 : n ≠ 0 := Nat.succ_ne_zero _
    have hyn : ∀ j : Fin r, (Ps j.castSucc).val.valuation y ^ n *
        (Ps j.castSucc).val.valuation w < 1 := by
      intro j
      have h1 : (Ps j.castSucc).val.valuation y ^ n ≤
          (Ps j.castSucc).val.valuation y ^ ns j :=
        pow_le_pow_right_of_le_one' (hyj j).le
          (le_trans (Finset.le_sup (Finset.mem_univ j)) (Nat.le_succ _))
      have h2 : (Ps j.castSucc).val.valuation y ^ n <
          (Ps j.castSucc).val.valuation w⁻¹ :=
        lt_of_le_of_lt h1 (hns j)
      have hwv : (0 : _) < (Ps j.castSucc).val.valuation w :=
        zero_lt_iff.2 ((Valuation.ne_zero_iff _).2 hw0)
      have h3 := (OrderIso.mulRight₀ _ hwv).strictMono h2
      simp only [OrderIso.mulRight₀_apply] at h3
      rwa [map_inv₀, inv_mul_cancel₀ hwv.ne'] at h3
    rcases lt_trichotomy ((Ps (Fin.last r)).val.valuation y) 1 with
      hcase | hcase | hcase
    · -- `y` is already small at the new place.
      refine ⟨y, hy₀, fun j ↦ ?_⟩
      refine Fin.lastCases ?_ (fun i ↦ ?_) j
      · exact hcase
      · exact hyj i
    · -- Boundary: multiply a power of `y` with the separator.
      refine ⟨y ^ n * w, ?_, fun j ↦ ?_⟩
      · rw [Valuation.map_mul, Valuation.map_pow]
        exact one_lt_mul (one_lt_pow₀ hy₀ hn0).le hw₀
      · refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · rw [Valuation.map_mul, Valuation.map_pow, hcase, one_pow,
            one_mul]
          exact hwlast
        · rw [Valuation.map_mul, Valuation.map_pow]
          exact hyn i
    · -- `y` is large at the new place: use the indicator.
      refine ⟨y ^ n / (1 + y ^ n) * w, ?_, fun j ↦ ?_⟩
      · rw [Valuation.map_mul, valuation_indicator_of_gt_one hy₀ hn0,
          one_mul]
        exact hw₀
      · refine Fin.lastCases ?_ (fun i ↦ ?_) j
        · rw [Valuation.map_mul,
            valuation_indicator_of_gt_one hcase hn0, one_mul]
          exact hwlast
        · rw [Valuation.map_mul,
            valuation_indicator_of_lt_one (hyj i) hn0]
          exact hyn i

end WeakApproximation

end

end AclGeom
