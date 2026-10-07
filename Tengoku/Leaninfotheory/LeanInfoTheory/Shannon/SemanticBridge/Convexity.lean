/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Probability.FiniteChannel
import Tengoku.Leaninfotheory.LeanInfoTheory.Probability.FiniteMixture
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.EntropyConcavity
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.LogSum
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.KL
import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.SemanticBridge.Product

/-!
# Convexity results for finite Shannon information measures

This opt-in semantic-bridge module develops the finite convexity package for
KL divergence and mutual information.

The canonical KL theorems remain `ENNReal`-valued. Their proofs split on
whether the finite weighted component divergence is `top`. In the finite
branch, only components with nonzero selector mass need support inclusion;
inactive components may have infinite KL because `0 * top = 0`. The private
infrastructure below keeps that support and `toReal` bookkeeping out of the
public API.
-/

namespace LeanInfoTheory
namespace Shannon

open MeasureTheory
open scoped BigOperators

noncomputable section

universe u v w

/-! ## Private finite-branch infrastructure -/

private theorem component_klDiv_ne_top_of_weighted_sum_ne_top
    {iota : Type u} {alpha : Type v}
    [Fintype iota]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (r : PMF iota) (P Q : iota -> PMF alpha)
    (hfinite :
      (∑ i, r i *
        InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure) ≠ ⊤)
    {i : iota} (hi : r i ≠ 0) :
    InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure ≠ ⊤ := by
  have hterm :
      r i * InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure ≠ ⊤ :=
    (ENNReal.sum_ne_top.mp hfinite) i (Finset.mem_univ i)
  exact (ENNReal.lt_top_of_mul_ne_top_right hterm hi).ne

private theorem support_bind_subset_of_active
    {iota : Type u} {alpha : Type v}
    (r : PMF iota) (P Q : iota -> PMF alpha)
    (hsupport :
      ∀ i, r i ≠ 0 -> (P i).support ⊆ (Q i).support) :
    (r.bind P).support ⊆ (r.bind Q).support := by
  intro a ha
  rw [PMF.mem_support_bind_iff] at ha ⊢
  rcases ha with ⟨i, hi, hPa⟩
  exact ⟨i, hi, hsupport i ((r.mem_support_iff i).1 hi) hPa⟩

private theorem toReal_sum_mul_klDiv_of_ne_top
    {iota : Type u} {alpha : Type v}
    [Fintype iota]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (r : PMF iota) (P Q : iota -> PMF alpha)
    (hfinite :
      (∑ i, r i *
        InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure) ≠ ⊤) :
    (∑ i, r i *
        InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure).toReal =
      ∑ i, (r i).toReal *
        (InformationTheory.klDiv
          (P i).toMeasure (Q i).toMeasure).toReal := by
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro i _
    exact (ENNReal.sum_ne_top.mp hfinite) i (Finset.mem_univ i)

private theorem klDiv_bind_ne_top_of_weighted_sum_ne_top
    {iota : Type u} {alpha : Type v}
    [Fintype iota] [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (r : PMF iota) (P Q : iota -> PMF alpha)
    (hfinite :
      (∑ i, r i *
        InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure) ≠ ⊤) :
    InformationTheory.klDiv
        (r.bind P).toMeasure (r.bind Q).toMeasure ≠ ⊤ := by
  apply (klDiv_pmf_ne_top_iff_support_subset (r.bind P) (r.bind Q)).2
  apply support_bind_subset_of_active r P Q
  intro i hi
  apply (klDiv_pmf_ne_top_iff_support_subset (P i) (Q i)).1
  exact
    component_klDiv_ne_top_of_weighted_sum_ne_top
      r P Q hfinite hi

private theorem toReal_klDiv_bind_le_toReal_sum_of_ne_top
    {iota : Type u} {alpha : Type v}
    [Fintype iota] [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (r : PMF iota) (P Q : iota -> PMF alpha)
    (hfinite :
      (∑ i, r i *
        InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure) ≠ ⊤) :
    (InformationTheory.klDiv
        (r.bind P).toMeasure (r.bind Q).toMeasure).toReal <=
      (∑ i, r i *
        InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure).toReal := by
  classical
  let := Fintype.ofFinite alpha
  have hcomponentSupport (i : iota) (hi : r i ≠ 0) :
      (P i).support ⊆ (Q i).support :=
    (klDiv_pmf_ne_top_iff_support_subset (P i) (Q i)).1
      (component_klDiv_ne_top_of_weighted_sum_ne_top
        r P Q hfinite hi)
  have hcomponentExpansion (i : iota) (hi : r i ≠ 0) :
      (InformationTheory.klDiv
          (P i).toMeasure (Q i).toMeasure).toReal =
        ∑ x, (P i x).toReal *
          Real.log ((P i x / Q i x).toReal) := by
    apply toReal_klDiv_pmf_eq_sum
    exact
      (toMeasure_absolutelyContinuous_iff_support_subset (P i) (Q i)).2
        (hcomponentSupport i hi)
  have hmixSupport :
      (r.bind P).support ⊆ (r.bind Q).support := by
    apply support_bind_subset_of_active r P Q
    exact hcomponentSupport
  have hmixAC :
      (r.bind P).toMeasure ≪ (r.bind Q).toMeasure :=
    (toMeasure_absolutelyContinuous_iff_support_subset
      (r.bind P) (r.bind Q)).2 hmixSupport
  have hpoint (x : alpha) :
      ((r.bind P) x).toReal *
          Real.log (((r.bind P) x / (r.bind Q) x).toReal) <=
        ∑ i, (r i).toReal *
          ((P i x).toReal * Real.log ((P i x / Q i x).toReal)) := by
    let aMass : iota -> NNReal :=
      fun i => (r i).toNNReal * (P i x).toNNReal
    let bMass : iota -> NNReal :=
      fun i => (r i).toNNReal * (Q i x).toNNReal
    have hscalarSupport :
        ∀ i ∈ (Finset.univ : Finset iota),
          aMass i ≠ 0 -> bMass i ≠ 0 := by
      intro i _ hai
      have hriNN : (r i).toNNReal ≠ 0 := by
        intro hri
        exact hai (by simp [aMass, hri])
      have hPiNN : (P i x).toNNReal ≠ 0 := by
        intro hPi
        exact hai (by simp [aMass, hPi])
      have hri : r i ≠ 0 := (ENNReal.toNNReal_ne_zero.mp hriNN).1
      have hPi : P i x ≠ 0 := (ENNReal.toNNReal_ne_zero.mp hPiNN).1
      have hPmem : x ∈ (P i).support :=
        ((P i).mem_support_iff x).2 hPi
      have hQi : Q i x ≠ 0 :=
        ((Q i).mem_support_iff x).1 ((hcomponentSupport i hri) hPmem)
      have hQiNN : (Q i x).toNNReal ≠ 0 :=
        ENNReal.toNNReal_ne_zero.mpr ⟨hQi, (Q i).apply_ne_top x⟩
      exact mul_ne_zero hriNN hQiNN
    have haSum :
        ((∑ i, aMass i : NNReal) : Real) =
          ((r.bind P) x).toReal := by
      calc
        ((∑ i, aMass i : NNReal) : Real) =
            ∑ i, (aMass i : Real) := by rw [NNReal.coe_sum]
        _ = ∑ i, (r i).toReal * (P i x).toReal := by
          apply Finset.sum_congr rfl
          intro i _
          simp [aMass, ENNReal.coe_toNNReal_eq_toReal]
        _ = ((r.bind P) x).toReal :=
          (PMF.bind_toReal_apply r P x).symm
    have hbSum :
        ((∑ i, bMass i : NNReal) : Real) =
          ((r.bind Q) x).toReal := by
      calc
        ((∑ i, bMass i : NNReal) : Real) =
            ∑ i, (bMass i : Real) := by rw [NNReal.coe_sum]
        _ = ∑ i, (r i).toReal * (Q i x).toReal := by
          apply Finset.sum_congr rfl
          intro i _
          simp [bMass, ENNReal.coe_toNNReal_eq_toReal]
        _ = ((r.bind Q) x).toReal :=
          (PMF.bind_toReal_apply r Q x).symm
    have hscaled (i : iota) :
        (aMass i : Real) *
            Real.log ((aMass i : Real) / (bMass i : Real)) =
          (r i).toReal *
            ((P i x).toReal * Real.log ((P i x / Q i x).toReal)) := by
      by_cases hi : r i = 0
      · simp [aMass, bMass, hi]
      · have hriReal : (r i).toReal ≠ 0 :=
          ENNReal.toReal_ne_zero.mpr ⟨hi, r.apply_ne_top i⟩
        simp only [aMass, bMass, NNReal.coe_mul,
          ENNReal.coe_toNNReal_eq_toReal, ENNReal.toReal_div]
        rw [mul_div_mul_left _ _ hriReal]
        ring
    have hlog :=
      real_logSum_inequality_of_support
        (Finset.univ : Finset iota) aMass bMass hscalarSupport
    calc
      ((r.bind P) x).toReal *
          Real.log (((r.bind P) x / (r.bind Q) x).toReal) =
          ((∑ i, aMass i : NNReal) : Real) *
            Real.log
              (((∑ i, aMass i : NNReal) : Real) /
                ((∑ i, bMass i : NNReal) : Real)) := by
        rw [ENNReal.toReal_div, haSum, hbSum]
      _ <= ∑ i, (aMass i : Real) *
          Real.log ((aMass i : Real) / (bMass i : Real)) := hlog
      _ = ∑ i, (r i).toReal *
          ((P i x).toReal * Real.log ((P i x / Q i x).toReal)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hscaled i
  rw [toReal_klDiv_pmf_eq_sum (r.bind P) (r.bind Q) hmixAC,
    toReal_sum_mul_klDiv_of_ne_top r P Q hfinite]
  calc
    (∑ x, ((r.bind P) x).toReal *
        Real.log (((r.bind P) x / (r.bind Q) x).toReal)) <=
        ∑ x, ∑ i, (r i).toReal *
          ((P i x).toReal * Real.log ((P i x / Q i x).toReal)) := by
      apply Finset.sum_le_sum
      intro x _
      exact hpoint x
    _ = ∑ i, (r i).toReal *
        (∑ x, (P i x).toReal *
          Real.log ((P i x / Q i x).toReal)) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ i, (r i).toReal *
        (InformationTheory.klDiv
          (P i).toMeasure (Q i).toMeasure).toReal := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : r i = 0
      · simp [hi]
      · rw [hcomponentExpansion i hi]

/-!
## KL joint convexity
-/

/--
KL divergence is jointly convex under a common finite PMF-valued selector.

The result is canonical in `ENNReal`. An inactive selector component may have
infinite KL because its weighted contribution is `0 * top = 0`.
-/
theorem klDiv_bind_le_sum
    {iota : Type u} {alpha : Type v}
    [Fintype iota] [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (r : PMF iota) (P Q : iota -> PMF alpha) :
    InformationTheory.klDiv
        (r.bind P).toMeasure (r.bind Q).toMeasure <=
      ∑ i, r i *
        InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure := by
  classical
  by_cases hfinite :
      (∑ i, r i *
        InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure) = ⊤
  · rw [hfinite]
    exact le_top
  · have hmixFinite :=
      klDiv_bind_ne_top_of_weighted_sum_ne_top r P Q hfinite
    exact
      (ENNReal.toReal_le_toReal hmixFinite hfinite).mp
        (toReal_klDiv_bind_le_toReal_sum_of_ne_top
          r P Q hfinite)

/--
Real-valued KL joint convexity under support inclusion for every active
selector component.

No support condition is required when the selector mass is zero, even if that
inactive component has infinite KL.
-/
theorem toReal_klDiv_bind_le_sum
    {iota : Type u} {alpha : Type v}
    [Fintype iota] [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (r : PMF iota) (P Q : iota -> PMF alpha)
    (hsupport :
      ∀ i, r i ≠ 0 -> (P i).support ⊆ (Q i).support) :
    (InformationTheory.klDiv
        (r.bind P).toMeasure (r.bind Q).toMeasure).toReal <=
      ∑ i, (r i).toReal *
        (InformationTheory.klDiv
          (P i).toMeasure (Q i).toMeasure).toReal := by
  classical
  have hcomponentFinite (i : iota) (hi : r i ≠ 0) :
      InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure ≠ ⊤ :=
    (klDiv_pmf_ne_top_iff_support_subset (P i) (Q i)).2
      (hsupport i hi)
  have htermFinite (i : iota) :
      r i * InformationTheory.klDiv
        (P i).toMeasure (Q i).toMeasure ≠ ⊤ := by
    by_cases hi : r i = 0
    · simp [hi]
    · exact ENNReal.mul_ne_top (r.apply_ne_top i) (hcomponentFinite i hi)
  have hsumFinite :
      (∑ i, r i *
        InformationTheory.klDiv (P i).toMeasure (Q i).toMeasure) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun i _ => htermFinite i
  have hmixFinite :=
    klDiv_bind_ne_top_of_weighted_sum_ne_top r P Q hsumFinite
  have hbound :
      (InformationTheory.klDiv
          (r.bind P).toMeasure (r.bind Q).toMeasure).toReal <=
        (∑ i, r i *
          InformationTheory.klDiv
            (P i).toMeasure (Q i).toMeasure).toReal :=
    (ENNReal.toReal_le_toReal hmixFinite hsumFinite).2
      (klDiv_bind_le_sum r P Q)
  rw [toReal_sum_mul_klDiv_of_ne_top r P Q hsumFinite] at hbound
  exact hbound

/-! ### Binary textbook forms -/

/--
Binary joint convexity of KL divergence.

The weight is `t` on the first component and `1 - t` on the second.
-/
theorem klDiv_binaryMixture_le
    {alpha : Type u} [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (t : NNReal) (ht : t <= 1)
    (p1 p2 q1 q2 : PMF alpha) :
    InformationTheory.klDiv
        (PMF.binaryMixture t ht p1 p2).toMeasure
        (PMF.binaryMixture t ht q1 q2).toMeasure <=
      (t : ENNReal) *
          InformationTheory.klDiv p1.toMeasure q1.toMeasure +
        ((1 - t : NNReal) : ENNReal) *
          InformationTheory.klDiv p2.toMeasure q2.toMeasure := by
  let r : PMF Bool :=
    PMF.ofFintype
      (fun b : Bool => ((cond b t (1 - t) : NNReal) : ENNReal))
      (by simp [ht])
  have hr_true : r true = (t : ENNReal) := by
    simp only [r, PMF.ofFintype_apply, Bool.cond_true]
  have hr_false : r false = ((1 - t : NNReal) : ENNReal) := by
    simp only [r, PMF.ofFintype_apply, Bool.cond_false]
  change
    InformationTheory.klDiv
        (r.bind (fun b => if b then p1 else p2)).toMeasure
        (r.bind (fun b => if b then q1 else q2)).toMeasure <=
      (t : ENNReal) * InformationTheory.klDiv p1.toMeasure q1.toMeasure +
        ((1 - t : NNReal) : ENNReal) *
          InformationTheory.klDiv p2.toMeasure q2.toMeasure
  simpa only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true,
    Finset.sum_singleton, hr_true, hr_false, ite_true, ite_false] using
    (klDiv_bind_le_sum r
      (fun b => if b then p1 else p2)
      (fun b => if b then q1 else q2))

/--
Real-valued binary KL joint convexity with support assumptions only for
components whose weights can be nonzero.

At `t = 0`, only the second support implication is used; at `t = 1`, only the
first is used.
-/
theorem toReal_klDiv_binaryMixture_le
    {alpha : Type u} [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (t : NNReal) (ht : t <= 1)
    (p1 p2 q1 q2 : PMF alpha)
    (hfirst : t ≠ 0 -> p1.support ⊆ q1.support)
    (hsecond : t ≠ 1 -> p2.support ⊆ q2.support) :
    (InformationTheory.klDiv
        (PMF.binaryMixture t ht p1 p2).toMeasure
        (PMF.binaryMixture t ht q1 q2).toMeasure).toReal <=
      (t : Real) *
          (InformationTheory.klDiv p1.toMeasure q1.toMeasure).toReal +
        ((1 - t : NNReal) : Real) *
          (InformationTheory.klDiv p2.toMeasure q2.toMeasure).toReal := by
  let r : PMF Bool :=
    PMF.ofFintype
      (fun b : Bool => ((cond b t (1 - t) : NNReal) : ENNReal))
      (by simp [ht])
  have hsupport :
      ∀ b, r b ≠ 0 ->
        (if b then p1 else p2).support ⊆
          (if b then q1 else q2).support := by
    intro b hb
    cases b
    · apply hsecond
      intro ht1
      exact hb (by simp [r, PMF.ofFintype_apply, ht1])
    · apply hfirst
      intro ht0
      exact hb (by simp [r, PMF.ofFintype_apply, ht0])
  simpa [r, PMF.binaryMixture, Fintype.univ_bool, PMF.ofFintype_apply,
    ENNReal.coe_sub] using
    (toReal_klDiv_bind_le_sum
      r
      (fun b => if b then p1 else p2)
      (fun b => if b then q1 else q2)
      hsupport)

/-! ### Private binary equality infrastructure -/

private def weightedPair
    (t x1 x2 : NNReal) : Bool -> NNReal
  | false => (1 - t) * x2
  | true => t * x1

private theorem one_sub_ne_zero {t : NNReal} (ht : t < 1) :
    1 - t ≠ 0 :=
  ne_of_gt (tsub_pos_iff_lt.2 ht)

private theorem real_weighted_ratio
    (w p q : NNReal) (hw : w ≠ 0) :
    (((w * p : NNReal) : Real) / ((w * q : NNReal) : Real)) =
      (p : Real) / (q : Real) := by
  have hwReal : (w : Real) ≠ 0 := by exact_mod_cast hw
  push_cast
  field_simp

private theorem weightedPair_support
    (t p1 q1 p2 q2 : NNReal) (ht0 : 0 < t) (ht1 : t < 1)
    (h1 : p1 ≠ 0 -> q1 ≠ 0) (h2 : p2 ≠ 0 -> q2 ≠ 0) :
    ∀ b ∈ (Finset.univ : Finset Bool),
      weightedPair t p1 p2 b ≠ 0 ->
        weightedPair t q1 q2 b ≠ 0 := by
  intro b _ hb
  have ht : t ≠ 0 := ne_of_gt ht0
  have hu : 1 - t ≠ 0 := one_sub_ne_zero ht1
  cases b with
  | false =>
      simp only [weightedPair] at hb ⊢
      have hp2 : p2 ≠ 0 := by
        intro hp2
        exact hb (by simp [hp2])
      exact mul_ne_zero hu (h2 hp2)
  | true =>
      simp only [weightedPair] at hb ⊢
      have hp1 : p1 ≠ 0 := by
        intro hp1
        exact hb (by simp [hp1])
      exact mul_ne_zero ht (h1 hp1)

private theorem sum_weightedPair
    (t x1 x2 : NNReal) :
    ∑ b : Bool, weightedPair t x1 x2 b =
      t * x1 + (1 - t) * x2 := by
  simp [weightedPair]

private def realKlAtom (p q : NNReal) : Real :=
  (p : Real) * Real.log ((p : Real) / (q : Real))

private def mixedMass (t p1 p2 : NNReal) : NNReal :=
  t * p1 + (1 - t) * p2

private theorem real_binary_logSum_le
    (t p1 q1 p2 q2 : NNReal) (ht0 : 0 < t) (ht1 : t < 1)
    (h1 : p1 ≠ 0 -> q1 ≠ 0) (h2 : p2 ≠ 0 -> q2 ≠ 0) :
    realKlAtom (mixedMass t p1 p2) (mixedMass t q1 q2) <=
      (t : Real) * realKlAtom p1 q1 +
        ((1 - t : NNReal) : Real) * realKlAtom p2 q2 := by
  have ht : t ≠ 0 := ne_of_gt ht0
  have hu : 1 - t ≠ 0 := one_sub_ne_zero ht1
  have hr1 := real_weighted_ratio t p1 q1 ht
  have hr2 := real_weighted_ratio (1 - t) p2 q2 hu
  have h := real_logSum_inequality_of_support
    (Finset.univ : Finset Bool)
    (weightedPair t p1 p2) (weightedPair t q1 q2)
    (weightedPair_support t p1 q1 p2 q2 ht0 ht1 h1 h2)
  rw [sum_weightedPair, sum_weightedPair] at h
  simp only [Fintype.univ_bool, Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    weightedPair] at h
  rw [hr1, hr2] at h
  push_cast at h
  simpa [realKlAtom, mixedMass, mul_assoc] using h

private theorem weightedPair_constant_ratio_iff_cross
    (t p1 q1 p2 q2 : NNReal) (ht0 : 0 < t) (ht1 : t < 1)
    (h1 : p1 ≠ 0 -> q1 ≠ 0) (h2 : p2 ≠ 0 -> q2 ≠ 0) :
    (∃ c : Real, ∀ b ∈ (Finset.univ : Finset Bool),
        (weightedPair t p1 p2 b ≠ 0 ∨
          weightedPair t q1 q2 b ≠ 0) ->
        ((weightedPair t p1 p2 b : NNReal) : Real) /
            ((weightedPair t q1 q2 b : NNReal) : Real) = c) ↔
      p1 * q2 = p2 * q1 := by
  have ht : t ≠ 0 := ne_of_gt ht0
  have hu : 1 - t ≠ 0 := one_sub_ne_zero ht1
  have hr1 := real_weighted_ratio t p1 q1 ht
  have hr2 := real_weighted_ratio (1 - t) p2 q2 hu
  by_cases hq1 : q1 = 0
  · have hp1 : p1 = 0 := by
      by_contra hp1
      exact (h1 hp1) hq1
    by_cases hq2 : q2 = 0
    · have hp2 : p2 = 0 := by
        by_contra hp2
        exact (h2 hp2) hq2
      constructor
      · intro _
        simp [hp1, hq1, hp2, hq2]
      · intro _
        refine ⟨0, ?_⟩
        intro b _ hactive
        cases b <;> simp [weightedPair, hp1, hq1, hp2, hq2] at hactive
    · constructor
      · intro _
        simp [hp1, hq1]
      · intro _
        refine ⟨(p2 : Real) / (q2 : Real), ?_⟩
        intro b _ hactive
        cases b with
        | false => exact hr2
        | true =>
            simp [weightedPair, hp1, hq1] at hactive
  · by_cases hq2 : q2 = 0
    · have hp2 : p2 = 0 := by
        by_contra hp2
        exact (h2 hp2) hq2
      constructor
      · intro _
        simp [hp2, hq2]
      · intro _
        refine ⟨(p1 : Real) / (q1 : Real), ?_⟩
        intro b _ hactive
        cases b with
        | false =>
            simp [weightedPair, hp2, hq2] at hactive
        | true => exact hr1
    · have hq1Real : (q1 : Real) ≠ 0 := by exact_mod_cast hq1
      have hq2Real : (q2 : Real) ≠ 0 := by exact_mod_cast hq2
      constructor
      · rintro ⟨c, hc⟩
        have hc1 := hc true (by simp)
          (Or.inr (mul_ne_zero ht hq1))
        have hc2 := hc false (by simp)
          (Or.inr (mul_ne_zero hu hq2))
        have hratio :
            (p1 : Real) / (q1 : Real) =
              (p2 : Real) / (q2 : Real) :=
          hr1.symm.trans (hc1.trans (hc2.symm.trans hr2))
        field_simp [hq1Real, hq2Real] at hratio
        have hcrossReal :
            (p1 : Real) * (q2 : Real) =
              (p2 : Real) * (q1 : Real) := by
          simpa [mul_comm] using hratio
        exact_mod_cast hcrossReal
      · intro hcross
        have hcrossReal :
            (p1 : Real) * (q2 : Real) =
              (p2 : Real) * (q1 : Real) := by
          exact_mod_cast hcross
        have hratio :
            (p1 : Real) / (q1 : Real) =
              (p2 : Real) / (q2 : Real) := by
          field_simp [hq1Real, hq2Real]
          simpa [mul_comm] using hcrossReal
        refine ⟨(p1 : Real) / (q1 : Real), ?_⟩
        intro b _ _
        cases b with
        | false => exact hr2.trans hratio.symm
        | true => exact hr1

private theorem real_binary_logSum_eq_iff_cross
    (t p1 q1 p2 q2 : NNReal) (ht0 : 0 < t) (ht1 : t < 1)
    (h1 : p1 ≠ 0 -> q1 ≠ 0) (h2 : p2 ≠ 0 -> q2 ≠ 0) :
    (realKlAtom (mixedMass t p1 p2) (mixedMass t q1 q2) =
        (t : Real) * realKlAtom p1 q1 +
          ((1 - t : NNReal) : Real) * realKlAtom p2 q2) ↔
      p1 * q2 = p2 * q1 := by
  have ht : t ≠ 0 := ne_of_gt ht0
  have hu : 1 - t ≠ 0 := one_sub_ne_zero ht1
  have hr1 := real_weighted_ratio t p1 q1 ht
  have hr2 := real_weighted_ratio (1 - t) p2 q2 hu
  have h := real_logSum_eq_iff_exists_constant_ratio_of_support
    (Finset.univ : Finset Bool)
    (weightedPair t p1 p2) (weightedPair t q1 q2)
    (weightedPair_support t p1 q1 p2 q2 ht0 ht1 h1 h2)
  rw [sum_weightedPair, sum_weightedPair] at h
  simp only [Fintype.univ_bool, Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true,
    weightedPair] at h
  rw [hr1, hr2] at h
  push_cast at h
  have h' :
      (realKlAtom (mixedMass t p1 p2) (mixedMass t q1 q2) =
          (t : Real) * realKlAtom p1 q1 +
            ((1 - t : NNReal) : Real) * realKlAtom p2 q2) ↔
        ∃ c : Real, ∀ b ∈ (Finset.univ : Finset Bool),
          (weightedPair t p1 p2 b ≠ 0 ∨
            weightedPair t q1 q2 b ≠ 0) ->
          ((weightedPair t p1 p2 b : NNReal) : Real) /
              ((weightedPair t q1 q2 b : NNReal) : Real) = c := by
    simpa [realKlAtom, mixedMass, mul_assoc, Fintype.univ_bool,
      weightedPair] using h
  rw [h']
  exact weightedPair_constant_ratio_iff_cross
    t p1 q1 p2 q2 ht0 ht1 h1 h2

private theorem binaryMixture_support_subset
    {alpha : Type u}
    (t : NNReal) (ht : t <= 1) (p1 q1 p2 q2 : PMF alpha)
    (h1 : p1.support ⊆ q1.support)
    (h2 : p2.support ⊆ q2.support) :
    (PMF.binaryMixture t ht p1 p2).support ⊆
      (PMF.binaryMixture t ht q1 q2).support := by
  intro x hx
  rw [PMF.binaryMixture, PMF.mem_support_bind_iff] at hx ⊢
  obtain ⟨b, hb, hpx⟩ := hx
  refine ⟨b, hb, ?_⟩
  cases b with
  | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hpx ⊢
      exact h2 hpx
  | true =>
      simp only [↓reduceIte] at hpx ⊢
      exact h1 hpx

private def pmfMassNN {alpha : Type u} (p : PMF alpha) (x : alpha) : NNReal :=
  (p x).toNNReal

private theorem pmfMassNN_ne_zero_iff
    {alpha : Type u} (p : PMF alpha) (x : alpha) :
    pmfMassNN p x ≠ 0 ↔ p x ≠ 0 := by
  simp [pmfMassNN, ENNReal.toNNReal_ne_zero, p.apply_ne_top x]

private theorem pmfMassNN_binaryMixture
    {alpha : Type u}
    (t : NNReal) (ht : t <= 1) (p1 p2 : PMF alpha) (x : alpha) :
    pmfMassNN (PMF.binaryMixture t ht p1 p2) x =
      mixedMass t (pmfMassNN p1 x) (pmfMassNN p2 x) := by
  apply ENNReal.coe_injective
  simp only [pmfMassNN, mixedMass]
  rw [ENNReal.coe_toNNReal
    ((PMF.binaryMixture t ht p1 p2).apply_ne_top x)]
  rw [PMF.binaryMixture_apply]
  simp [
    ENNReal.coe_toNNReal (p1.apply_ne_top x),
    ENNReal.coe_toNNReal (p2.apply_ne_top x),
    ENNReal.coe_sub]

private theorem realKlAtom_pmfMassNN
    {alpha : Type u} (p q : PMF alpha) (x : alpha) :
    realKlAtom (pmfMassNN p x) (pmfMassNN q x) =
      (p x).toReal * Real.log ((p x / q x).toReal) := by
  simp [realKlAtom, pmfMassNN, ENNReal.coe_toNNReal_eq_toReal,
    ENNReal.toReal_div]

private theorem pmfMassNN_cross_iff
    {alpha : Type u} (p1 q1 p2 q2 : PMF alpha) (x : alpha) :
    pmfMassNN p1 x * pmfMassNN q2 x =
        pmfMassNN p2 x * pmfMassNN q1 x ↔
      p1 x * q2 x = p2 x * q1 x := by
  rw [← ENNReal.coe_inj]
  simp [pmfMassNN,
    ENNReal.coe_toNNReal (p1.apply_ne_top x),
    ENNReal.coe_toNNReal (q1.apply_ne_top x),
    ENNReal.coe_toNNReal (p2.apply_ne_top x),
    ENNReal.coe_toNNReal (q2.apply_ne_top x)]

private def realKL
    {alpha : Type u} [MeasurableSpace alpha] (p q : PMF alpha) : Real :=
  (InformationTheory.klDiv p.toMeasure q.toMeasure).toReal

private theorem realKL_eq_sum_realKlAtom
    {alpha : Type u}
    [Fintype alpha] [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (p q : PMF alpha) (h : p.support ⊆ q.support) :
    realKL p q =
      ∑ x : alpha, realKlAtom (pmfMassNN p x) (pmfMassNN q x) := by
  rw [realKL, toReal_klDiv_pmf_eq_sum p q
    ((toMeasure_absolutelyContinuous_iff_support_subset p q).2 h)]
  apply Finset.sum_congr rfl
  intro x _
  exact (realKlAtom_pmfMassNN p q x).symm

private theorem real_binaryKl_rhs_eq_sum
    {alpha : Type u}
    [Fintype alpha] [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (t : NNReal) (p1 q1 p2 q2 : PMF alpha)
    (h1 : p1.support ⊆ q1.support)
    (h2 : p2.support ⊆ q2.support) :
    (t : Real) * realKL p1 q1 +
        ((1 - t : NNReal) : Real) * realKL p2 q2 =
      ∑ x : alpha,
        ((t : Real) *
            realKlAtom (pmfMassNN p1 x) (pmfMassNN q1 x) +
          ((1 - t : NNReal) : Real) *
            realKlAtom (pmfMassNN p2 x) (pmfMassNN q2 x)) := by
  rw [realKL_eq_sum_realKlAtom p1 q1 h1,
    realKL_eq_sum_realKlAtom p2 q2 h2,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]

private theorem real_binaryKl_eq_iff_cross
    {alpha : Type u}
    [Finite alpha] [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (t : NNReal) (ht : t <= 1) (ht0 : 0 < t) (ht1 : t < 1)
    (p1 q1 p2 q2 : PMF alpha)
    (h1 : p1.support ⊆ q1.support)
    (h2 : p2.support ⊆ q2.support) :
    (realKL (PMF.binaryMixture t ht p1 p2)
          (PMF.binaryMixture t ht q1 q2) =
        (t : Real) * realKL p1 q1 +
          ((1 - t : NNReal) : Real) * realKL p2 q2) ↔
      ∀ x, p1 x * q2 x = p2 x * q1 x := by
  classical
  let := Fintype.ofFinite alpha
  have hmix :
      (PMF.binaryMixture t ht p1 p2).support ⊆
        (PMF.binaryMixture t ht q1 q2).support :=
    binaryMixture_support_subset t ht p1 q1 p2 q2 h1 h2
  rw [realKL_eq_sum_realKlAtom
      (PMF.binaryMixture t ht p1 p2)
      (PMF.binaryMixture t ht q1 q2) hmix,
    real_binaryKl_rhs_eq_sum t p1 q1 p2 q2 h1 h2]
  simp_rw [pmfMassNN_binaryMixture]
  have h1atom :
      ∀ x, pmfMassNN p1 x ≠ 0 -> pmfMassNN q1 x ≠ 0 := by
    intro x hp
    rw [pmfMassNN_ne_zero_iff] at hp ⊢
    exact (q1.mem_support_iff x).1
      (h1 ((p1.mem_support_iff x).2 hp))
  have h2atom :
      ∀ x, pmfMassNN p2 x ≠ 0 -> pmfMassNN q2 x ≠ 0 := by
    intro x hp
    rw [pmfMassNN_ne_zero_iff] at hp ⊢
    exact (q2.mem_support_iff x).1
      (h2 ((p2.mem_support_iff x).2 hp))
  let lhsAtom : alpha -> Real := fun x =>
    realKlAtom
      (mixedMass t (pmfMassNN p1 x) (pmfMassNN p2 x))
      (mixedMass t (pmfMassNN q1 x) (pmfMassNN q2 x))
  let rhsAtom : alpha -> Real := fun x =>
    (t : Real) * realKlAtom (pmfMassNN p1 x) (pmfMassNN q1 x) +
      ((1 - t : NNReal) : Real) *
        realKlAtom (pmfMassNN p2 x) (pmfMassNN q2 x)
  change ((∑ x, lhsAtom x) = ∑ x, rhsAtom x) ↔ _
  have hle : ∀ x, lhsAtom x <= rhsAtom x := by
    intro x
    exact real_binary_logSum_le t
      (pmfMassNN p1 x) (pmfMassNN q1 x)
      (pmfMassNN p2 x) (pmfMassNN q2 x)
      ht0 ht1 (h1atom x) (h2atom x)
  constructor
  · intro hsum x
    have hnonneg :
        ∀ y ∈ (Finset.univ : Finset alpha),
          0 <= rhsAtom y - lhsAtom y := by
      intro y _
      exact sub_nonneg.2 (hle y)
    have hgapSum :
        ∑ y : alpha, (rhsAtom y - lhsAtom y) = 0 := by
      rw [Finset.sum_sub_distrib, hsum, sub_self]
    have hgap :=
      (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hgapSum
        x (Finset.mem_univ x)
    have hatom : lhsAtom x = rhsAtom x := by
      linarith
    have hcrossNN :=
      (real_binary_logSum_eq_iff_cross t
        (pmfMassNN p1 x) (pmfMassNN q1 x)
        (pmfMassNN p2 x) (pmfMassNN q2 x)
        ht0 ht1 (h1atom x) (h2atom x)).1 hatom
    exact (pmfMassNN_cross_iff p1 q1 p2 q2 x).1 hcrossNN
  · intro hcross
    apply Finset.sum_congr rfl
    intro x _
    exact (real_binary_logSum_eq_iff_cross t
      (pmfMassNN p1 x) (pmfMassNN q1 x)
      (pmfMassNN p2 x) (pmfMassNN q2 x)
      ht0 ht1 (h1atom x) (h2atom x)).2
        ((pmfMassNN_cross_iff p1 q1 p2 q2 x).2 (hcross x))

private theorem ennreal_binaryKl_eq_iff_cross
    {alpha : Type u}
    [Finite alpha] [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (t : NNReal) (ht : t <= 1) (ht0 : 0 < t) (ht1 : t < 1)
    (p1 q1 p2 q2 : PMF alpha)
    (h1 : p1.support ⊆ q1.support)
    (h2 : p2.support ⊆ q2.support) :
    (InformationTheory.klDiv
          (PMF.binaryMixture t ht p1 p2).toMeasure
          (PMF.binaryMixture t ht q1 q2).toMeasure =
        (t : ENNReal) *
            InformationTheory.klDiv p1.toMeasure q1.toMeasure +
          ((1 - t : NNReal) : ENNReal) *
            InformationTheory.klDiv p2.toMeasure q2.toMeasure) ↔
      ∀ x, p1 x * q2 x = p2 x * q1 x := by
  classical
  let := Fintype.ofFinite alpha
  have hmixSupport :
      (PMF.binaryMixture t ht p1 p2).support ⊆
        (PMF.binaryMixture t ht q1 q2).support :=
    binaryMixture_support_subset t ht p1 q1 p2 q2 h1 h2
  have hmixNe :
      InformationTheory.klDiv
          (PMF.binaryMixture t ht p1 p2).toMeasure
          (PMF.binaryMixture t ht q1 q2).toMeasure ≠ ⊤ :=
    (klDiv_pmf_ne_top_iff_support_subset
      (PMF.binaryMixture t ht p1 p2)
      (PMF.binaryMixture t ht q1 q2)).2 hmixSupport
  have h1Ne :
      InformationTheory.klDiv p1.toMeasure q1.toMeasure ≠ ⊤ :=
    (klDiv_pmf_ne_top_iff_support_subset p1 q1).2 h1
  have h2Ne :
      InformationTheory.klDiv p2.toMeasure q2.toMeasure ≠ ⊤ :=
    (klDiv_pmf_ne_top_iff_support_subset p2 q2).2 h2
  have hterm1Ne :
      (t : ENNReal) *
          InformationTheory.klDiv p1.toMeasure q1.toMeasure ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top h1Ne
  have hterm2Ne :
      ((1 - t : NNReal) : ENNReal) *
          InformationTheory.klDiv p2.toMeasure q2.toMeasure ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.coe_ne_top h2Ne
  have hrhsNe :
      (t : ENNReal) *
            InformationTheory.klDiv p1.toMeasure q1.toMeasure +
          ((1 - t : NNReal) : ENNReal) *
            InformationTheory.klDiv p2.toMeasure q2.toMeasure ≠ ⊤ :=
    ENNReal.add_ne_top.2 ⟨hterm1Ne, hterm2Ne⟩
  rw [← ENNReal.toReal_eq_toReal_iff' hmixNe hrhsNe]
  rw [ENNReal.toReal_add hterm1Ne hterm2Ne,
    ENNReal.toReal_mul, ENNReal.toReal_mul,
    ENNReal.coe_toReal, ENNReal.coe_toReal]
  exact real_binaryKl_eq_iff_cross
    t ht ht0 ht1 p1 q1 p2 q2 h1 h2

/-! ### Binary equality characterizations -/

/--
Equality in binary KL joint convexity for an interior weight.

The component support assumptions exclude infinite component divergences.
Under those guards, equality holds exactly when the two component likelihood
ratios agree pointwise, expressed without division by the cross-product law.
When both reference masses at an atom are positive, the cross-product law is
the usual equality of likelihood ratios. If one reference mass vanishes,
support inclusion forces its corresponding numerator mass to vanish, so the
division-free statement handles the absent component without assigning a
meaning to `0 / 0`.
-/
theorem klDiv_binaryMixture_eq_iff
    {alpha : Type u} [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (t : NNReal) (ht : t <= 1) (ht0 : 0 < t) (ht1 : t < 1)
    (p1 p2 q1 q2 : PMF alpha)
    (hfirst : p1.support ⊆ q1.support)
    (hsecond : p2.support ⊆ q2.support) :
    (InformationTheory.klDiv
          (PMF.binaryMixture t ht p1 p2).toMeasure
          (PMF.binaryMixture t ht q1 q2).toMeasure =
        (t : ENNReal) *
            InformationTheory.klDiv p1.toMeasure q1.toMeasure +
          ((1 - t : NNReal) : ENNReal) *
            InformationTheory.klDiv p2.toMeasure q2.toMeasure) ↔
      ∀ x, p1 x * q2 x = p2 x * q1 x := by
  classical
  let := Fintype.ofFinite alpha
  exact ennreal_binaryKl_eq_iff_cross
    t ht ht0 ht1 p1 q1 p2 q2 hfirst hsecond

/--
Real-valued equality in binary KL joint convexity for an interior weight.

The same component support assumptions make every KL divergence finite, so
the exact cross-product characterization is preserved by `ENNReal.toReal`.
The division-free condition has the same null-mass interpretation as the
canonical `ENNReal` theorem: a component absent at an atom contributes matching
zero numerator and reference masses rather than an artificial likelihood
ratio.
-/
theorem toReal_klDiv_binaryMixture_eq_iff
    {alpha : Type u} [Finite alpha]
    [MeasurableSpace alpha] [MeasurableSingletonClass alpha]
    (t : NNReal) (ht : t <= 1) (ht0 : 0 < t) (ht1 : t < 1)
    (p1 p2 q1 q2 : PMF alpha)
    (hfirst : p1.support ⊆ q1.support)
    (hsecond : p2.support ⊆ q2.support) :
    ((InformationTheory.klDiv
          (PMF.binaryMixture t ht p1 p2).toMeasure
          (PMF.binaryMixture t ht q1 q2).toMeasure).toReal =
        (t : Real) *
            (InformationTheory.klDiv p1.toMeasure q1.toMeasure).toReal +
          ((1 - t : NNReal) : Real) *
            (InformationTheory.klDiv p2.toMeasure q2.toMeasure).toReal) ↔
      ∀ x, p1 x * q2 x = p2 x * q1 x := by
  classical
  let := Fintype.ofFinite alpha
  exact real_binaryKl_eq_iff_cross
    t ht ht0 ht1 p1 q1 p2 q2 hfirst hsecond

/-!
## Mutual information under input mixing
-/

private theorem entropy_channelJoint_eq_entropy_add_sum
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (p : PMF alpha) (W : alpha -> PMF beta) :
    entropy (PMF.channelJoint p W) =
      entropy p + ∑ x, (p x).toReal * entropy (W x) := by
  classical
  rw [entropy_eq_sum, entropy_eq_sum]
  calc
    (∑ z : alpha × beta,
        Real.negMulLog ((PMF.channelJoint p W) z).toReal) =
        ∑ x : alpha, ∑ y : beta,
          Real.negMulLog ((PMF.channelJoint p W) (x, y)).toReal := by
      rw [Fintype.sum_prod_type]
    _ = ∑ x : alpha, ∑ y : beta,
          Real.negMulLog ((p x).toReal * (W x y).toReal) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      rw [PMF.channelJoint_apply, ENNReal.toReal_mul]
    _ = ∑ x : alpha,
          (Real.negMulLog (p x).toReal +
            (p x).toReal * entropy (W x)) := by
      apply Finset.sum_congr rfl
      intro x _
      simp_rw [Real.negMulLog_mul]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, PMF.sum_toReal,
        one_mul, ← Finset.mul_sum, ← entropy_eq_sum]
    _ = (∑ x : alpha, Real.negMulLog (p x).toReal) +
          ∑ x : alpha, (p x).toReal * entropy (W x) := by
      rw [Finset.sum_add_distrib]

/--
Mutual information across a finite PMF-valued channel is output entropy minus
the input-weighted entropy of the channel laws.
-/
theorem mutualInfo_channelJoint_eq_entropy_bind_sub_sum
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (p : PMF alpha) (W : alpha -> PMF beta) :
    mutualInfo (PMF.channelJoint p W) =
      entropy (p.bind W) - ∑ x, (p x).toReal * entropy (W x) := by
  rw [mutualInfo_eq]
  change
    entropy ((PMF.channelJoint p W).map Prod.fst) +
          entropy ((PMF.channelJoint p W).map Prod.snd) -
        entropy (PMF.channelJoint p W) =
      entropy (p.bind W) - ∑ x, (p x).toReal * entropy (W x)
  rw [PMF.channelJoint_map_fst, PMF.channelJoint_map_snd,
    entropy_channelJoint_eq_entropy_add_sum]
  ring

private theorem sum_mul_expectation_eq_expectation_bind
    {iota : Type u} {alpha : Type v}
    [Fintype iota] [Fintype alpha]
    (r : PMF iota) (P : iota -> PMF alpha) (f : alpha -> Real) :
    (∑ i, (r i).toReal * ∑ x, (P i x).toReal * f x) =
      ∑ x, ((r.bind P) x).toReal * f x := by
  classical
  calc
    (∑ i, (r i).toReal * ∑ x, (P i x).toReal * f x) =
        ∑ i, ∑ x, (r i).toReal * ((P i x).toReal * f x) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.mul_sum]
    _ = ∑ x, ∑ i, (r i).toReal * ((P i x).toReal * f x) := by
      rw [Finset.sum_comm]
    _ = ∑ x, ((r.bind P) x).toReal * f x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [PMF.bind_toReal_apply r P x, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      ring

/--
For a fixed finite channel, mutual information is concave in the input law
under a common finite PMF-valued selector.
-/
theorem sum_mul_mutualInfo_channelJoint_le
    {iota : Type u} {alpha : Type v} {beta : Type w}
    [Fintype iota] [Fintype alpha] [Fintype beta]
    (r : PMF iota) (P : iota -> PMF alpha)
    (W : alpha -> PMF beta) :
    (∑ i, (r i).toReal * mutualInfo (PMF.channelJoint (P i) W)) <=
      mutualInfo (PMF.channelJoint (r.bind P) W) := by
  have houtput :
      (∑ i, (r i).toReal * entropy ((P i).bind W)) <=
        entropy ((r.bind P).bind W) := by
    rw [PMF.bind_bind]
    exact sum_mul_entropy_le_entropy_bind
      r (fun i => (P i).bind W)
  have hexpect :
      (∑ i, (r i).toReal *
          ∑ x, (P i x).toReal * entropy (W x)) =
        ∑ x, ((r.bind P) x).toReal * entropy (W x) :=
    sum_mul_expectation_eq_expectation_bind r P
      (fun x => entropy (W x))
  calc
    (∑ i, (r i).toReal * mutualInfo (PMF.channelJoint (P i) W)) =
        ∑ i, (r i).toReal *
          (entropy ((P i).bind W) -
            ∑ x, (P i x).toReal * entropy (W x)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [mutualInfo_channelJoint_eq_entropy_bind_sub_sum]
    _ = (∑ i, (r i).toReal * entropy ((P i).bind W)) -
          ∑ i, (r i).toReal *
            ∑ x, (P i x).toReal * entropy (W x) := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
    _ <= entropy ((r.bind P).bind W) -
          ∑ i, (r i).toReal *
            ∑ x, (P i x).toReal * entropy (W x) :=
      sub_le_sub_right houtput _
    _ = entropy ((r.bind P).bind W) -
          ∑ x, ((r.bind P) x).toReal * entropy (W x) := by
      rw [hexpect]
    _ = mutualInfo (PMF.channelJoint (r.bind P) W) :=
      (mutualInfo_channelJoint_eq_entropy_bind_sub_sum
        (r.bind P) W).symm

/--
For a fixed finite channel, mutual information is concave along a binary
mixture of input laws.
-/
theorem mutualInfo_binaryMixture_input_concave
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (t : NNReal) (ht : t <= 1)
    (p q : PMF alpha) (W : alpha -> PMF beta) :
    (t : Real) * mutualInfo (PMF.channelJoint p W) +
        ((1 - t : NNReal) : Real) *
          mutualInfo (PMF.channelJoint q W) <=
      mutualInfo (PMF.channelJoint (PMF.binaryMixture t ht p q) W) := by
  let r : PMF Bool :=
    PMF.ofFintype
      (fun b : Bool => ((cond b t (1 - t) : NNReal) : ENNReal))
      (by simp [ht])
  have hr_true : (r true).toReal = (t : Real) := by
    simp only [r, PMF.ofFintype_apply, Bool.cond_true]
    rw [ENNReal.coe_toReal]
  have hr_false : (r false).toReal = ((1 - t : NNReal) : Real) := by
    simp only [r, PMF.ofFintype_apply, Bool.cond_false]
    rw [ENNReal.coe_toReal]
  change
    (t : Real) * mutualInfo (PMF.channelJoint p W) +
        ((1 - t : NNReal) : Real) * mutualInfo (PMF.channelJoint q W) <=
      mutualInfo (PMF.channelJoint (r.bind fun b => if b then p else q) W)
  simpa only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true,
    Finset.sum_singleton, hr_true, hr_false, ite_true, ite_false] using
    (sum_mul_mutualInfo_channelJoint_le r (fun b => if b then p else q) W)

/-!
## Mutual information under channel mixing
-/

private theorem bind_channelJoint_eq_channelJoint_bind
    {iota : Type u} {alpha : Type v} {beta : Type w}
    [Finite iota]
    (r : PMF iota) (p : PMF alpha)
    (W : iota -> alpha -> PMF beta) :
    r.bind (fun i => PMF.channelJoint p (W i)) =
      PMF.channelJoint p (fun x => r.bind fun i => W i x) := by
  classical
  let := Fintype.ofFinite iota
  apply PMF.ext
  rintro ⟨x, y⟩
  simp only [PMF.bind_apply, tsum_fintype, PMF.channelJoint_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

private theorem bind_channelOutput_eq_channelOutput_bind
    {iota : Type u} {alpha : Type v} {beta : Type w}
    (r : PMF iota) (p : PMF alpha)
    (W : iota -> alpha -> PMF beta) :
    r.bind (fun i => p.bind (W i)) =
      p.bind (fun x => r.bind fun i => W i x) :=
  (PMF.bind_comm p r (fun x i => W i x)).symm

private theorem bind_indepProd_eq_indepProd_bind
    {iota : Type u} {alpha : Type v} {beta : Type w}
    [Finite iota]
    (r : PMF iota) (p : PMF alpha) (Q : iota -> PMF beta) :
    r.bind (fun i => indepProd p (Q i)) =
      indepProd p (r.bind Q) := by
  classical
  let := Fintype.ofFinite iota
  apply PMF.ext
  rintro ⟨x, y⟩
  simp only [PMF.bind_apply, tsum_fintype, indepProd_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ac_rfl

/--
For a fixed finite input law, mutual information is convex under a common
finite PMF-valued selector of channels.
-/
theorem mutualInfo_channelMixture_le_sum
    {iota : Type u} {alpha : Type v} {beta : Type w}
    [Fintype iota] [Fintype alpha] [Fintype beta]
    (r : PMF iota) (p : PMF alpha)
    (W : iota -> alpha -> PMF beta) :
    mutualInfo
        (PMF.channelJoint p (fun x => r.bind fun i => W i x)) <=
      ∑ i, (r i).toReal * mutualInfo (PMF.channelJoint p (W i)) := by
  classical
  let : MeasurableSpace (alpha × beta) := ⊤
  have : MeasurableSingletonClass (alpha × beta) := ⟨fun _ => trivial⟩
  have hsupport :
      ∀ i, r i ≠ 0 ->
        (PMF.channelJoint p (W i)).support ⊆
          (indepProd p (p.bind (W i))).support := by
    intro i _hi
    have hcomponent :=
      (toMeasure_absolutelyContinuous_iff_support_subset
        (PMF.channelJoint p (W i))
        (indepProd
          (fstMarginal (PMF.channelJoint p (W i)))
          (sndMarginal (PMF.channelJoint p (W i))))).1
        (joint_toMeasure_absolutelyContinuous_indepProd_marginals
          (p := PMF.channelJoint p (W i)))
    simpa using hcomponent
  have hbound :=
    toReal_klDiv_bind_le_sum
      r
      (fun i => PMF.channelJoint p (W i))
      (fun i => indepProd p (p.bind (W i)))
      hsupport
  rw [bind_channelJoint_eq_channelJoint_bind,
    bind_indepProd_eq_indepProd_bind,
    bind_channelOutput_eq_channelOutput_bind] at hbound
  have hMIKL (V : alpha -> PMF beta) :
      mutualInfo (PMF.channelJoint p V) =
        (InformationTheory.klDiv
          (PMF.channelJoint p V).toMeasure
          (indepProd p (p.bind V)).toMeasure).toReal := by
    simpa using
      (mutualInfo_eq_toReal_klDiv_joint_indepProd
        (PMF.channelJoint p V))
  calc
    mutualInfo
        (PMF.channelJoint p (fun x => r.bind fun i => W i x)) =
        (InformationTheory.klDiv
          (PMF.channelJoint p
            (fun x => r.bind fun i => W i x)).toMeasure
          (indepProd p
            (p.bind (fun x => r.bind fun i => W i x))).toMeasure).toReal :=
      hMIKL (fun x => r.bind fun i => W i x)
    _ <= ∑ i, (r i).toReal *
        (InformationTheory.klDiv
          (PMF.channelJoint p (W i)).toMeasure
          (indepProd p (p.bind (W i))).toMeasure).toReal :=
      hbound
    _ = ∑ i, (r i).toReal *
        mutualInfo (PMF.channelJoint p (W i)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hMIKL (W i)]

/--
For a fixed finite input law, mutual information is convex along a binary
mixture of channels.
-/
theorem mutualInfo_binaryChannelMixture_le
    {alpha : Type u} {beta : Type v}
    [Fintype alpha] [Fintype beta]
    (t : NNReal) (ht : t <= 1) (p : PMF alpha)
    (W1 W2 : alpha -> PMF beta) :
    mutualInfo
        (PMF.channelJoint p
          (fun x => PMF.binaryMixture t ht (W1 x) (W2 x))) <=
      (t : Real) * mutualInfo (PMF.channelJoint p W1) +
        ((1 - t : NNReal) : Real) *
          mutualInfo (PMF.channelJoint p W2) := by
  let r : PMF Bool :=
    PMF.ofFintype
      (fun b : Bool => ((cond b t (1 - t) : NNReal) : ENNReal))
      (by simp [ht])
  have hr_true : (r true).toReal = (t : Real) := by
    simp only [r, PMF.ofFintype_apply, Bool.cond_true]
    rw [ENNReal.coe_toReal]
  have hr_false : (r false).toReal = ((1 - t : NNReal) : Real) := by
    simp only [r, PMF.ofFintype_apply, Bool.cond_false]
    rw [ENNReal.coe_toReal]
  change
    mutualInfo
        (PMF.channelJoint p
          (fun x => r.bind fun b => if b then W1 x else W2 x)) <=
      (t : Real) * mutualInfo (PMF.channelJoint p W1) +
        ((1 - t : NNReal) : Real) * mutualInfo (PMF.channelJoint p W2)
  simpa only [Fintype.univ_bool, Finset.sum_insert, Finset.mem_singleton,
    Bool.true_eq_false, Bool.false_eq_true, not_false_eq_true,
    Finset.sum_singleton, hr_true, hr_false, ite_true, ite_false] using
    (mutualInfo_channelMixture_le_sum r p
      (fun b x => if b then W1 x else W2 x))

end

end Shannon
end LeanInfoTheory
