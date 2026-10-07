/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Shannon.Entropy
import Tengoku

/-!
# Finite Shannon entropy bounds

This file contains analytic finite-entropy bounds that need heavier convexity
tools than the lightweight entropy definition file. Keeping these theorems here
lets the core finite entropy API remain cheap to import.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators

universe u v

noncomputable section

/--
Finite Shannon entropy is bounded above by the logarithm of the alphabet size.

The proof is Jensen's inequality for the concave function `Real.negMulLog`,
applied with uniform weights over the finite alphabet.
-/
theorem entropy_le_log_card {alpha : Type u} [Fintype alpha] [Nonempty alpha]
    (p : PMF alpha) :
    entropy p <= Real.log (Fintype.card alpha) := by
  classical
  let n : Real := Fintype.card alpha
  have hn_pos : 0 < n := by
    simpa [n] using
      (Nat.cast_pos.mpr (Fintype.card_pos (α := alpha)) :
        (0 : Real) < Fintype.card alpha)
  have hn_nonneg : 0 <= n := hn_pos.le
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  -- The uniform weights `1 / n` over the finite alphabet sum to one.
  have hweights :
      (∑ _a ∈ (Finset.univ : Finset alpha), (1 : Real) / n) = 1 := by
    calc
      (∑ _a ∈ (Finset.univ : Finset alpha), (1 : Real) / n) =
          ((Finset.univ : Finset alpha).card : Real) * (1 / n) := by
        simp [Finset.sum_const, nsmul_eq_mul]
      _ = n * (1 / n) := by
        simp [n]
      _ = 1 := by
        rw [mul_one_div_cancel hn_ne]
  -- Jensen turns the average of `negMulLog (p a)` into `negMulLog` of the average mass.
  have hJ :
      (∑ a ∈ (Finset.univ : Finset alpha),
          ((1 : Real) / n) • Real.negMulLog (p a).toReal) <=
        Real.negMulLog
          (∑ a ∈ (Finset.univ : Finset alpha), ((1 : Real) / n) • (p a).toReal) := by
    exact
      Real.concaveOn_negMulLog.le_map_sum
        (t := (Finset.univ : Finset alpha))
        (w := fun _ => (1 : Real) / n)
        (p := fun a => (p a).toReal)
        (fun _ _ => div_nonneg zero_le_one hn_nonneg)
        hweights
        (fun a _ => PMF.toReal_nonneg p a)
  -- The left side of Jensen is `(1 / n) * H(p)`.
  have hleft :
      (∑ a ∈ (Finset.univ : Finset alpha),
          ((1 : Real) / n) • Real.negMulLog (p a).toReal) =
        (1 / n) * entropy p := by
    calc
      (∑ a ∈ (Finset.univ : Finset alpha),
          ((1 : Real) / n) • Real.negMulLog (p a).toReal) =
          ∑ a ∈ (Finset.univ : Finset alpha),
            (1 / n) * Real.negMulLog (p a).toReal := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [smul_eq_mul]
      _ = (1 / n) * ∑ a ∈ (Finset.univ : Finset alpha),
          Real.negMulLog (p a).toReal := by
        rw [Finset.mul_sum]
      _ = (1 / n) * entropy p := by
        rw [entropy_eq_sum]
  -- The Jensen center point is the average of the masses, namely `1 / n`.
  have hright :
      (∑ a ∈ (Finset.univ : Finset alpha), ((1 : Real) / n) • (p a).toReal) =
        1 / n := by
    calc
      (∑ a ∈ (Finset.univ : Finset alpha), ((1 : Real) / n) • (p a).toReal) =
          ∑ a ∈ (Finset.univ : Finset alpha), (1 / n) * (p a).toReal := by
        apply Finset.sum_congr rfl
        intro a _ha
        rw [smul_eq_mul]
      _ = (1 / n) * ∑ a ∈ (Finset.univ : Finset alpha), (p a).toReal := by
        rw [Finset.mul_sum]
      _ = 1 / n := by
        rw [PMF.sum_toReal p, mul_one]
  -- Combining the previous two rewrites gives `(1 / n) * H(p) <= negMulLog (1 / n)`.
  have hJ' : (1 / n) * entropy p <= Real.negMulLog (1 / n) := by
    calc
      (1 / n) * entropy p =
          (∑ a ∈ (Finset.univ : Finset alpha),
            ((1 : Real) / n) • Real.negMulLog (p a).toReal) := hleft.symm
      _ <= Real.negMulLog
          (∑ a ∈ (Finset.univ : Finset alpha), ((1 : Real) / n) • (p a).toReal) := hJ
      _ = Real.negMulLog (1 / n) := by
        rw [hright]
  -- Multiply by the alphabet size and simplify `n * negMulLog (1 / n)` to `log n`.
  calc
    entropy p = n * ((1 / n) * entropy p) := by
      symm
      rw [← mul_assoc, mul_one_div_cancel hn_ne, one_mul]
    _ <= n * Real.negMulLog (1 / n) :=
      mul_le_mul_of_nonneg_left hJ' hn_nonneg
    _ = Real.log (Fintype.card alpha) := by
      have hlog : Real.log (1 / n) = -Real.log n := by
        rw [div_eq_mul_inv, one_mul, Real.log_inv]
      rw [Real.negMulLog, hlog]
      change n * (-(1 / n) * -Real.log n) = Real.log n
      calc
        n * (-(1 / n) * -Real.log n) = n * ((1 / n) * Real.log n) := by
          ring
        _ = (n * (1 / n)) * Real.log n := by
          ring
        _ = Real.log n := by
          rw [mul_one_div_cancel hn_ne, one_mul]

private def supportPMF {alpha : Type u} [Fintype alpha]
    (p : PMF alpha) : PMF p.supportFinset := by
  classical
  apply PMF.ofFintype (fun a : p.supportFinset => p a.1)
  have hsupportSum :
      (∑ a : p.supportFinset, p a.1) =
        ∑ a ∈ p.supportFinset, p a := by
    rw [Finset.univ_eq_attach]
    exact Finset.sum_attach p.supportFinset (fun a => p a)
  have hsum_all : (∑ a : alpha, p a) = 1 := by
    simpa using p.tsum_coe
  calc
    (∑ a : p.supportFinset, p a.1) =
        ∑ a ∈ p.supportFinset, p a := hsupportSum
    _ = ∑ a : alpha, p a := by
      apply Finset.sum_subset
      · intro a ha
        simp at ha ⊢
      · intro a _ha hnot
        have ha_not_support : a ∉ p.support := by
          intro ha
          exact hnot ((PMF.mem_supportFinset p a).2 ha)
        rw [(p.apply_eq_zero_iff a).2 ha_not_support]
    _ = 1 := hsum_all

private theorem entropy_supportPMF {alpha : Type u} [Fintype alpha]
    (p : PMF alpha) : entropy (supportPMF p) = entropy p := by
  classical
  rw [entropy_eq_sum, entropy_eq_sum]
  have hsupportSum :
      (∑ a : p.supportFinset, Real.negMulLog (p a.1).toReal) =
      ∑ a ∈ p.supportFinset, Real.negMulLog (p a).toReal := by
    rw [Finset.univ_eq_attach]
    exact
      Finset.sum_attach p.supportFinset
        (fun a => Real.negMulLog (p a).toReal)
  calc
    (∑ a : p.supportFinset,
        Real.negMulLog (supportPMF p a).toReal) =
        ∑ a : p.supportFinset, Real.negMulLog (p a.1).toReal := by
      rfl
    _ = ∑ a ∈ p.supportFinset,
          Real.negMulLog (p a).toReal := hsupportSum
    _ = ∑ a : alpha, Real.negMulLog (p a).toReal := by
      apply Finset.sum_subset
      · intro a ha
        simp at ha ⊢
      · intro a _ha hnot
        have ha_not_support : a ∉ p.support := by
          intro ha
          exact hnot ((PMF.mem_supportFinset p a).2 ha)
        rw [(p.apply_eq_zero_iff a).2 ha_not_support]
        simp

/--
Finite Shannon entropy is bounded by the logarithm of the number of atoms with
nonzero mass.

Unlike `entropy_le_log_card`, this theorem counts only the PMF support and does
not require a separate nonempty-alphabet instance.
-/
theorem entropy_le_log_support_ncard {alpha : Type u} [Fintype alpha]
    (p : PMF alpha) :
    entropy p <= Real.log (p.support.ncard : Real) := by
  classical
  let : Nonempty p.supportFinset := by
    obtain ⟨a, ha⟩ := p.supportFinset_nonempty
    exact ⟨⟨a, ha⟩⟩
  have h := entropy_le_log_card (supportPMF p)
  rw [entropy_supportPMF, Fintype.card_coe, PMF.supportFinset_card] at h
  exact h

/--
The entropy of a finite-valued random variable is bounded by the logarithm of
the support size of its pushforward law.
-/
theorem entropyOf_le_log_support_ncard
    {omega : Type u} {alpha : Type v} [Fintype alpha]
    (p : PMF omega) (X : omega -> alpha) :
    entropyOf p X <= Real.log ((p.map X).support.ncard : Real) := by
  simpa [entropyOf] using entropy_le_log_support_ncard (p.map X)

/--
The uniform distribution reaches the finite entropy upper bound.

Mathematically, this is the equality case `H(U_alpha) = log |alpha|` for the
uniform law on a nonempty finite alphabet.
-/
theorem entropy_uniformOfFintype {alpha : Type u} [Fintype alpha] [Nonempty alpha] :
    entropy (PMF.uniformOfFintype alpha) = Real.log (Fintype.card alpha) := by
  classical
  let n : Real := Fintype.card alpha
  have hn_pos : 0 < n := by
    simpa [n] using
      (Nat.cast_pos.mpr (Fintype.card_pos (α := alpha)) :
        (0 : Real) < Fintype.card alpha)
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  -- Every atom of the uniform law has real mass `1 / n`.
  have hmass (a : alpha) : (PMF.uniformOfFintype alpha a).toReal = 1 / n := by
    rw [PMF.uniformOfFintype_apply]
    simp [n]
  rw [entropy_eq_sum]
  calc
    (∑ a, Real.negMulLog (PMF.uniformOfFintype alpha a).toReal) =
        ∑ _a : alpha, Real.negMulLog (1 / n) := by
      apply Finset.sum_congr rfl
      intro a _ha
      rw [hmass a]
    _ = n * Real.negMulLog (1 / n) := by
      rw [Finset.sum_const, Finset.card_univ]
      simp [n, nsmul_eq_mul]
    _ = Real.log (Fintype.card alpha) := by
      have hlog : Real.log (1 / n) = -Real.log n := by
        rw [div_eq_mul_inv, one_mul, Real.log_inv]
      rw [Real.negMulLog, hlog]
      change n * (-(1 / n) * -Real.log n) = Real.log n
      calc
        n * (-(1 / n) * -Real.log n) = n * ((1 / n) * Real.log n) := by
          ring
        _ = (n * (1 / n)) * Real.log n := by
          ring
        _ = Real.log n := by
          rw [mul_one_div_cancel hn_ne, one_mul]

/--
Finite Shannon entropy reaches the alphabet-cardinality bound exactly at the
uniform distribution.
-/
theorem entropy_eq_log_card_iff_eq_uniformOfFintype
    {alpha : Type u} [Fintype alpha] [Nonempty alpha] (p : PMF alpha) :
    entropy p = Real.log (Fintype.card alpha) ↔
      p = PMF.uniformOfFintype alpha := by
  classical
  constructor
  · intro hp
    let n : Real := Fintype.card alpha
    have hn_pos : 0 < n := by
      simpa [n] using
        (Nat.cast_pos.mpr (Fintype.card_pos (α := alpha)) :
          (0 : Real) < Fintype.card alpha)
    have hweights :
        (∑ _a ∈ (Finset.univ : Finset alpha), (1 : Real) / n) = 1 := by
      calc
        (∑ _a ∈ (Finset.univ : Finset alpha), (1 : Real) / n) =
            ((Finset.univ : Finset alpha).card : Real) * (1 / n) := by
          simp [Finset.sum_const, nsmul_eq_mul]
        _ = n * (1 / n) := by simp [n]
        _ = 1 := by rw [mul_one_div_cancel (ne_of_gt hn_pos)]
    have hleft :
        (∑ a ∈ (Finset.univ : Finset alpha),
            ((1 : Real) / n) • Real.negMulLog (p a).toReal) =
          (1 / n) * entropy p := by
      calc
        (∑ a ∈ (Finset.univ : Finset alpha),
            ((1 : Real) / n) • Real.negMulLog (p a).toReal) =
            ∑ a ∈ (Finset.univ : Finset alpha),
              (1 / n) * Real.negMulLog (p a).toReal := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [smul_eq_mul]
        _ = (1 / n) * ∑ a ∈ (Finset.univ : Finset alpha),
            Real.negMulLog (p a).toReal := by
          rw [Finset.mul_sum]
        _ = (1 / n) * entropy p := by rw [entropy_eq_sum]
    have hright :
        (∑ a ∈ (Finset.univ : Finset alpha),
            ((1 : Real) / n) • (p a).toReal) = 1 / n := by
      calc
        (∑ a ∈ (Finset.univ : Finset alpha),
            ((1 : Real) / n) • (p a).toReal) =
            ∑ a ∈ (Finset.univ : Finset alpha), (1 / n) * (p a).toReal := by
          apply Finset.sum_congr rfl
          intro a _ha
          rw [smul_eq_mul]
        _ = (1 / n) * ∑ a ∈ (Finset.univ : Finset alpha), (p a).toReal := by
          rw [Finset.mul_sum]
        _ = 1 / n := by rw [PMF.sum_toReal p, mul_one]
    have hlog : Real.log (1 / n) = -Real.log n := by
      rw [div_eq_mul_inv, one_mul, Real.log_inv]
    have hneg : Real.negMulLog (1 / n) = (1 / n) * Real.log n := by
      rw [Real.negMulLog, hlog]
      ring
    have hp' : entropy p = Real.log n := by simpa [n] using hp
    have hJ_eq :
        Real.negMulLog
            (∑ a ∈ (Finset.univ : Finset alpha),
              ((1 : Real) / n) • (p a).toReal) =
          ∑ a ∈ (Finset.univ : Finset alpha),
            ((1 : Real) / n) • Real.negMulLog (p a).toReal := by
      rw [hright, hleft, hp', hneg]
    have hconst :=
      (Real.strictConcaveOn_negMulLog.map_sum_eq_iff
        (t := (Finset.univ : Finset alpha))
        (w := fun _ => (1 : Real) / n)
        (p := fun a => (p a).toReal)
        (fun _ _ => div_pos zero_lt_one hn_pos)
        hweights
        (fun a _ => PMF.toReal_nonneg p a)).1 hJ_eq
    apply PMF.ext
    intro a
    apply
      (ENNReal.toReal_eq_toReal_iff'
        (p.apply_ne_top a)
        ((PMF.uniformOfFintype alpha).apply_ne_top a)).1
    have hpReal := hconst a (Finset.mem_univ a)
    rw [hright] at hpReal
    rw [hpReal, PMF.uniformOfFintype_apply]
    simp [n]
  · rintro rfl
    exact entropy_uniformOfFintype

private theorem entropy_uniformOfFinset {alpha : Type u} [Fintype alpha]
    (s : Finset alpha) (hs : s.Nonempty) :
    entropy (PMF.uniformOfFinset s hs) = Real.log (s.card : Real) := by
  classical
  let n : Real := s.card
  have hn_pos : 0 < n := by
    simpa [n] using (Nat.cast_pos.mpr hs.card_pos : (0 : Real) < s.card)
  have hn_ne : n ≠ 0 := ne_of_gt hn_pos
  have hmass {a : alpha} (ha : a ∈ s) :
      (PMF.uniformOfFinset s hs a).toReal = 1 / n := by
    rw [PMF.uniformOfFinset_apply_of_mem hs ha]
    simp [n]
  rw [entropy_eq_sum]
  calc
    (∑ a : alpha, Real.negMulLog (PMF.uniformOfFinset s hs a).toReal) =
        ∑ a ∈ s, Real.negMulLog (PMF.uniformOfFinset s hs a).toReal := by
      symm
      apply Finset.sum_subset
      · simp
      · intro a _ha hnot
        rw [PMF.uniformOfFinset_apply_of_notMem hs hnot]
        simp
    _ = ∑ _a ∈ s, Real.negMulLog (1 / n) := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [hmass ha]
    _ = n * Real.negMulLog (1 / n) := by
      rw [Finset.sum_const]
      simp [n, nsmul_eq_mul]
    _ = Real.log (s.card : Real) := by
      have hlog : Real.log (1 / n) = -Real.log n := by
        rw [div_eq_mul_inv, one_mul, Real.log_inv]
      rw [Real.negMulLog, hlog]
      change n * (-(1 / n) * -Real.log n) = Real.log n
      calc
        n * (-(1 / n) * -Real.log n) = n * ((1 / n) * Real.log n) := by ring
        _ = (n * (1 / n)) * Real.log n := by ring
        _ = Real.log n := by rw [mul_one_div_cancel hn_ne, one_mul]

/--
Finite Shannon entropy reaches its support-cardinality bound exactly when the
distribution is uniform on its support.
-/
theorem entropy_eq_log_support_ncard_iff_eq_uniformOnSupport
    {alpha : Type u} [Fintype alpha] (p : PMF alpha) :
    entropy p = Real.log (p.support.ncard : Real) ↔
      p = PMF.uniformOfFinset p.supportFinset p.supportFinset_nonempty := by
  classical
  let : Nonempty p.supportFinset := by
    obtain ⟨a, ha⟩ := p.supportFinset_nonempty
    exact ⟨⟨a, ha⟩⟩
  constructor
  · intro hp
    have hrestricted :
        entropy (supportPMF p) =
          Real.log (Fintype.card p.supportFinset : Real) := by
      rw [entropy_supportPMF, Fintype.card_coe, PMF.supportFinset_card]
      exact hp
    have hu :=
      (entropy_eq_log_card_iff_eq_uniformOfFintype (supportPMF p)).1 hrestricted
    apply PMF.ext
    intro a
    by_cases ha : a ∈ p.supportFinset
    · calc
        p a = supportPMF p ⟨a, ha⟩ := rfl
        _ = PMF.uniformOfFintype p.supportFinset ⟨a, ha⟩ := by rw [hu]
        _ = (p.supportFinset.card : ENNReal)⁻¹ := by
          simp only [PMF.uniformOfFintype_apply, Fintype.card_coe]
        _ = PMF.uniformOfFinset p.supportFinset p.supportFinset_nonempty a := by
          symm
          exact PMF.uniformOfFinset_apply_of_mem p.supportFinset_nonempty ha
    · have ha_not_support : a ∉ p.support := by simpa using ha
      rw [(p.apply_eq_zero_iff a).2 ha_not_support]
      symm
      exact PMF.uniformOfFinset_apply_of_notMem p.supportFinset_nonempty ha
  · intro hp
    calc
      entropy p =
          entropy (PMF.uniformOfFinset p.supportFinset p.supportFinset_nonempty) :=
        congrArg entropy hp
      _ = Real.log (p.supportFinset.card : Real) :=
        entropy_uniformOfFinset p.supportFinset p.supportFinset_nonempty
      _ = Real.log (p.support.ncard : Real) := by
        rw [PMF.supportFinset_card]

/--
A finite-valued random variable reaches the alphabet-cardinality entropy bound
exactly when its law is uniform on the alphabet.
-/
theorem entropyOf_eq_log_card_iff_map_eq_uniformOfFintype
    {omega : Type u} {alpha : Type v} [Fintype alpha] [Nonempty alpha]
    (p : PMF omega) (X : omega → alpha) :
    entropyOf p X = Real.log (Fintype.card alpha) ↔
      p.map X = PMF.uniformOfFintype alpha := by
  simpa [entropyOf] using
    entropy_eq_log_card_iff_eq_uniformOfFintype (p.map X)

/--
A finite-valued random variable reaches its law-support entropy bound exactly
when that law is uniform on its support.
-/
theorem entropyOf_eq_log_support_ncard_iff_map_eq_uniformOnSupport
    {omega : Type u} {alpha : Type v} [Fintype alpha]
    (p : PMF omega) (X : omega → alpha) :
    entropyOf p X = Real.log ((p.map X).support.ncard : Real) ↔
      p.map X = PMF.uniformOfFinset (p.map X).supportFinset
        (p.map X).supportFinset_nonempty := by
  simpa [entropyOf] using
    entropy_eq_log_support_ncard_iff_eq_uniformOnSupport (p.map X)

end

end Shannon
end LeanInfoTheory
