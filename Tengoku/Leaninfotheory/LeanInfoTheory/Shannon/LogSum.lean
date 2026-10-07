/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku

/-!
# Finite log-sum inequality

This opt-in scalar module develops the finite log-sum inequality independently
of probability-mass functions and Shannon information measures.
-/

namespace LeanInfoTheory
namespace Shannon

open scoped BigOperators ENNReal

noncomputable section

universe u

/-! ## Guarded Real proof infrastructure -/

/--
Guarded Real log-sum inequality used internally to construct the later
zero-safe extended-valued API.

The support guard permits selected `(0, 0)` pairs. It excludes only a positive
numerator over a zero denominator.
-/
private theorem real_logSum_inequality_aux
    {ι : Type u} (s : Finset ι) (a b : ι → NNReal)
    (h_support : ∀ i ∈ s, a i ≠ 0 → b i ≠ 0) :
    ((∑ i ∈ s, a i : NNReal) : Real) *
        Real.log
          (((∑ i ∈ s, a i : NNReal) : Real) /
            ((∑ i ∈ s, b i : NNReal) : Real))
      ≤ ∑ i ∈ s,
          (a i : Real) * Real.log ((a i : Real) / (b i : Real)) := by
  classical
  by_cases hBzero : (∑ i ∈ s, b i) = 0
  · have hb_zero : ∀ i ∈ s, b i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 hBzero
    have ha_zero : ∀ i ∈ s, a i = 0 := by
      intro i hi
      by_contra hai
      exact (h_support i hi hai) (hb_zero i hi)
    have hAzero : (∑ i ∈ s, a i) = 0 :=
      Finset.sum_eq_zero fun i hi => ha_zero i hi
    have hterms :
        (∑ i ∈ s,
          (a i : Real) * Real.log ((a i : Real) / (b i : Real))) = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [ha_zero i hi]
    rw [hAzero, hBzero, hterms]
    simp
  · have ha_zero : ∀ i ∈ s, b i = 0 → a i = 0 := by
      intro i hi hbi
      by_contra hai
      exact (h_support i hi hai) hbi
    let t := s.filter fun i => b i ≠ 0
    have ht_subset : t ⊆ s := Finset.filter_subset _ _
    have hb_t : ∀ i ∈ t, b i ≠ 0 := by
      intro i hi
      exact (Finset.mem_filter.1 hi).2
    have hsum_a :
        (∑ i ∈ s, a i) = ∑ i ∈ t, a i := by
      symm
      apply Finset.sum_subset ht_subset
      intro i hi hi_not
      have hbi : b i = 0 := by
        by_contra hbi
        exact hi_not (Finset.mem_filter.2 ⟨hi, hbi⟩)
      exact ha_zero i hi hbi
    have hsum_b :
        (∑ i ∈ s, b i) = ∑ i ∈ t, b i := by
      symm
      apply Finset.sum_subset ht_subset
      intro i hi hi_not
      by_contra hbi
      exact hi_not (Finset.mem_filter.2 ⟨hi, hbi⟩)
    have hsum_terms :
        (∑ i ∈ s,
          (a i : Real) * Real.log ((a i : Real) / (b i : Real))) =
        ∑ i ∈ t,
          (a i : Real) * Real.log ((a i : Real) / (b i : Real)) := by
      symm
      apply Finset.sum_subset ht_subset
      intro i hi hi_not
      have hbi : b i = 0 := by
        by_contra hbi
        exact hi_not (Finset.mem_filter.2 ⟨hi, hbi⟩)
      simp [ha_zero i hi hbi]
    have ht_nonempty : t.Nonempty := by
      rcases t.eq_empty_or_nonempty with ht_empty | ht_nonempty
      · exfalso
        apply hBzero
        rw [hsum_b, ht_empty]
        simp
      · exact ht_nonempty
    let B : Real := ∑ i ∈ t, (b i : Real)
    have hBpos : 0 < B := by
      dsimp [B]
      exact Finset.sum_pos
        (fun i hi => by
          exact_mod_cast (pos_iff_ne_zero.2 (hb_t i hi) : 0 < b i))
        ht_nonempty
    have hw_nonneg : ∀ i ∈ t, 0 ≤ (b i : Real) / B := by
      intro i hi
      exact div_nonneg (by positivity) hBpos.le
    have hw_sum : ∑ i ∈ t, (b i : Real) / B = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      change B * B⁻¹ = 1
      exact mul_inv_cancel₀ hBpos.ne'
    have hx_nonneg :
        ∀ i ∈ t, (a i : Real) / (b i : Real) ∈ Set.Ici (0 : Real) := by
      intro i hi
      have hbi : 0 < (b i : Real) := by
        exact_mod_cast (pos_iff_ne_zero.2 (hb_t i hi) : 0 < b i)
      exact div_nonneg (by positivity) hbi.le
    have hcenter :
        (∑ i ∈ t,
            (b i : Real) / B * ((a i : Real) / (b i : Real))) =
          (∑ i ∈ t, (a i : Real)) / B := by
      calc
        (∑ i ∈ t,
            (b i : Real) / B * ((a i : Real) / (b i : Real))) =
            ∑ i ∈ t, (a i : Real) / B := by
              apply Finset.sum_congr rfl
              intro i hi
              have hbi : (b i : Real) ≠ 0 := by
                exact_mod_cast hb_t i hi
              field_simp [hBpos.ne', hbi]
        _ = (∑ i ∈ t, (a i : Real)) / B := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    have hright :
        B * (∑ i ∈ t,
          (b i : Real) / B *
            (((a i : Real) / (b i : Real)) *
              Real.log ((a i : Real) / (b i : Real)))) =
          ∑ i ∈ t,
            (a i : Real) * Real.log ((a i : Real) / (b i : Real)) := by
      calc
        B * (∑ i ∈ t,
          (b i : Real) / B *
            (((a i : Real) / (b i : Real)) *
              Real.log ((a i : Real) / (b i : Real)))) =
            ∑ i ∈ t, B *
              ((b i : Real) / B *
                (((a i : Real) / (b i : Real)) *
                  Real.log ((a i : Real) / (b i : Real)))) := by
                    rw [Finset.mul_sum]
        _ = ∑ i ∈ t,
            (a i : Real) * Real.log ((a i : Real) / (b i : Real)) := by
              apply Finset.sum_congr rfl
              intro i hi
              have hbi : (b i : Real) ≠ 0 := by
                exact_mod_cast hb_t i hi
              field_simp [hBpos.ne', hbi]
    have hleft :
        B * (((∑ i ∈ t, (a i : Real)) / B) *
          Real.log ((∑ i ∈ t, (a i : Real)) / B)) =
          (∑ i ∈ t, (a i : Real)) *
            Real.log ((∑ i ∈ t, (a i : Real)) / B) := by
      field_simp [hBpos.ne']
    have hJensen := Real.convexOn_mul_log.map_sum_le
      (t := t)
      (w := fun i => (b i : Real) / B)
      (p := fun i => (a i : Real) / (b i : Real))
      hw_nonneg hw_sum hx_nonneg
    simp only [smul_eq_mul] at hJensen
    rw [hcenter] at hJensen
    have hscaled := mul_le_mul_of_nonneg_left hJensen hBpos.le
    rw [hleft, hright] at hscaled
    rw [hsum_a, hsum_b, hsum_terms]
    simpa [B] using hscaled

/--
Equality in the guarded Real log-sum inequality holds exactly when all active
selected pairs have one common finite numerator-to-denominator ratio.

Selected `(0, 0)` pairs are inactive and impose no condition.
-/
private theorem real_logSum_eq_iff_exists_constant_ratio_aux
    {ι : Type u} (s : Finset ι) (a b : ι → NNReal)
    (h_support : ∀ i ∈ s, a i ≠ 0 → b i ≠ 0) :
    (((∑ i ∈ s, a i : NNReal) : Real) *
          Real.log
            (((∑ i ∈ s, a i : NNReal) : Real) /
              ((∑ i ∈ s, b i : NNReal) : Real)) =
        ∑ i ∈ s,
          (a i : Real) * Real.log ((a i : Real) / (b i : Real))) ↔
      ∃ c : Real, ∀ i ∈ s, (a i ≠ 0 ∨ b i ≠ 0) →
        (a i : Real) / (b i : Real) = c := by
  classical
  by_cases hBzero : (∑ i ∈ s, b i) = 0
  · have hb_zero : ∀ i ∈ s, b i = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 hBzero
    have ha_zero : ∀ i ∈ s, a i = 0 := by
      intro i hi
      by_contra hai
      exact (h_support i hi hai) (hb_zero i hi)
    have hAzero : (∑ i ∈ s, a i) = 0 :=
      Finset.sum_eq_zero fun i hi => ha_zero i hi
    have hterms :
        (∑ i ∈ s,
          (a i : Real) * Real.log ((a i : Real) / (b i : Real))) = 0 :=
      Finset.sum_eq_zero fun i hi => by simp [ha_zero i hi]
    constructor
    · intro _
      refine ⟨0, ?_⟩
      intro i hi _
      simp [ha_zero i hi, hb_zero i hi]
    · intro _
      rw [hAzero, hBzero, hterms]
      simp
  · have ha_zero : ∀ i ∈ s, b i = 0 → a i = 0 := by
      intro i hi hbi
      by_contra hai
      exact (h_support i hi hai) hbi
    let B : Real := ∑ i ∈ s, (b i : Real)
    have hBpos : 0 < B := by
      have hBpos_nn : 0 < ∑ i ∈ s, b i := pos_iff_ne_zero.2 hBzero
      dsimp [B]
      exact_mod_cast hBpos_nn
    have hw_nonneg : ∀ i ∈ s, 0 ≤ (b i : Real) / B := by
      intro i hi
      exact div_nonneg (by positivity) hBpos.le
    have hw_sum : ∑ i ∈ s, (b i : Real) / B = 1 := by
      simp_rw [div_eq_mul_inv]
      rw [← Finset.sum_mul]
      change B * B⁻¹ = 1
      exact mul_inv_cancel₀ hBpos.ne'
    have hx_nonneg :
        ∀ i ∈ s, (a i : Real) / (b i : Real) ∈ Set.Ici (0 : Real) := by
      intro i hi
      change (0 : Real) ≤ (a i : Real) / (b i : Real)
      exact div_nonneg (NNReal.coe_nonneg _) (NNReal.coe_nonneg _)
    have hcenter :
        (∑ i ∈ s,
            (b i : Real) / B * ((a i : Real) / (b i : Real))) =
          (∑ i ∈ s, (a i : Real)) / B := by
      calc
        (∑ i ∈ s,
            (b i : Real) / B * ((a i : Real) / (b i : Real))) =
            ∑ i ∈ s, (a i : Real) / B := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hbi : b i = 0
              · simp [hbi, ha_zero i hi hbi]
              · have hbi_real : (b i : Real) ≠ 0 := by
                  exact_mod_cast hbi
                field_simp [hBpos.ne', hbi_real]
        _ = (∑ i ∈ s, (a i : Real)) / B := by
          simp_rw [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    have hright :
        B * (∑ i ∈ s,
          (b i : Real) / B *
            (((a i : Real) / (b i : Real)) *
              Real.log ((a i : Real) / (b i : Real)))) =
          ∑ i ∈ s,
            (a i : Real) * Real.log ((a i : Real) / (b i : Real)) := by
      calc
        B * (∑ i ∈ s,
          (b i : Real) / B *
            (((a i : Real) / (b i : Real)) *
              Real.log ((a i : Real) / (b i : Real)))) =
            ∑ i ∈ s, B *
              ((b i : Real) / B *
                (((a i : Real) / (b i : Real)) *
                  Real.log ((a i : Real) / (b i : Real)))) := by
                    rw [Finset.mul_sum]
        _ = ∑ i ∈ s,
            (a i : Real) * Real.log ((a i : Real) / (b i : Real)) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hbi : b i = 0
              · simp [hbi, ha_zero i hi hbi]
              · have hbi_real : (b i : Real) ≠ 0 := by
                  exact_mod_cast hbi
                field_simp [hBpos.ne', hbi_real]
    have hleft :
        B * (((∑ i ∈ s, (a i : Real)) / B) *
          Real.log ((∑ i ∈ s, (a i : Real)) / B)) =
          (∑ i ∈ s, (a i : Real)) *
            Real.log ((∑ i ∈ s, (a i : Real)) / B) := by
      field_simp [hBpos.ne']
    have hscale :
        ((∑ i ∈ s, (a i : Real)) *
              Real.log ((∑ i ∈ s, (a i : Real)) / B) =
            ∑ i ∈ s,
              (a i : Real) * Real.log ((a i : Real) / (b i : Real))) ↔
          ((∑ i ∈ s, (a i : Real)) / B) *
                Real.log ((∑ i ∈ s, (a i : Real)) / B) =
            ∑ i ∈ s,
              (b i : Real) / B *
                (((a i : Real) / (b i : Real)) *
                  Real.log ((a i : Real) / (b i : Real))) := by
      constructor
      · intro h
        apply (mul_left_cancel₀ hBpos.ne')
        rw [hleft, hright, h]
      · intro h
        calc
          (∑ i ∈ s, (a i : Real)) *
                Real.log ((∑ i ∈ s, (a i : Real)) / B) =
              B * (((∑ i ∈ s, (a i : Real)) / B) *
                Real.log ((∑ i ∈ s, (a i : Real)) / B)) := hleft.symm
          _ = B * (∑ i ∈ s,
                (b i : Real) / B *
                  (((a i : Real) / (b i : Real)) *
                    Real.log ((a i : Real) / (b i : Real)))) :=
              congrArg (B * ·) h
          _ = ∑ i ∈ s,
                (a i : Real) * Real.log ((a i : Real) / (b i : Real)) :=
              hright
    have hJensen := Real.strictConvexOn_mul_log.map_sum_eq_iff'
      (t := s)
      (w := fun i => (b i : Real) / B)
      (p := fun i => (a i : Real) / (b i : Real))
      hw_nonneg hw_sum hx_nonneg
    simp only [smul_eq_mul] at hJensen
    rw [hcenter] at hJensen
    have hReal :
        (((∑ i ∈ s, (a i : Real)) *
              Real.log ((∑ i ∈ s, (a i : Real)) / B) =
            ∑ i ∈ s,
              (a i : Real) * Real.log ((a i : Real) / (b i : Real)))) ↔
          ∃ c : Real, ∀ i ∈ s, (a i ≠ 0 ∨ b i ≠ 0) →
            (a i : Real) / (b i : Real) = c := by
      rw [hscale, hJensen]
      constructor
      · intro h
        refine ⟨(∑ i ∈ s, (a i : Real)) / B, ?_⟩
        intro i hi hactive
        have hbi : b i ≠ 0 := by
          rcases hactive with hai | hbi
          · exact h_support i hi hai
          · exact hbi
        have hbi_real : (b i : Real) ≠ 0 := by
          exact_mod_cast hbi
        exact h i hi (div_ne_zero hbi_real hBpos.ne')
      · rintro ⟨c, hc⟩
        have hcenter_c : (∑ i ∈ s, (a i : Real)) / B = c := by
          rw [← hcenter]
          calc
            (∑ i ∈ s,
                (b i : Real) / B * ((a i : Real) / (b i : Real))) =
                ∑ i ∈ s, (b i : Real) / B * c := by
                  apply Finset.sum_congr rfl
                  intro i hi
                  by_cases hbi : b i = 0
                  · simp [hbi]
                  · rw [hc i hi (Or.inr hbi)]
            _ = (∑ i ∈ s, (b i : Real) / B) * c := by
                  rw [Finset.sum_mul]
            _ = c := by rw [hw_sum, one_mul]
        intro i hi hweight
        have hbi : b i ≠ 0 := by
          intro hbi
          exact hweight (by simp [hbi])
        exact (hc i hi (Or.inr hbi)).trans hcenter_c.symm
    simpa [B] using hReal

/-! ## Extended log-sum terms -/

/--
The zero-safe extended-real scalar term in the finite log-sum inequality.

The conventions are `0 * log (0 / b) = 0` for every `b`, including `b = 0`,
and `a * log (a / 0) = top` when `a` is positive.
-/
def logSumTerm (a b : NNReal) : EReal :=
  ((a : ENNReal) : EReal) *
    ENNReal.log ((a : ENNReal) / (b : ENNReal))

/-- A zero numerator contributes zero to the extended log-sum. -/
theorem logSumTerm_zero_left (b : NNReal) :
    logSumTerm 0 b = 0 := by
  simp [logSumTerm]

/-- A positive numerator over a zero denominator contributes `top`. -/
theorem logSumTerm_pos_zero {a : NNReal} (ha : a ≠ 0) :
    logSumTerm a 0 = ⊤ := by
  have ha' : (a : ENNReal) ≠ 0 := ENNReal.coe_ne_zero.mpr ha
  have hdiv : (a : ENNReal) / (0 : ENNReal) = ⊤ :=
    ENNReal.div_eq_top.2 (Or.inl ⟨ha', rfl⟩)
  rw [logSumTerm]
  simp only [ENNReal.coe_zero]
  rw [hdiv, ENNReal.log_top]
  exact EReal.coe_ennreal_mul_top ha'

/-- An extended log-sum term is never `bottom`. -/
theorem logSumTerm_ne_bot (a b : NNReal) :
    logSumTerm a b ≠ ⊥ := by
  rw [logSumTerm, EReal.mul_ne_bot]
  refine ⟨Or.inl (EReal.coe_ennreal_ne_bot _), ?_,
    Or.inl (EReal.coe_nnreal_ne_top a), Or.inl (EReal.coe_ennreal_nonneg _)⟩
  by_cases ha : a = 0
  · left
    simp [ha]
  · right
    have hratio :
        (a : ENNReal) / (b : ENNReal) ≠ 0 :=
      ENNReal.div_ne_zero.2 ⟨ENNReal.coe_ne_zero.mpr ha, ENNReal.coe_ne_top⟩
    intro hlog
    exact hratio (ENNReal.log_eq_bot_iff.1 hlog)

/-- Every finite selected sum of extended log-sum terms is never `bottom`. -/
theorem sum_logSumTerm_ne_bot {ι : Type u}
    (s : Finset ι) (a b : ι → NNReal) :
    (∑ i ∈ s, logSumTerm (a i) (b i)) ≠ ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact EReal.add_ne_bot_iff.2 ⟨logSumTerm_ne_bot _ _, ih⟩

private theorem logSumTerm_eq_coe_real_aux
    {a b : NNReal} (hb : b ≠ 0) :
    logSumTerm a b =
      (((a : Real) * Real.log ((a : Real) / (b : Real)) : Real) : EReal) := by
  by_cases ha : a = 0
  · simp [ha, logSumTerm_zero_left]
  · have hab : a / b ≠ 0 := div_ne_zero ha hb
    rw [logSumTerm, ← ENNReal.coe_div hb, ENNReal.log_of_nnreal hab,
      EReal.coe_nnreal_eq_coe_real, ← EReal.coe_mul]
    norm_cast

private theorem sum_logSumTerm_eq_coe_real_of_support_aux
    {ι : Type u} (s : Finset ι) (a b : ι → NNReal)
    (h_support : ∀ i ∈ s, a i ≠ 0 → b i ≠ 0) :
    (∑ i ∈ s, logSumTerm (a i) (b i)) =
      (((∑ i ∈ s,
          (a i : Real) *
            Real.log ((a i : Real) / (b i : Real))) : Real) : EReal) := by
  classical
  have hcoe_sum (t : Finset ι) (f : ι → Real) :
      (∑ i ∈ t, (f i : EReal)) =
        (((∑ i ∈ t, f i) : Real) : EReal) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
        rw [Finset.sum_insert hi, Finset.sum_insert hi, EReal.coe_add, ih]
  calc
    (∑ i ∈ s, logSumTerm (a i) (b i)) =
        ∑ i ∈ s,
          (((a i : Real) *
            Real.log ((a i : Real) / (b i : Real)) : Real) : EReal) := by
              apply Finset.sum_congr rfl
              intro i hi
              by_cases hbi : b i = 0
              · have hai : a i = 0 := by
                  by_contra hai
                  exact (h_support i hi hai) hbi
                simp [hai, hbi, logSumTerm_zero_left]
              · exact logSumTerm_eq_coe_real_aux hbi
    _ = (((∑ i ∈ s,
          (a i : Real) *
            Real.log ((a i : Real) / (b i : Real))) : Real) : EReal) :=
      hcoe_sum s fun i =>
        (a i : Real) * Real.log ((a i : Real) / (b i : Real))

private theorem sum_logSumTerm_eq_top_of_exists_pos_zero_aux
    {ι : Type u} (s : Finset ι) (a b : ι → NNReal)
    (h : ∃ i ∈ s, a i ≠ 0 ∧ b i = 0) :
    (∑ i ∈ s, logSumTerm (a i) (b i)) = ⊤ := by
  classical
  obtain ⟨i, hi, hai, hbi⟩ := h
  rw [← Finset.add_sum_erase s (fun j => logSumTerm (a j) (b j)) hi,
    hbi, logSumTerm_pos_zero hai]
  exact EReal.top_add_of_ne_bot
    (sum_logSumTerm_ne_bot (s.erase i) a b)

/--
Finite log-sum inequality with the zero-safe conventions of `logSumTerm`.

In particular, a selected positive numerator over a zero denominator makes the
right-hand side `top`; no support or positivity guard is required.
-/
theorem logSum_inequality {ι : Type u}
    (s : Finset ι) (a b : ι → NNReal) :
    logSumTerm (∑ i ∈ s, a i) (∑ i ∈ s, b i) ≤
      ∑ i ∈ s, logSumTerm (a i) (b i) := by
  classical
  by_cases hbad : ∃ i ∈ s, a i ≠ 0 ∧ b i = 0
  · rw [sum_logSumTerm_eq_top_of_exists_pos_zero_aux s a b hbad]
    exact le_top
  · have h_support : ∀ i ∈ s, a i ≠ 0 → b i ≠ 0 := by
      intro i hi hai hbi
      exact hbad ⟨i, hi, hai, hbi⟩
    by_cases hBzero : (∑ i ∈ s, b i) = 0
    · have hb_zero : ∀ i ∈ s, b i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 hBzero
      have ha_zero : ∀ i ∈ s, a i = 0 := by
        intro i hi
        by_contra hai
        exact (h_support i hi hai) (hb_zero i hi)
      have hAzero : (∑ i ∈ s, a i) = 0 :=
        Finset.sum_eq_zero fun i hi => ha_zero i hi
      have hterms :
          (∑ i ∈ s, logSumTerm (a i) (b i)) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [ha_zero i hi, logSumTerm_zero_left]
      rw [hAzero, hBzero, logSumTerm_zero_left, hterms]
    · have haggregate :
          logSumTerm (∑ i ∈ s, a i) (∑ i ∈ s, b i) =
            ((((∑ i ∈ s, a i : NNReal) : Real) *
                Real.log
                  (((∑ i ∈ s, a i : NNReal) : Real) /
                    ((∑ i ∈ s, b i : NNReal) : Real)) : Real) : EReal) :=
        logSumTerm_eq_coe_real_aux hBzero
      rw [haggregate,
        sum_logSumTerm_eq_coe_real_of_support_aux s a b h_support]
      exact EReal.coe_le_coe
        (real_logSum_inequality_aux s a b h_support)

private theorem ennreal_ratio_eq_iff_real_ratio_eq_aux
    {a b c d : NNReal} (hb : b ≠ 0) (hd : d ≠ 0) :
    ((a : ENNReal) / (b : ENNReal) =
        (c : ENNReal) / (d : ENNReal)) ↔
      (a : Real) / (b : Real) = (c : Real) / (d : Real) := by
  rw [← ENNReal.coe_div hb, ← ENNReal.coe_div hd]
  norm_cast

/--
Equality in the zero-safe finite log-sum inequality.

Equality holds exactly when all active selected pairs have one common
`ENNReal` numerator-to-denominator ratio. Selected `(0, 0)` pairs are inactive;
the common ratio may be finite or `top`.
-/
theorem logSum_eq_iff_exists_constant_ratio {ι : Type u}
    (s : Finset ι) (a b : ι → NNReal) :
    (logSumTerm (∑ i ∈ s, a i) (∑ i ∈ s, b i) =
        ∑ i ∈ s, logSumTerm (a i) (b i)) ↔
      ∃ c : ENNReal, ∀ i ∈ s, (a i ≠ 0 ∨ b i ≠ 0) →
        (a i : ENNReal) / (b i : ENNReal) = c := by
  classical
  by_cases htop : ∃ i ∈ s, a i ≠ 0 ∧ b i = 0
  · obtain ⟨i₀, hi₀, hai₀, hbi₀⟩ := htop
    have htop' : ∃ i ∈ s, a i ≠ 0 ∧ b i = 0 :=
      ⟨i₀, hi₀, hai₀, hbi₀⟩
    have hratio₀ :
        (a i₀ : ENNReal) / (b i₀ : ENNReal) = ⊤ := by
      rw [show (b i₀ : ENNReal) = 0 by exact_mod_cast hbi₀,
        ENNReal.div_zero (by exact_mod_cast hai₀)]
    have hApos : 0 < ∑ i ∈ s, a i := by
      exact Finset.sum_pos'
        (fun i _ => by positivity) ⟨i₀, hi₀, pos_iff_ne_zero.2 hai₀⟩
    constructor
    · intro hEq
      have hleft_top :
          logSumTerm (∑ i ∈ s, a i) (∑ i ∈ s, b i) = ⊤ :=
        hEq.trans
          (sum_logSumTerm_eq_top_of_exists_pos_zero_aux s a b htop')
      have hb_zero : ∀ i ∈ s, b i = 0 := by
        intro i hi
        by_contra hbi
        have hBpos : 0 < ∑ j ∈ s, b j := by
          exact Finset.sum_pos'
            (fun j _ => by positivity) ⟨i, hi, pos_iff_ne_zero.2 hbi⟩
        rw [logSumTerm_eq_coe_real_aux hBpos.ne'] at hleft_top
        exact EReal.coe_ne_top _ hleft_top
      refine ⟨⊤, ?_⟩
      intro i hi hactive
      have hbi : b i = 0 := hb_zero i hi
      have hai : a i ≠ 0 := by
        rcases hactive with hai | hbi'
        · exact hai
        · exact False.elim (hbi' hbi)
      rw [show (b i : ENNReal) = 0 by exact_mod_cast hbi,
        ENNReal.div_zero (by exact_mod_cast hai)]
    · rintro ⟨c, hc⟩
      have hc_top : c = ⊤ :=
        (hc i₀ hi₀ (Or.inl hai₀)).symm.trans hratio₀
      have hb_zero : ∀ i ∈ s, b i = 0 := by
        intro i hi
        by_contra hbi
        have hratio_ne_top :
            (a i : ENNReal) / (b i : ENNReal) ≠ ⊤ :=
          ENNReal.div_ne_top ENNReal.coe_ne_top (by exact_mod_cast hbi)
        exact hratio_ne_top ((hc i hi (Or.inr hbi)).trans hc_top)
      have hBzero : (∑ i ∈ s, b i) = 0 :=
        Finset.sum_eq_zero fun i hi => hb_zero i hi
      rw [hBzero, logSumTerm_pos_zero hApos.ne',
        sum_logSumTerm_eq_top_of_exists_pos_zero_aux s a b htop']
  · have h_support : ∀ i ∈ s, a i ≠ 0 → b i ≠ 0 := by
      intro i hi hai hbi
      exact htop ⟨i, hi, hai, hbi⟩
    by_cases hBzero : (∑ i ∈ s, b i) = 0
    · have hb_zero : ∀ i ∈ s, b i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 hBzero
      have ha_zero : ∀ i ∈ s, a i = 0 := by
        intro i hi
        by_contra hai
        exact (h_support i hi hai) (hb_zero i hi)
      have hAzero : (∑ i ∈ s, a i) = 0 :=
        Finset.sum_eq_zero fun i hi => ha_zero i hi
      have hterms :
          (∑ i ∈ s, logSumTerm (a i) (b i)) = 0 :=
        Finset.sum_eq_zero fun i hi => by
          rw [ha_zero i hi, logSumTerm_zero_left]
      constructor
      · intro _
        refine ⟨0, ?_⟩
        intro i hi hactive
        exact False.elim <| hactive.elim
          (fun hai => hai (ha_zero i hi))
          (fun hbi => hbi (hb_zero i hi))
      · intro _
        rw [hAzero, hBzero, logSumTerm_zero_left, hterms]
    · obtain ⟨i₀, hi₀, hbi₀⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero hBzero
      have haggregate :
          logSumTerm (∑ i ∈ s, a i) (∑ i ∈ s, b i) =
            ((((∑ i ∈ s, a i : NNReal) : Real) *
                Real.log
                  (((∑ i ∈ s, a i : NNReal) : Real) /
                    ((∑ i ∈ s, b i : NNReal) : Real)) : Real) : EReal) :=
        logSumTerm_eq_coe_real_aux hBzero
      constructor
      · intro hEq
        rw [haggregate,
          sum_logSumTerm_eq_coe_real_of_support_aux s a b h_support] at hEq
        have hRealEq :
            ((∑ i ∈ s, a i : NNReal) : Real) *
                  Real.log
                    (((∑ i ∈ s, a i : NNReal) : Real) /
                      ((∑ i ∈ s, b i : NNReal) : Real)) =
                ∑ i ∈ s,
                  (a i : Real) *
                    Real.log ((a i : Real) / (b i : Real)) :=
          EReal.coe_injective hEq
        obtain ⟨c, hc⟩ :=
          (real_logSum_eq_iff_exists_constant_ratio_aux
            s a b h_support).1 hRealEq
        refine ⟨(a i₀ : ENNReal) / (b i₀ : ENNReal), ?_⟩
        intro i hi hactive
        have hbi : b i ≠ 0 :=
          hactive.elim (fun hai => h_support i hi hai) (fun hbi => hbi)
        exact (ennreal_ratio_eq_iff_real_ratio_eq_aux hbi hbi₀).2
          ((hc i hi hactive).trans
            (hc i₀ hi₀ (Or.inr hbi₀)).symm)
      · rintro ⟨c, hc⟩
        have hRealRatio :
            ∀ i ∈ s, (a i ≠ 0 ∨ b i ≠ 0) →
              (a i : Real) / (b i : Real) =
                (a i₀ : Real) / (b i₀ : Real) := by
          intro i hi hactive
          have hbi : b i ≠ 0 :=
            hactive.elim (fun hai => h_support i hi hai) (fun hbi => hbi)
          have hratio :
              (a i : ENNReal) / (b i : ENNReal) =
                (a i₀ : ENNReal) / (b i₀ : ENNReal) :=
            (hc i hi hactive).trans
              (hc i₀ hi₀ (Or.inr hbi₀)).symm
          exact (ennreal_ratio_eq_iff_real_ratio_eq_aux hbi hbi₀).1 hratio
        have hRealEq :
            ((∑ i ∈ s, a i : NNReal) : Real) *
                  Real.log
                    (((∑ i ∈ s, a i : NNReal) : Real) /
                      ((∑ i ∈ s, b i : NNReal) : Real)) =
                ∑ i ∈ s,
                  (a i : Real) *
                    Real.log ((a i : Real) / (b i : Real)) :=
          (real_logSum_eq_iff_exists_constant_ratio_aux
            s a b h_support).2
              ⟨(a i₀ : Real) / (b i₀ : Real), hRealRatio⟩
        rw [haggregate,
          sum_logSumTerm_eq_coe_real_of_support_aux s a b h_support]
        exact congrArg Real.toEReal hRealEq

/--
Guarded Real finite log-sum inequality.

The support guard excludes positive-over-zero selected pairs while permitting
selected `(0, 0)` pairs.
-/
theorem real_logSum_inequality_of_support {ι : Type u}
    (s : Finset ι) (a b : ι → NNReal)
    (h_support : ∀ i ∈ s, a i ≠ 0 → b i ≠ 0) :
    ((∑ i ∈ s, a i : NNReal) : Real) *
        Real.log
          (((∑ i ∈ s, a i : NNReal) : Real) /
            ((∑ i ∈ s, b i : NNReal) : Real))
      ≤ ∑ i ∈ s,
          (a i : Real) * Real.log ((a i : Real) / (b i : Real)) :=
  real_logSum_inequality_aux s a b h_support

/--
Equality in the guarded Real finite log-sum inequality holds exactly when all
active selected pairs have one common finite ratio.
-/
theorem real_logSum_eq_iff_exists_constant_ratio_of_support
    {ι : Type u} (s : Finset ι) (a b : ι → NNReal)
    (h_support : ∀ i ∈ s, a i ≠ 0 → b i ≠ 0) :
    (((∑ i ∈ s, a i : NNReal) : Real) *
          Real.log
            (((∑ i ∈ s, a i : NNReal) : Real) /
              ((∑ i ∈ s, b i : NNReal) : Real)) =
        ∑ i ∈ s,
          (a i : Real) * Real.log ((a i : Real) / (b i : Real))) ↔
      ∃ c : Real, ∀ i ∈ s, (a i ≠ 0 ∨ b i ≠ 0) →
        (a i : Real) / (b i : Real) = c :=
  real_logSum_eq_iff_exists_constant_ratio_aux s a b h_support

end

end Shannon
end LeanInfoTheory
