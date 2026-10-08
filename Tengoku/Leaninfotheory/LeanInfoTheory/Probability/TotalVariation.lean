/-
Copyright © 2026 ECOLE POLYTECHNIQUE FEDERALE DE LAUSANNE (EPFL),
Switzerland, Mathematics of Information Laboratory (MIL).
All rights reserved.

Licensed under the Apache License, Version 2.0.
See the LICENSE file for details.

Author: Serhat Emre Coban
-/

import Tengoku.Leaninfotheory.LeanInfoTheory.Probability.Finite
import Tengoku

/-!
# Total variation of finite PMFs

`PMF.totalVariation` uses the probability convention: one half of the sum of
absolute differences of real atom masses. Its values lie in `[0, 1]`; it is
symmetric, separates PMFs, and satisfies the triangle inequality. The event where
the first law has at least as much mass explicitly attains both the signed and
absolute greatest event discrepancy. Common minimum and residual mass formulas
hold in both real and ENNReal form; distance one characterizes disjoint supports.
Bounded tests have sharp interval-width and signed-radius bounds; explicit
indicator and sign tests attain the two greatest absolute discrepancies. Applying
a common channel or deterministic map cannot increase TV; equivalence relabeling
preserves it exactly.

The probability laws remain mathlib's `PMF`s. No support or inhabitedness
assumption is imposed, and no metric instance or additional simp rule is added.
This finite algebraic API is independent of the project's Shannon and KL layers.

The normalization agrees with Levin--Peres, Sections 4.1--4.2, and
Polyanskiy--Wu (2024), Section 7.3. The finite event interface uses existing
outer-measure probabilities without measurability assumptions. The overlap and
residual totals supply normalization identities without constructing normalized
laws. Test functions use explicit real weighted sums, without an expectation
object or a strict-width premise. Contraction uses finite real-mass sums and
normalized channel rows, without a channel-layer or semantic DPI dependency.
-/

namespace PMF

universe u

open scoped BigOperators

variable {α : Type u} [Fintype α]

/-- Total variation of finite PMFs, normalized as half the L1 distance of real masses. -/
noncomputable def totalVariation (p q : PMF α) : ℝ :=
  (1 / 2 : ℝ) * ∑ a, |(p a).toReal - (q a).toReal|

/-- Total variation is nonnegative. -/
theorem totalVariation_nonneg (p q : PMF α) : 0 ≤ totalVariation p q := by
  unfold totalVariation
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg fun _ _ => abs_nonneg _)

/-- Total variation of probability laws is at most one. -/
theorem totalVariation_le_one (p q : PMF α) : totalVariation p q ≤ 1 := by
  have hs : (∑ a, |(p a).toReal - (q a).toReal|) ≤
      ∑ a, ((p a).toReal + (q a).toReal) := by
    apply Finset.sum_le_sum
    intro a _
    simpa only [sub_zero, zero_sub, abs_neg,
      abs_of_nonneg (PMF.toReal_nonneg p a),
      abs_of_nonneg (PMF.toReal_nonneg q a)] using
      abs_sub_le (p a).toReal 0 (q a).toReal
  rw [Finset.sum_add_distrib, PMF.sum_toReal, PMF.sum_toReal] at hs
  unfold totalVariation
  linarith

/-- A PMF has zero total variation from itself. -/
theorem totalVariation_self (p : PMF α) : totalVariation p p = 0 := by
  simp [totalVariation]

/-- Total variation is symmetric in its two PMFs. -/
theorem totalVariation_comm (p q : PMF α) : totalVariation p q = totalVariation q p := by
  unfold totalVariation
  congr 1
  exact Finset.sum_congr rfl fun _ _ => abs_sub_comm _ _

/-- Two finite PMFs have zero total variation exactly when they are equal. -/
theorem totalVariation_eq_zero_iff (p q : PMF α) : totalVariation p q = 0 ↔ p = q := by
  classical
  constructor
  · intro h
    have hs : (∑ a, |(p a).toReal - (q a).toReal|) = 0 := by
      unfold totalVariation at h
      linarith
    apply PMF.ext
    intro a
    have ha := (Finset.sum_eq_zero_iff_of_nonneg
      (fun a _ => abs_nonneg ((p a).toReal - (q a).toReal))).1 hs a (Finset.mem_univ a)
    exact (ENNReal.toReal_eq_toReal_iff' (p.apply_ne_top a) (q.apply_ne_top a)).1
      (sub_eq_zero.mp (abs_eq_zero.mp ha))
  · rintro rfl
    exact totalVariation_self p

/-- Total variation satisfies the triangle inequality. -/
theorem totalVariation_triangle (p q r : PMF α) :
    totalVariation p r ≤ totalVariation p q + totalVariation q r := by
  have hs : (∑ a, |(p a).toReal - (r a).toReal|) ≤
      ∑ a, (|(p a).toReal - (q a).toReal| + |(q a).toReal - (r a).toReal|) := by
    exact Finset.sum_le_sum fun a _ => abs_sub_le (p a).toReal (q a).toReal (r a).toReal
  rw [Finset.sum_add_distrib] at hs
  unfold totalVariation
  linarith

/-- On a finite type, event probability is the sum of the real masses in the event. -/
theorem toOuterMeasure_toReal_eq_sum (p : PMF α) (s : Set α) :
    (p.toOuterMeasure s).toReal = ∑ a, s.indicator (fun a => (p a).toReal) a := by
  classical
  rw [p.toOuterMeasure_apply_fintype, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ∈ s <;> simp [ha]
  · intro a _
    by_cases ha : a ∈ s <;> simp [ha, p.apply_ne_top a]

/-- Total variation is the total excess mass where the first law dominates the second. -/
theorem totalVariation_eq_sum_pos (p q : PMF α) :
    totalVariation p q =
      ∑ a ∈ Finset.univ.filter (fun a => (q a).toReal ≤ (p a).toReal),
        ((p a).toReal - (q a).toReal) := by
  have hzero : (∑ a, ((p a).toReal - (q a).toReal)) = 0 := by
    rw [Finset.sum_sub_distrib, p.sum_toReal, q.sum_toReal, sub_self]
  have hpoint (a : α) : |(p a).toReal - (q a).toReal| =
      2 * (if (q a).toReal ≤ (p a).toReal then (p a).toReal - (q a).toReal else 0) -
        ((p a).toReal - (q a).toReal) := by
    split_ifs with h
    · rw [abs_of_nonneg (sub_nonneg.mpr h)]
      linarith
    · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge h))]
      linarith
  have hsum := Finset.sum_congr (s₁ := Finset.univ) rfl (fun a _ => hpoint a)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hzero, sub_zero] at hsum
  rw [totalVariation, Finset.sum_filter]
  linarith

private theorem toOuterMeasure_sub_le_totalVariation (p q : PMF α) (s : Set α) :
    (p.toOuterMeasure s).toReal - (q.toOuterMeasure s).toReal ≤ totalVariation p q := by
  classical
  rw [p.toOuterMeasure_toReal_eq_sum, q.toOuterMeasure_toReal_eq_sum,
    ← Finset.sum_sub_distrib, totalVariation_eq_sum_pos, Finset.sum_filter]
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ s
  · simp only [Set.indicator_of_mem ha]
    split_ifs with h
    · exact le_rfl
    · exact sub_nonpos.mpr (le_of_not_ge h)
  · simp only [Set.indicator_of_notMem ha, sub_self]
    split_ifs with h
    · exact sub_nonneg.mpr h
    · exact le_rfl

/-- The discrepancy of any event is bounded by total variation. -/
theorem abs_toOuterMeasure_sub_le_totalVariation (p q : PMF α) (s : Set α) :
    |(p.toOuterMeasure s).toReal - (q.toOuterMeasure s).toReal| ≤ totalVariation p q := by
  apply abs_le.mpr
  constructor
  · have h := toOuterMeasure_sub_le_totalVariation q p s
    rw [totalVariation_comm q p] at h
    linarith
  · exact toOuterMeasure_sub_le_totalVariation p q s

/-- The event where the first law has at least as much mass attains total variation. -/
theorem totalVariation_eq_toOuterMeasure_sub (p q : PMF α) :
    totalVariation p q =
      (p.toOuterMeasure {a | (q a).toReal ≤ (p a).toReal}).toReal -
        (q.toOuterMeasure {a | (q a).toReal ≤ (p a).toReal}).toReal := by
  classical
  rw [p.toOuterMeasure_toReal_eq_sum, q.toOuterMeasure_toReal_eq_sum,
    ← Finset.sum_sub_distrib, totalVariation_eq_sum_pos, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  by_cases h : (q a).toReal ≤ (p a).toReal <;> simp [h]

/-- Total variation is the greatest signed discrepancy among all events. -/
theorem totalVariation_isGreatest_event (p q : PMF α) :
    IsGreatest (Set.range (fun s : Set α =>
      (p.toOuterMeasure s).toReal - (q.toOuterMeasure s).toReal)) (totalVariation p q) := by
  constructor
  · exact ⟨{a | (q a).toReal ≤ (p a).toReal}, (totalVariation_eq_toOuterMeasure_sub p q).symm⟩
  · rintro _ ⟨s, rfl⟩
    exact toOuterMeasure_sub_le_totalVariation p q s

/-- Total variation is the greatest absolute discrepancy among all events. -/
theorem totalVariation_isGreatest_abs_event (p q : PMF α) :
    IsGreatest (Set.range (fun s : Set α =>
      |(p.toOuterMeasure s).toReal - (q.toOuterMeasure s).toReal|)) (totalVariation p q) := by
  constructor
  · refine ⟨{a | (q a).toReal ≤ (p a).toReal}, ?_⟩
    change |(p.toOuterMeasure {a | (q a).toReal ≤ (p a).toReal}).toReal -
      (q.toOuterMeasure {a | (q a).toReal ≤ (p a).toReal}).toReal| = totalVariation p q
    rw [← totalVariation_eq_toOuterMeasure_sub, abs_of_nonneg (totalVariation_nonneg p q)]
  · rintro _ ⟨s, rfl⟩
    exact abs_toOuterMeasure_sub_le_totalVariation p q s

/-- Total variation is the first law's mass remaining after removing the common minimum. -/
theorem totalVariation_eq_sum_sub_min (p q : PMF α) :
    totalVariation p q = ∑ a, ((p a).toReal - min (p a).toReal (q a).toReal) := by
  rw [totalVariation_eq_sum_pos, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs with h
  · rw [min_eq_right h]
  · rw [min_eq_left (le_of_not_ge h), sub_self]

/-- Total variation is one minus the common mass of the two finite laws. -/
theorem totalVariation_eq_one_sub_sum_min (p q : PMF α) :
    totalVariation p q = 1 - ∑ a, min (p a).toReal (q a).toReal := by
  rw [totalVariation_eq_sum_sub_min, Finset.sum_sub_distrib, p.sum_toReal]

/-- The ENNReal common mass is the finite overlap complement of total variation. -/
theorem sum_min_eq_ofReal_one_sub_totalVariation (p q : PMF α) :
    (∑ a, min (p a) (q a)) = ENNReal.ofReal (1 - totalVariation p q) := by
  have h : 1 - totalVariation p q = ∑ a, min (p a).toReal (q a).toReal := by
    rw [totalVariation_eq_one_sub_sum_min]
    linarith
  rw [h, ENNReal.ofReal_sum_of_nonneg
    (fun a _ => le_min (p.toReal_nonneg a) (q.toReal_nonneg a))]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.ofReal_min, ENNReal.ofReal_toReal (p.apply_ne_top a),
    ENNReal.ofReal_toReal (q.apply_ne_top a)]

/-- Total variation is the ENNReal total of the first law's truncated excess masses. -/
theorem ofReal_totalVariation_eq_sum_sub (p q : PMF α) :
    ENNReal.ofReal (totalVariation p q) = ∑ a, (p a - q a) := by
  rw [totalVariation_eq_sum_sub_min,
    ENNReal.ofReal_sum_of_nonneg (fun a _ => sub_nonneg.mpr (min_le_left _ _))]
  apply Finset.sum_congr rfl
  intro a _
  rw [ENNReal.ofReal_sub _ (le_min (p.toReal_nonneg a) (q.toReal_nonneg a)),
    ENNReal.ofReal_min, ENNReal.ofReal_toReal (p.apply_ne_top a),
    ENNReal.ofReal_toReal (q.apply_ne_top a), tsub_min]

/-- Two finite laws have total variation one exactly when their supports are disjoint. -/
theorem totalVariation_eq_one_iff_disjoint_support (p q : PMF α) :
    totalVariation p q = 1 ↔ Disjoint p.support q.support := by
  classical
  have htotal : totalVariation p q = 1 ↔ (∑ a, min (p a) (q a)) = 0 := by
    rw [sum_min_eq_ofReal_one_sub_totalVariation, ENNReal.ofReal_eq_zero]
    constructor
    · intro h
      linarith
    · intro h
      linarith [totalVariation_le_one p q]
  rw [htotal, Finset.sum_eq_zero_iff]
  constructor
  · intro h
    apply Set.disjoint_left.mpr
    intro a hp hq
    rcases min_eq_zero.mp (h a (Finset.mem_univ a)) with ha | ha
    · exact (p.mem_support_iff a).mp hp ha
    · exact (q.mem_support_iff a).mp hq ha
  · intro h a _
    apply min_eq_zero.mpr
    by_cases hp : p a = 0
    · exact Or.inl hp
    · right
      by_contra hq
      exact Set.disjoint_left.mp h ((p.mem_support_iff a).mpr hp)
        ((q.mem_support_iff a).mpr hq)

private theorem sum_sub_le_interval_mul_totalVariation (p q : PMF α) (f : α → ℝ)
    (l u : ℝ) (hf : ∀ a, l ≤ f a ∧ f a ≤ u) :
    (∑ a, (p a).toReal * f a) - (∑ a, (q a).toReal * f a) ≤
      (u - l) * totalVariation p q := by
  classical
  have hzero : (∑ a, ((p a).toReal - (q a).toReal)) = 0 := by
    rw [Finset.sum_sub_distrib, p.sum_toReal, q.sum_toReal, sub_self]
  have hshift :
      (∑ a, ((p a).toReal - (q a).toReal) * (f a - l)) =
        (∑ a, (p a).toReal * f a) - (∑ a, (q a).toReal * f a) := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hzero, zero_mul, sub_zero]
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib]
  rw [← hshift, totalVariation_eq_sum_pos, Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _
  by_cases h : (q a).toReal ≤ (p a).toReal
  · simp only [ite_eq_left h]
    simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (sub_le_sub_right (hf a).2 l) (sub_nonneg.mpr h)
  · simp only [ite_eq_right h, mul_zero]
    exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge h))
      (sub_nonneg.mpr (hf a).1)

/-- A test taking values in a closed interval has discrepancy at most its width times TV. -/
theorem abs_sum_sub_le_totalVariation_of_mem_Icc (p q : PMF α) (f : α → ℝ)
    (l u : ℝ) (_hlu : l ≤ u) (hf : ∀ a, l ≤ f a ∧ f a ≤ u) :
    |(∑ a, (p a).toReal * f a) - (∑ a, (q a).toReal * f a)| ≤
      (u - l) * totalVariation p q := by
  apply abs_le.mpr
  constructor
  · have h := sum_sub_le_interval_mul_totalVariation q p f l u hf
    rw [totalVariation_comm q p] at h
    linarith
  · exact sum_sub_le_interval_mul_totalVariation p q f l u hf

/-- A test bounded in absolute value by `M` has discrepancy at most `2 * M` times TV. -/
theorem abs_sum_sub_le_mul_totalVariation (p q : PMF α) (f : α → ℝ)
    (M : ℝ) (hM : 0 ≤ M) (hf : ∀ a, |f a| ≤ M) :
    |(∑ a, (p a).toReal * f a) - (∑ a, (q a).toReal * f a)| ≤
      2 * M * totalVariation p q := by
  have h := abs_sum_sub_le_totalVariation_of_mem_Icc p q f (-M) M
    (by linarith) (fun a => abs_le.mp (hf a))
  have hwidth : M - -M = 2 * M := by linarith
  rwa [hwidth] at h

private theorem sum_mul_indicator_one (p : PMF α) (s : Set α) :
    (∑ a, (p a).toReal * s.indicator (fun _ : α => (1 : ℝ)) a) =
      (p.toOuterMeasure s).toReal := by
  classical
  rw [p.toOuterMeasure_toReal_eq_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : a ∈ s <;> simp [ha]

private theorem sum_sub_indicator_eq_totalVariation (p q : PMF α) :
    (∑ a, (p a).toReal *
      {a | (q a).toReal ≤ (p a).toReal}.indicator (fun _ : α => (1 : ℝ)) a) -
        (∑ a, (q a).toReal *
          {a | (q a).toReal ≤ (p a).toReal}.indicator (fun _ : α => (1 : ℝ)) a) =
      totalVariation p q := by
  rw [sum_mul_indicator_one, sum_mul_indicator_one,
    ← totalVariation_eq_toOuterMeasure_sub]

/-- Total variation is the greatest absolute discrepancy of tests valued in `[0, 1]`. -/
theorem totalVariation_isGreatest_unitInterval (p q : PMF α) :
    IsGreatest {d : ℝ | ∃ f : α → ℝ,
      (∀ a, 0 ≤ f a ∧ f a ≤ 1) ∧
        d = |(∑ a, (p a).toReal * f a) - (∑ a, (q a).toReal * f a)|}
      (totalVariation p q) := by
  classical
  constructor
  · refine ⟨{a | (q a).toReal ≤ (p a).toReal}.indicator
      (fun _ : α => (1 : ℝ)), ?_, ?_⟩
    · intro a
      by_cases h : (q a).toReal ≤ (p a).toReal <;> simp [h]
    · rw [sum_sub_indicator_eq_totalVariation,
        abs_of_nonneg (totalVariation_nonneg p q)]
  · rintro _ ⟨f, hf, rfl⟩
    simpa only [sub_zero, one_mul] using
      abs_sum_sub_le_totalVariation_of_mem_Icc p q f 0 1 (by norm_num) hf

private theorem sum_sub_sign_eq_two_mul_totalVariation (p q : PMF α) :
    (∑ a, (p a).toReal *
      (if a ∈ {a | (q a).toReal ≤ (p a).toReal} then (1 : ℝ) else -1)) -
        (∑ a, (q a).toReal *
          (if a ∈ {a | (q a).toReal ≤ (p a).toReal} then (1 : ℝ) else -1)) =
      2 * totalVariation p q := by
  classical
  have hsum (r : PMF α) :
      (∑ a, (r a).toReal *
        (if a ∈ {a | (q a).toReal ≤ (p a).toReal} then (1 : ℝ) else -1)) =
        2 * (∑ a, (r a).toReal *
          {a | (q a).toReal ≤ (p a).toReal}.indicator (fun _ : α => (1 : ℝ)) a) - 1 := by
    calc
      _ = ∑ a, (2 * ((r a).toReal *
          {a | (q a).toReal ≤ (p a).toReal}.indicator (fun _ : α => (1 : ℝ)) a) -
            (r a).toReal) := by
        apply Finset.sum_congr rfl
        intro a _
        by_cases h : (q a).toReal ≤ (p a).toReal
        · simp [h]
          linarith
        · simp [h]
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum, r.sum_toReal]
  rw [hsum p, hsum q]
  have h := sum_sub_indicator_eq_totalVariation p q
  linarith

/-- Twice total variation is the greatest absolute discrepancy of tests bounded by one. -/
theorem two_mul_totalVariation_isGreatest_bounded (p q : PMF α) :
    IsGreatest {d : ℝ | ∃ f : α → ℝ,
      (∀ a, |f a| ≤ 1) ∧
        d = |(∑ a, (p a).toReal * f a) - (∑ a, (q a).toReal * f a)|}
      (2 * totalVariation p q) := by
  classical
  constructor
  · refine ⟨fun a => if a ∈ {a | (q a).toReal ≤ (p a).toReal}
      then (1 : ℝ) else -1, ?_, ?_⟩
    · intro a
      by_cases h : (q a).toReal ≤ (p a).toReal <;> simp [h]
    · rw [sum_sub_sign_eq_two_mul_totalVariation,
        abs_of_nonneg (mul_nonneg (by norm_num) (totalVariation_nonneg p q))]
  · rintro _ ⟨f, hf, rfl⟩
    simpa only [mul_one] using
      abs_sum_sub_le_mul_totalVariation p q f 1 (by norm_num) hf

universe v

variable {β : Type v} [Fintype β]

/-- Applying the same finite channel to two laws cannot increase total variation. -/
theorem totalVariation_bind_le (p q : PMF α) (W : α → PMF β) :
    totalVariation (p.bind W) (q.bind W) ≤ totalVariation p q := by
  have hpoint (b : β) :
      |((p.bind W) b).toReal - ((q.bind W) b).toReal| ≤
        ∑ a, |(p a).toReal - (q a).toReal| * (W a b).toReal := by
    rw [p.bind_toReal_apply, q.bind_toReal_apply, ← Finset.sum_sub_distrib]
    simp_rw [← sub_mul]
    calc
      _ ≤ ∑ a, |((p a).toReal - (q a).toReal) * (W a b).toReal| :=
        Finset.abs_sum_le_sum_abs _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [abs_mul, abs_of_nonneg ((W a).toReal_nonneg b)]
  have hsum :
      (∑ b, |((p.bind W) b).toReal - ((q.bind W) b).toReal|) ≤
        ∑ a, |(p a).toReal - (q a).toReal| := by
    calc
      _ ≤ ∑ b, ∑ a, |(p a).toReal - (q a).toReal| * (W a b).toReal :=
        Finset.sum_le_sum fun b _ => hpoint b
      _ = ∑ a, ∑ b, |(p a).toReal - (q a).toReal| * (W a b).toReal :=
        Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.mul_sum, (W a).sum_toReal, mul_one]
  unfold totalVariation
  linarith

/-- A deterministic map cannot increase total variation. -/
theorem totalVariation_map_le (p q : PMF α) (f : α → β) :
    totalVariation (p.map f) (q.map f) ≤ totalVariation p q := by
  exact totalVariation_bind_le p q (pure ∘ f)

/-- Relabeling a finite alphabet by an equivalence preserves total variation. -/
theorem totalVariation_map_equiv (p q : PMF α) (e : α ≃ β) :
    totalVariation (p.map e) (q.map e) = totalVariation p q := by
  apply le_antisymm
  · exact totalVariation_map_le p q e
  · have h := totalVariation_map_le (p.map e) (q.map e) e.symm
    simpa only [PMF.map_comp, Equiv.symm_comp_self, PMF.map_id] using h

end PMF
