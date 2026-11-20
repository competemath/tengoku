/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku
import Tengoku.LeanTnorms.Tnorms.Basic.Algebra
import Tengoku.LeanTnorms.Tnorms.Util.Mathlib

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Prove things about properties of t-norms related to continuity.  In particular about
  `MulArchimedeanDualWithZero` and `Nilpotent`.  We don't need to prove much about `Strict`
  because it is a class abbrev.  Its properties are largely just inherited from `ContinuousMul` and
  `PosMulStrictMono`.

The main result of this file is a classification of continuous archimedean t-norms.  Every
  continuous archimedean t-norm on a linear order is either nilpotent or strict.
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
local infixl:60 " ⇒ " => LImp

variable {M : Type*}

section Archimedean

variable [TopologicalSpace M] [CommMonoidWithZero M]

  -- Proposition 2.6
lemma _root_.Tengoku.LeanTnorms.idempt_iff_exists_pow_seq_tendsto [Preorder M] [IsOrderedMonoid M] [IsTopOneClass M]
    [T2Space M] [RightContinuousMul M] (a : M) :
    IsIdempotentElem a ↔ ∃ p : M, Filter.Tendsto (p ^ ·) Filter.atTop (nhds a) := by
  constructor
  · intro ha
    use a
    have h : Filter.EventuallyEq Filter.atTop (a ^ ·) (fun _ ↦ a) := by
      rw [Filter.EventuallyEq, Filter.eventually_atTop]
      use 1
      grind [IsIdempotentElem.pow_eq]
    rw [Filter.tendsto_congr' h]
    exact tendsto_const_nhds
  · intro ⟨p, hp⟩
    suffices Filter.Tendsto ((p ^ ·) * (p ^ ·)) Filter.atTop (nhds a) ∧
        Filter.Tendsto ((p ^ ·) * (p ^ ·)) Filter.atTop (nhds (a * a)) by
      exact tendsto_nhds_unique this.2 this.1
    constructor
    · have hp2 : (p ^ ·) * (p ^ ·) = (fun n ↦ p ^ n) ∘ (fun n ↦ 2 * n) := by
        ext n
        simp [two_mul, pow_add]
      rw [hp2]
      refine Filter.Tendsto.comp hp <| Filter.tendsto_atTop_atTop_of_monotone ?_ ?_
      · grind [Monotone]
      · intro b
        use b
        grind
    · have := pow_right_anti₀ zero_le (le_one (a := p))
      exact antitone_continuous_mul _ (p ^ ·) (p ^ ·) a a this this hp hp

lemma _root_.Tengoku.LeanTnorms.exists_pow_tendsto [ConditionallyCompletePartialOrderInf M] [InfConvergenceClass M]
    [IsOrderedMonoid M]
    {p : M} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ q : M, Filter.Tendsto (p ^ ·) Filter.atTop (nhds q) := by
  use ⨅ n, p ^ n
  refine tendsto_atTop_ciInf (pow_right_anti₀ hp0 hp1) ?_
  rw [bddBelow_def]
  use 0
  simp only [Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff]
  intro n
  by_cases! hn : n = 0
  · rw [hn, pow_zero]
    exact le_trans hp0 hp1
  · rw [← zero_pow hn]
    exact pow_le_pow_left' hp0 n

lemma _root_.Tengoku.LeanTnorms.lt_one_of_tendsto [PartialOrder M] [OrderTopology M] [IsTopOneClass M] [OrderTop M]
    [IsOrderedMonoid M]
    {p q : M} (hp1 : p < 1) (hq : Filter.Tendsto (p ^ ·) Filter.atTop (nhds q)) :
    q < 1 := by
  rw [lt_one_iff_ne_one]
  contrapose! hq
  subst hq
  rw [one_eq_top]
  simp only [nhds_top_order, Filter.tendsto_iInf, Filter.tendsto_principal, Set.mem_Ioi,
    Filter.eventually_atTop, not_forall, not_exists]
  use p, (by rwa [← one_eq_top])
  intro n
  use n + 1
  simp only [le_add_iff_nonneg_right, zero_le, exists_const]
  refine not_lt_of_ge ?_
  conv_rhs => rw [← pow_one p]
  exact pow_right_anti₀ zero_le le_one (by lia)

-- Proposition 2.15 (i)

end Archimedean

section Nilpotent

variable (M : Type*) [TopologicalSpace M]

instance [MonoidWithZero M] [SubsingletonZeroOne M] [ContinuousMul M] : Nilpotent M where
  nilpt p hp := by simp [eq_zero_of_ne_one hp]

lemma _root_.Tengoku.LeanTnorms.not_isReduced_of_nilpotent [MonoidWithZero M] [Nilpotent M] [NontrivialZeroOne M] :
    ¬ IsReduced M := by
  simp only [isReduced_iff, not_forall]
  obtain ⟨x, hx0, hx1⟩ := NontrivialZeroOne.exists_ne (M := M)
  use x
  simp only [exists_prop]
  grind [Nilpotent.nilpt]

theorem _root_.Tengoku.LeanTnorms.nilpt_of_not_noZeroDivisors [SemilatticeInf M] [CommMonoidWithZero M]
    [ContinuousMul M] [MulArchimedeanDualWithZero M] [IsOrderedMonoid M] [IsTopOneClass M]
    (h : ¬ NoZeroDivisors M) : Nilpotent M := by
  rw [← isReduced_iff_noZeroDivisors_of_arch, isReduced_iff] at h
  push Not at h
  obtain ⟨a, ⟨m, ha⟩, ha0⟩ := h
  rw [← pos_iff_ne_zero] at ha0
  refine Nilpotent.mk ?_
  intro p hp
  rw [← lt_one_iff_ne_one] at hp
  obtain ⟨n, hap⟩ := MulArchimedeanDualWithZero.arch ha0 hp
  use n * m
  rw [← le_zero_iff]
  grind [pow_mul, pow_le_pow_left']

end Nilpotent

-- proof that all archimedean t-norms are either nilpotent or strict
section Classification

variable (M : Type*) [TopologicalSpace M] [CommMonoidWithZero M]
  [SemilatticeInf M]
  [MulArchimedeanDualWithZero M] [IsOrderedMonoid M] [IsTopOneClass M]
  [NontrivialZeroOne M] [ContinuousMul M]

theorem _root_.Tengoku.LeanTnorms.nilpt_tfae' : [Nilpotent M, ¬ IsReduced M, ¬ NoZeroDivisors M].TFAE := by
  tfae_have 2 → 3 := by simp [isReduced_iff_noZeroDivisors_of_arch]
  tfae_have 3 → 1 := by
    exact nilpt_of_not_noZeroDivisors M
  tfae_have 1 → 2 := by
    intro _
    exact not_isReduced_of_nilpotent M
  tfae_finish

variable (M : Type*) [TopologicalSpace M] [CommMonoidWithZero M]
  [PartialOrder M]
  [MulArchimedeanDualWithZero M] [IsOrderedMonoid M] [IsTopOneClass M]
  [ContinuousMul M] [T2Space M]
  [OrderTopology M]

theorem _root_.Tengoku.LeanTnorms.strict_of_noZeroDivisors_of_tendsto
  (f : ℕ → M)
  (hf : Filter.Tendsto f Filter.atTop (nhds 1))
  (hf1 : ∀ n, f n ≠ 1)
  (h : NoZeroDivisors M) : Strict M := by
  contrapose! h
  simp only [strict_iff, posMulStrictMono_iff, not_and, not_forall] at h
  specialize h (by assumption)
  obtain ⟨u, hu0, ⟨v, w, hvw, h⟩⟩ := h
  suffices ∃ z, v ≤ z * w ∧ z ≠ 1 by
    obtain ⟨z, hvz, hz1⟩ := this
    have huzw : u * w * z = u * w := by
      refine le_antisymm (mul_le_left _ _) ?_
      simp only [lt_iff_le_and_ne, mul_le_mul_right hvw.le u, ne_eq, true_and, not_not] at h
      nth_rw 1 [← h, mul_assoc, mul_comm w z]
      exact mul_le_mul_right hvz u
    have huwz : ∀ (n : ℕ), n ≥ 0 → u * w * (z ^ n) = u * w := by
      simp only [ge_iff_le, zero_le, forall_const]
      intro n
      induction n with
      | zero => simp
      | succ n ih => rwa [pow_succ, ← mul_assoc, ih]
    rw [noZeroDivisors_iff]
    push Not
    use u, w
    constructor; swap; constructor
    · exact ne_of_gt hu0
    · exact ne_of_gt <| lt_of_le_of_lt zero_le hvw
    suffices Filter.Tendsto (fun n : ℕ ↦ u * w * (z ^ n)) Filter.atTop (nhds (u * w)) ∧
        Filter.Tendsto (fun n : ℕ ↦ u * w * (z ^ n)) Filter.atTop (nhds 0) by
      exact tendsto_nhds_unique this.1 this.2
    constructor
    · exact tendsto_atTop_of_eventually_const huwz
    · have huwt : Filter.Tendsto (fun n : ℕ ↦ u * w) Filter.atTop (nhds (u * w)) :=
        tendsto_const_nhds
      have hzt : Filter.Tendsto (z ^ ·) Filter.atTop (nhds 0) := by
        rw [← lt_one_iff_ne_one] at hz1
        exact arch_iff_lim_prop.mp (by assumption) hz1
      rw [show 0 = u * w * 0 by exact Eq.symm (mul_zero _)]
      refine antitone_continuous_mul _ _ _ _ _ antitone_const ?_ huwt hzt
      exact pow_right_anti₀ zero_le le_one
  apply Filter.Tendsto.mul (tendsto_const_nhds (x := w)) at hf
  rw [mul_one] at hf
  simp only [tendsto_order, Filter.eventually_atTop, gt_iff_lt] at hf
  obtain ⟨n, hn⟩ := hf.1 v hvw
  specialize hn n (by rfl)
  rw [mul_comm] at hn
  use f n
  simp [hn.le, hf1 n]

-- TODO: Can we relate NontrivialZeroOne and PreconnectedSpace? (Maybe using Nontrivial)
variable (M : Type*) [TopologicalSpace M] [CommMonoidWithZero M]
  [LinearOrder M]
  [MulArchimedeanDualWithZero M] [IsOrderedMonoid M] [IsTopOneClass M]
  [NontrivialZeroOne M] [ContinuousMul M]
  [OrderTopology M] [PreconnectedSpace M]

/- I think this can be generalized to a product of LinearOrders by making an OrderOpenTopology class
  and prove the analogous theorems as for OrderClosedTopology.  This should allow for a
  generalization of the intermediate value theorem.

  Or the easier way is to duplicate the necessary lemmas (in this project) for LinearOrder +
  OrderClosedTopology.  Then it will hold for products of LinearOrders.
-/
-- TODO: I would like to have a counterexample showing that the LinearOrder assumption can't be
--  weakened to a PartialOrder.
theorem _root_.Tengoku.LeanTnorms.nilpt_tfae : [Nilpotent M, ¬ IsReduced M, ¬ NoZeroDivisors M, ¬ Strict M].TFAE := by
  tfae_have 3 → 1 := nilpt_of_not_noZeroDivisors M
  tfae_have 2 → 4 := by
    contrapose!
    intro h
    infer_instance
  tfae_have 1 → 2 := fun _ ↦ not_isReduced_of_nilpotent M
  tfae_have 4 → 3 := by
    intro h
    simp only [strict_iff, posMulStrictMono_iff, not_and, not_forall, not_lt] at h
    specialize h (by assumption)
    obtain ⟨u, hu0, ⟨v, w, hvw, h⟩⟩ := h
    have hz := intermediate_value_univ v 1 (continuous_const_mul w)
    have hvz : v ∈ Set.Icc (w * v) (w * 1) := by
      simp only [mul_one, Set.mem_Icc]
      constructor
      · exact mul_le_right _ _
      · exact le_of_lt hvw
    apply hz at hvz
    rw [Set.mem_range] at hvz
    obtain ⟨z, hz⟩ := hvz
    have huwz : ∀ (n : ℕ), n ≥ 0 → u * w * (z ^ n) = u * w := by
      simp only [ge_iff_le, zero_le, forall_const]
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have huvw : u * w = u * v := le_antisymm h <| mul_le_mul_right hvw.le u
        rw [pow_succ, ← mul_assoc, ih, mul_assoc, hz, huvw]
    rw [noZeroDivisors_iff]
    push Not
    use u, w
    constructor; swap; constructor
    · exact ne_of_gt hu0
    · exact ne_of_gt <| lt_of_le_of_lt zero_le hvw
    suffices Filter.Tendsto (fun n : ℕ ↦ u * w * (z ^ n)) Filter.atTop (nhds (u * w)) ∧
        Filter.Tendsto (fun n : ℕ ↦ u * w * (z ^ n)) Filter.atTop (nhds 0) by
      exact tendsto_nhds_unique this.1 this.2
    constructor
    · exact tendsto_atTop_of_eventually_const huwz
    · have huwt : Filter.Tendsto (fun n : ℕ ↦ u * w) Filter.atTop (nhds (u * w)) :=
        tendsto_const_nhds
      have hzt : Filter.Tendsto (z ^ ·) Filter.atTop (nhds 0) := by
        have hz1 : z < 1 := by
          rw [lt_one_iff_ne_one]
          contrapose! hz
          rw [hz, mul_one]
          exact ne_of_gt hvw
        exact arch_iff_lim_prop.mp (by assumption) hz1
      rw [show 0 = u * w * 0 by exact Eq.symm (mul_zero _)]
      refine antitone_continuous_mul _ _ _ _ _ antitone_const ?_ huwt hzt
      exact pow_right_anti₀ zero_le le_one
  tfae_finish

theorem _root_.Tengoku.LeanTnorms.nilpt_iff : Nilpotent M ↔ ¬ Strict M := by
  refine (nilpt_tfae M) (Nilpotent M) ?_ (¬ Strict M) ?_ <;> simp

theorem _root_.Tengoku.LeanTnorms.nilpt_or_strict_of_cont_arch : Nilpotent M ∨ Strict M := by
  grind [nilpt_iff]

end Classification

variable {M : Type*} [TopologicalSpace M] [CommMonoidWithZero M]
  [LinearOrder M]
  [MulArchimedeanDualWithZero M] [IsOrderedMonoid M] [IsTopOneClass M]
  [NontrivialZeroOne M] [ContinuousMul M]
  [OrderTopology M] [PreconnectedSpace M]

lemma _root_.Tengoku.LeanTnorms.mul_lt_right (p q : M) (hp1 : p ≠ 1) (hq0 : q ≠ 0) : p * q < q := by
  by_cases! hnt : ¬Nontrivial M
  · rw [not_nontrivial_iff_subsingleton] at hnt
    grind [Subsingleton.eq_one p]
  cases nilpt_or_strict_of_cont_arch M
  · refine lt_of_le_of_ne (mul_le_right p q) ?_
    by_contra!
    have hp : ∀ n, (p ^ n) * q = q := by
      intro n
      induction n with
      | zero => simp
      | succ n ih => rw [pow_add, pow_one, mul_assoc, this, ih]
    have hp' := Nilpotent.nilpt p hp1
    obtain ⟨n, hn⟩ := hp'
    specialize hp n
    rw [hn, zero_mul] at hp
    symm at hp
    contradiction
  · have := PosMulStrictMono.toMulPosStrictMono (α := M)
    exact mul_lt_of_lt_one_left (lt_of_le_of_ne' zero_le hq0) <| (lt_of_le_of_ne le_one hp1)

lemma _root_.Tengoku.LeanTnorms.mul_lt_left (p q : M) (hp0 : p ≠ 0) (hq1 : q ≠ 1) : p * q < p := by
  rw [mul_comm]
  exact mul_lt_right q p hq1 hp0

theorem _root_.Tengoku.LeanTnorms.npow_right_strictAnti (p : M) (n m : ℕ) (hp1 : p ≠ 1) (hpn : p ^ n ≠ 0)
    (h : n < m) : p ^ m < p ^ n := by
  obtain ⟨k, hk0, hk⟩ := exists_pos_add_of_lt h
  rw [← hk, pow_add]
  refine mul_lt_left _ _ hpn ?_
  rw [← lt_one_iff_ne_one] at hp1
  refine ne_of_lt <| lt_of_le_of_lt ?_ hp1
  nth_rw 2 [← npow_one p]
  exact pow_right_anti₀ zero_le le_one hk0

theorem _root_.Tengoku.LeanTnorms.npow_right_inj (p : M) (n m : ℕ) (hp1 : p ≠ 1) (hpn : p ^ n ≠ 0)
    (h : p ^ n = p ^ m) : n = m := by
  contrapose! h
  wlog hnm : n < m generalizing n m
  · symm at h
    contrapose! h
    rw [h] at hpn
    contrapose! h
    push Not at hnm
    exact (this m n hpn h (lt_of_le_of_ne hnm h)).symm
  · exact (ne_of_lt <| npow_right_strictAnti p n m hp1 hpn hnm).symm
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
