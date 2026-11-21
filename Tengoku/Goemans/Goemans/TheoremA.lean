/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: Weaver (exploration and formalization); GPT-5.6 Sol (review).
-/
import Tengoku.Goemans.Goemans.Admissibility
import Tengoku.Goemans.Goemans.Costs
import Tengoku.Goemans.Goemans.Inequalities

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Theorem A, upper bound: `ρ(H*) ≤ ρ* = 2/(2√2 - 1)`

Every SSUF instance on the Rybin digraph `H*` admits an unsplittable routing
within the Dinitz–Garg–Goemans capacity bound of cost at most
`ρ* = 2/(2√2 - 1) ≈ 1.0938363` times the fractional cost
(`exists_admissible_ucost_le`).

Proof architecture (paper, Section 3):

* `af i = 1 - fᵢ/dᵢ` is the expensive fraction; blocked pairs force
  `af i + af j ≥ 1` (Lemma 2 via `pair_bound`), an all-blocked pattern forces
  `Σ af ≥ 2√2 - 1` (Lemma 3 via `splitLP`), and a blocked triple over
  admissible pairs forces `Σ af > 1` (case (d) of Lemma 5a);
* `exists_admissible_weight`: for any nonnegative savings `m`, some admissible
  routing's forgone savings are at most `ρ*·Σ mᵢ·afᵢ` — the weight
  inequality (Lemma 5a), dispatched over the 2³ admissibility patterns of
  the three pairs into the four cores `weight_core_a/b/c/d`;
* `exists_admissible_ucost_le`: the reduction to nonnegative savings
  (Lemma 4) — apply the weight inequality to `m i = max (sav i) 0`, drop the
  negative-saving terminals from the routing (downward closure), and absorb
  the negative parts pointwise into `(ρ* - 1)·base`.
-/

namespace Goemans

namespace FlowInstance

open Real

variable (I : FlowInstance ℝ)

/-- The expensive fraction `af i = 1 - fᵢ/dᵢ ∈ [0,1]` (the paper's
`aᵢ = 1 - zᵢ`).-/
noncomputable def af (i : Terminal) : ℝ := 1 - I.f i / I.d i

/--
@isnad1 id=le.0h2v.s4.68c04bb5fbae from=translated src=- shape=4328188d vocab=45aea91e
-/
theorem af_nonneg (i : Terminal) : 0 ≤ I.af i := by
  have hd := I.d_pos i
  have hf := I.f_le_d i
  rw [af, sub_nonneg]
  exact (div_le_one hd).mpr hf

/--
@isnad1 id=le.0h2v.s4.2eaa6bd91bce from=translated src=- shape=da955437 vocab=45aea91e
-/
theorem af_le_one (i : Terminal) : I.af i ≤ 1 := by
  have h : 0 ≤ I.f i / I.d i := div_nonneg (I.f_nonneg i) (I.d_pos i).le
  rw [af]
  linarith

/--
@isnad1 id=eq.0h2v.s5.5a38d8b35857 from=translated src=- shape=e6ebc7fb vocab=af2c783d
-/
theorem af_mul_d (i : Terminal) : I.af i * I.d i = I.d i - I.f i := by
  have hd := (I.d_pos i).ne'
  rw [af]
  field_simp

/-! ### Blocked patterns force lower bounds on the expensive fractions -/

/-- Strict Lemma 2 for the pair `{0,1}`.
@isnad1 id=lt.1h1v.s6.332db4727ccd from=translated src=- shape=fbd3ef94 vocab=ab7e2154
-/
theorem blocked_af01_lt (h : ¬ I.Admissible {0, 1}) : 1 < I.af 0 + I.af 1 := by
  have hb := I.blocked_pair01_lt h
  have key := pair_bound_lt (I.d_pos 0) (I.d_pos 1) (I.f_nonneg 0) (I.f_nonneg 1)
    (I.d_le_dmax 0) (I.d_le_dmax 1) hb
  simp only [af]
  linarith

/-- Closed Lemma 2 for the pair `{0,1}`.
@isnad1 id=le.1h1v.s6.8d96b5050d46 from=translated src=- shape=fbd3ef94 vocab=c31b55a9
-/
theorem blocked_af01 (h : ¬ I.Admissible {0, 1}) : 1 ≤ I.af 0 + I.af 1 :=
  (I.blocked_af01_lt h).le

/-- Strict Lemma 2 for the pair `{1,2}`.
@isnad1 id=lt.1h1v.s6.10591d0494c5 from=translated src=- shape=fbd3ef94 vocab=ab7e2154
-/
theorem blocked_af12_lt (h : ¬ I.Admissible {1, 2}) : 1 < I.af 1 + I.af 2 := by
  have hb := I.blocked_pair12_lt h
  have key := pair_bound_lt (I.d_pos 1) (I.d_pos 2) (I.f_nonneg 1) (I.f_nonneg 2)
    (I.d_le_dmax 1) (I.d_le_dmax 2) hb
  simp only [af]
  linarith

/-- Closed Lemma 2 for the pair `{1,2}`.
@isnad1 id=le.1h1v.s6.8bfc7e5c7b6b from=translated src=- shape=fbd3ef94 vocab=c31b55a9
-/
theorem blocked_af12 (h : ¬ I.Admissible {1, 2}) : 1 ≤ I.af 1 + I.af 2 :=
  (I.blocked_af12_lt h).le

/-- Strict Lemma 2 for the pair `{0,2}`.
@isnad1 id=lt.1h1v.s6.e5f0c6f84f49 from=translated src=- shape=fbd3ef94 vocab=ab7e2154
-/
theorem blocked_af02_lt (h : ¬ I.Admissible {0, 2}) : 1 < I.af 0 + I.af 2 := by
  have hb := I.blocked_pair02_lt h
  have hb' : I.f 0 + I.f 2 < I.d 0 + I.d 2 - I.dmax := by
    linarith [I.f_nonneg 1]
  have key := pair_bound_lt (I.d_pos 0) (I.d_pos 2) (I.f_nonneg 0) (I.f_nonneg 2)
    (I.d_le_dmax 0) (I.d_le_dmax 2) hb'
  simp only [af]
  linarith

/-- Closed Lemma 2 for the pair `{0,2}`.
@isnad1 id=le.1h1v.s6.3a9ae57f795a from=translated src=- shape=fbd3ef94 vocab=c31b55a9
-/
theorem blocked_af02 (h : ¬ I.Admissible {0, 2}) : 1 ≤ I.af 0 + I.af 2 :=
  (I.blocked_af02_lt h).le

/-- Strict Lemma 3: all three pairs blocked forces
`Σ af > 2√2 - 1`.
@isnad1 id=lt.3h1v.s7.fb6d49de122c from=translated src=- shape=e46cc2c2 vocab=9e628536
-/
theorem all_blocked_af_lt (h01 : ¬ I.Admissible {0, 1})
    (h12 : ¬ I.Admissible {1, 2})
    (h02 : ¬ I.Admissible {0, 2}) :
    2 * Real.sqrt 2 - 1 < I.af 0 + I.af 1 + I.af 2 := by
  have key := splitLP_lt (I.d_pos 0) (I.d_pos 1) (I.d_pos 2)
    (I.f_nonneg 0) (I.f_nonneg 2)
    (I.f_le_d 0) (I.f_le_d 1) (I.f_le_d 2)
    (I.d_le_dmax 0) (I.d_le_dmax 1) (I.d_le_dmax 2)
    (I.blocked_pair01_lt h01) (I.blocked_pair12_lt h12).le
    (I.blocked_pair02_lt h02)
  simp only [af]
  linarith

/-- Closed form of Lemma 3.
@isnad1 id=le.3h1v.s7.e64b0aab150b from=translated src=- shape=e46cc2c2 vocab=f60a6cb2
-/
theorem all_blocked_af (h01 : ¬ I.Admissible {0, 1})
    (h12 : ¬ I.Admissible {1, 2}) (h02 : ¬ I.Admissible {0, 2}) :
    2 * Real.sqrt 2 - 1 ≤ I.af 0 + I.af 1 + I.af 2 :=
  (I.all_blocked_af_lt h01 h12 h02).le

/-- Strict case (d) of Lemma 5a: a blocked triple over admissible pairs
forces `Σ af > 1`.
@isnad1 id=lt.3h1v.s7.9c974121455d from=translated src=- shape=bb7c079a vocab=a6aada30
-/
theorem triple_blocked_af_lt (h01 : I.Admissible {0, 1})
    (h12 : I.Admissible {1, 2})
    (h : ¬ I.Admissible Finset.univ) :
    1 < I.af 0 + I.af 1 + I.af 2 := by
  have hb := I.blocked_triple h01 h12 h
  have t0 : 0 ≤ I.af 0 * (I.dmax - I.d 0) :=
    mul_nonneg (I.af_nonneg 0) (by linarith [I.d_le_dmax 0])
  have t1 : 0 ≤ I.af 1 * (I.dmax - I.d 1) :=
    mul_nonneg (I.af_nonneg 1) (by linarith [I.d_le_dmax 1])
  have t2 : 0 ≤ I.af 2 * (I.dmax - I.d 2) :=
    mul_nonneg (I.af_nonneg 2) (by linarith [I.d_le_dmax 2])
  have hD := I.dmax_pos
  nlinarith [I.af_mul_d 0, I.af_mul_d 1, I.af_mul_d 2, t0, t1, t2]

/-- Closed case-(d) expensive-fraction bound.
@isnad1 id=le.3h1v.s7.dce07b11c0f5 from=translated src=- shape=bb7c079a vocab=4860a6c6
-/
theorem triple_blocked_af (h01 : I.Admissible {0, 1})
    (h12 : I.Admissible {1, 2}) (h : ¬ I.Admissible Finset.univ) :
    1 ≤ I.af 0 + I.af 1 + I.af 2 :=
  (I.triple_blocked_af_lt h01 h12 h).le

/-! ### The weight inequality (Lemma 5a) -/

/-- **Lemma 5a (the weight inequality).** For every nonnegative savings vector
`m` there is an admissible routing forgoing at most `ρ*·Σ mᵢ·afᵢ` of savings.
The four cases of the paper correspond to the admissibility pattern of the
three pairs.
@isnad1 id=ex.1h2v.s6.bfbdfd3c5cb7 from=translated src=- shape=21a1f86b vocab=264aab2d
-/
theorem exists_admissible_weight (m : Terminal → ℝ) (hm : ∀ i, 0 ≤ m i) :
    ∃ S : Finset Terminal, I.Admissible S ∧
      (∑ i, if i ∈ S then 0 else m i) ≤ rhoStar * ∑ i, m i * I.af i := by
  have ha0 := I.af_nonneg 0
  have ha1 := I.af_nonneg 1
  have ha2 := I.af_nonneg 2
  have hm0 := hm 0
  have hm1 := hm 1
  have hm2 := hm 2
  have hρ0 : (0 : ℝ) ≤ rhoStar := rhoStar_pos.le
  have hρ1 : (1 : ℝ) ≤ rhoStar := one_le_rhoStar
  have lift_pair : ∀ s : ℝ, 1 ≤ s → 1 ≤ rhoStar * s := fun s hs => by nlinarith
  have lift_sum : ∀ s : ℝ, 2 * Real.sqrt 2 - 1 ≤ s → 2 ≤ rhoStar * s := fun s hs => by
    have h2 := rhoStar_mul_denom
    nlinarith [mul_le_mul_of_nonneg_left hs hρ0]
  -- evaluation of the forgone-savings sum on each candidate routing
  have eEmpty : (∑ i, if i ∈ (Finset.univ : Finset Terminal) then 0 else m i) = 0 := by
    simp
  have e0 : (∑ i, if i ∈ ({0} : Finset Terminal) then 0 else m i) = m 1 + m 2 := by
    simp [Fin.sum_univ_three]
  have e1 : (∑ i, if i ∈ ({1} : Finset Terminal) then 0 else m i) = m 0 + m 2 := by
    simp [Fin.sum_univ_three]
  have e2 : (∑ i, if i ∈ ({2} : Finset Terminal) then 0 else m i) = m 0 + m 1 := by
    simp [Fin.sum_univ_three]
  have e01 : (∑ i, if i ∈ ({0, 1} : Finset Terminal) then 0 else m i) = m 2 := by
    simp [Fin.sum_univ_three]
  have e02 : (∑ i, if i ∈ ({0, 2} : Finset Terminal) then 0 else m i) = m 1 := by
    simp [Fin.sum_univ_three]
  have e12 : (∑ i, if i ∈ ({1, 2} : Finset Terminal) then 0 else m i) = m 0 := by
    simp [Fin.sum_univ_three]
  by_cases h01 : I.Admissible {0, 1} <;>
    by_cases h02 : I.Admissible {0, 2} <;>
    by_cases h12 : I.Admissible {1, 2}
  -- case TTT: all pairs admissible (paper case (d))
  · by_cases huniv : I.Admissible Finset.univ
    · refine ⟨Finset.univ, huniv, ?_⟩
      rw [eEmpty, Fin.sum_univ_three]
      nlinarith [mul_nonneg hm0 ha0, mul_nonneg hm1 ha1, mul_nonneg hm2 ha2]
    · -- triple blocked: route the two largest savings cheap
      have hsum : 1 ≤ rhoStar * (I.af 0 + I.af 1 + I.af 2) :=
        lift_pair _ (I.triple_blocked_af h01 h12 huniv)
      have core := weight_core_d hm0 hm1 hm2 ha0 ha1 ha2 hρ0 hsum
      rcases le_total (m 0) (m 1) with h01m | h01m
      · rcases le_total (m 0) (m 2) with h02m | h02m
        · -- argmin 0: route {1,2}
          rw [min_eq_left (le_min h01m h02m)] at core
          refine ⟨{1, 2}, h12, ?_⟩
          rw [e12, Fin.sum_univ_three]
          linarith [core]
        · -- argmin 2: route {0,1}
          rw [min_eq_right (show m 2 ≤ m 1 by linarith),
            min_eq_right h02m] at core
          refine ⟨{0, 1}, h01, ?_⟩
          rw [e01, Fin.sum_univ_three]
          linarith [core]
      · rcases le_total (m 1) (m 2) with h12m | h12m
        · -- argmin 1: route {0,2}
          rw [min_eq_left h12m, min_eq_right h01m] at core
          refine ⟨{0, 2}, h02, ?_⟩
          rw [e02, Fin.sum_univ_three]
          linarith [core]
        · -- argmin 2: route {0,1}
          rw [min_eq_right h12m,
            min_eq_right (show m 2 ≤ m 0 by linarith)] at core
          refine ⟨{0, 1}, h01, ?_⟩
          rw [e01, Fin.sum_univ_three]
          linarith [core]
  -- case TTF: pair {1,2} blocked, {0,1}, {0,2} admissible (paper case (c))
  · have hik : 1 ≤ rhoStar * (I.af 1 + I.af 2) := lift_pair _ (I.blocked_af12 h12)
    have core := weight_core_c (r := rhoStar) (ai := I.af 1) (aj := I.af 0)
      (ak := I.af 2) hm1 hm0 hm2 ha1 ha0 ha2 hρ1 hik
    rcases le_total (m 1) (m 2) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{0, 2}, h02, ?_⟩
      rw [e02, Fin.sum_univ_three]
      linarith [core]
    · rw [min_eq_right hmin] at core
      refine ⟨{0, 1}, h01, ?_⟩
      rw [e01, Fin.sum_univ_three]
      linarith [core]
  -- case TFT: pair {0,2} blocked, {0,1}, {1,2} admissible (paper case (c))
  · have hik : 1 ≤ rhoStar * (I.af 0 + I.af 2) := lift_pair _ (I.blocked_af02 h02)
    have core := weight_core_c (r := rhoStar) (ai := I.af 0) (aj := I.af 1)
      (ak := I.af 2) hm0 hm1 hm2 ha0 ha1 ha2 hρ1 hik
    rcases le_total (m 0) (m 2) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{1, 2}, h12, ?_⟩
      rw [e12, Fin.sum_univ_three]
      linarith [core]
    · rw [min_eq_right hmin] at core
      refine ⟨{0, 1}, h01, ?_⟩
      rw [e01, Fin.sum_univ_three]
      linarith [core]
  -- case TFF: only pair {0,1} admissible (paper case (b), k = 2)
  · have hik : 1 ≤ rhoStar * (I.af 0 + I.af 2) := lift_pair _ (I.blocked_af02 h02)
    have hjk : 1 ≤ rhoStar * (I.af 1 + I.af 2) := lift_pair _ (I.blocked_af12 h12)
    have core := weight_core_b (r := rhoStar) (ai := I.af 0) (aj := I.af 1)
      (ak := I.af 2) hm0 hm1 hm2 ha0 ha1 ha2 hρ1 hik hjk
    rcases le_total (m 0 + m 1) (m 2) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{2}, I.admissible_singleton 2, ?_⟩
      rw [e2, Fin.sum_univ_three]
      linarith [core]
    · rw [min_eq_right hmin] at core
      refine ⟨{0, 1}, h01, ?_⟩
      rw [e01, Fin.sum_univ_three]
      linarith [core]
  -- case FTT: pair {0,1} blocked, {0,2}, {1,2} admissible (paper case (c))
  · have hik : 1 ≤ rhoStar * (I.af 0 + I.af 1) := lift_pair _ (I.blocked_af01 h01)
    have core := weight_core_c (r := rhoStar) (ai := I.af 0) (aj := I.af 2)
      (ak := I.af 1) hm0 hm2 hm1 ha0 ha2 ha1 hρ1 hik
    rcases le_total (m 0) (m 1) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{1, 2}, h12, ?_⟩
      rw [e12, Fin.sum_univ_three]
      linarith [core]
    · rw [min_eq_right hmin] at core
      refine ⟨{0, 2}, h02, ?_⟩
      rw [e02, Fin.sum_univ_three]
      linarith [core]
  -- case FTF: only pair {0,2} admissible (paper case (b), k = 1)
  · have hik : 1 ≤ rhoStar * (I.af 0 + I.af 1) := lift_pair _ (I.blocked_af01 h01)
    have hjk : 1 ≤ rhoStar * (I.af 2 + I.af 1) := by
      have h := lift_pair _ (I.blocked_af12 h12)
      nlinarith [h]
    have core := weight_core_b (r := rhoStar) (ai := I.af 0) (aj := I.af 2)
      (ak := I.af 1) hm0 hm2 hm1 ha0 ha2 ha1 hρ1 hik hjk
    rcases le_total (m 0 + m 2) (m 1) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{1}, I.admissible_singleton 1, ?_⟩
      rw [e1, Fin.sum_univ_three]
      linarith [core]
    · rw [min_eq_right hmin] at core
      refine ⟨{0, 2}, h02, ?_⟩
      rw [e02, Fin.sum_univ_three]
      linarith [core]
  -- case FFT: only pair {1,2} admissible (paper case (b), k = 0)
  · have hik : 1 ≤ rhoStar * (I.af 1 + I.af 0) := by
      have h := lift_pair _ (I.blocked_af01 h01)
      nlinarith [h]
    have hjk : 1 ≤ rhoStar * (I.af 2 + I.af 0) := by
      have h := lift_pair _ (I.blocked_af02 h02)
      nlinarith [h]
    have core := weight_core_b (r := rhoStar) (ai := I.af 1) (aj := I.af 2)
      (ak := I.af 0) hm1 hm2 hm0 ha1 ha2 ha0 hρ1 hik hjk
    rcases le_total (m 1 + m 2) (m 0) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{0}, I.admissible_singleton 0, ?_⟩
      rw [e0, Fin.sum_univ_three]
      linarith [core]
    · rw [min_eq_right hmin] at core
      refine ⟨{1, 2}, h12, ?_⟩
      rw [e12, Fin.sum_univ_three]
      linarith [core]
  -- case FFF: all pairs blocked (paper case (a)): route the largest saving
  · have r01 : 1 ≤ rhoStar * (I.af 0 + I.af 1) := lift_pair _ (I.blocked_af01 h01)
    have r02 : 1 ≤ rhoStar * (I.af 0 + I.af 2) := lift_pair _ (I.blocked_af02 h02)
    have r12 : 1 ≤ rhoStar * (I.af 1 + I.af 2) := lift_pair _ (I.blocked_af12 h12)
    have rsum : 2 ≤ rhoStar * (I.af 0 + I.af 1 + I.af 2) :=
      lift_sum _ (I.all_blocked_af h01 h12 h02)
    rcases le_total (m 0) (m 1) with hab | hab
    · rcases le_total (m 1) (m 2) with hbc | hbc
      · -- m0 ≤ m1 ≤ m2: max = 2, mid = 1, small = 0
        have core := weight_core_a (r := rhoStar) (a1 := I.af 1) (a2 := I.af 0)
          (a3 := I.af 2) (m1 := m 1) (m2 := m 0) (m3 := m 2)
          hm0 hab hbc ha2 hρ0 (by nlinarith [r12]) (by nlinarith [rsum])
        refine ⟨{2}, I.admissible_singleton 2, ?_⟩
        rw [e2, Fin.sum_univ_three]
        linarith [core]
      · rcases le_total (m 0) (m 2) with hac | hac
        · -- m0 ≤ m2 ≤ m1: max = 1, mid = 2, small = 0
          have core := weight_core_a (r := rhoStar) (a1 := I.af 2) (a2 := I.af 0)
            (a3 := I.af 1) (m1 := m 2) (m2 := m 0) (m3 := m 1)
            hm0 hac hbc ha1 hρ0 (by nlinarith [r12]) (by nlinarith [rsum])
          refine ⟨{1}, I.admissible_singleton 1, ?_⟩
          rw [e1, Fin.sum_univ_three]
          linarith [core]
        · -- m2 ≤ m0 ≤ m1: max = 1, mid = 0, small = 2
          have core := weight_core_a (r := rhoStar) (a1 := I.af 0) (a2 := I.af 2)
            (a3 := I.af 1) (m1 := m 0) (m2 := m 2) (m3 := m 1)
            hm2 hac hab ha1 hρ0 (by nlinarith [r01]) (by nlinarith [rsum])
          refine ⟨{1}, I.admissible_singleton 1, ?_⟩
          rw [e1, Fin.sum_univ_three]
          linarith [core]
    · rcases le_total (m 0) (m 2) with hac | hac
      · -- m1 ≤ m0 ≤ m2: max = 2, mid = 0, small = 1
        have core := weight_core_a (r := rhoStar) (a1 := I.af 0) (a2 := I.af 1)
          (a3 := I.af 2) (m1 := m 0) (m2 := m 1) (m3 := m 2)
          hm1 hab hac ha2 hρ0 (by nlinarith [r02]) (by nlinarith [rsum])
        refine ⟨{2}, I.admissible_singleton 2, ?_⟩
        rw [e2, Fin.sum_univ_three]
        linarith [core]
      · rcases le_total (m 1) (m 2) with hbc | hbc
        · -- m1 ≤ m2 ≤ m0: max = 0, mid = 2, small = 1
          have core := weight_core_a (r := rhoStar) (a1 := I.af 2) (a2 := I.af 1)
            (a3 := I.af 0) (m1 := m 2) (m2 := m 1) (m3 := m 0)
            hm1 hbc hac ha0 hρ0 (by nlinarith [r02]) (by nlinarith [rsum])
          refine ⟨{0}, I.admissible_singleton 0, ?_⟩
          rw [e0, Fin.sum_univ_three]
          linarith [core]
        · -- m2 ≤ m1 ≤ m0: max = 0, mid = 1, small = 2
          have core := weight_core_a (r := rhoStar) (a1 := I.af 1) (a2 := I.af 2)
            (a3 := I.af 0) (m1 := m 1) (m2 := m 2) (m3 := m 0)
            hm2 hbc hab ha0 hρ0 (by nlinarith [r01]) (by nlinarith [rsum])
          refine ⟨{0}, I.admissible_singleton 0, ?_⟩
          rw [e0, Fin.sum_univ_three]
          linarith [core]

/-- Strict weight inequality. Whenever the weighted expensive fraction is
positive, some admissible routing forgoes strictly less than the sharp
factor times that weight. The strictness comes from inadmissibility itself:
outside the all-pairs-blocked case the same routing cores work already at
factor `1`; in the remaining case `weight_core_a_lt` retains the strict
blocked-pair and split-LP slacks.
@isnad1 id=ex.2h2v.s7.f2357bc6a1b3 from=translated src=- shape=0207bea2 vocab=174b6bda
-/
theorem exists_admissible_weight_lt (m : Terminal → ℝ) (hm : ∀ i, 0 ≤ m i)
    (hW : 0 < ∑ i, m i * I.af i) :
    ∃ S : Finset Terminal, I.Admissible S ∧
      (∑ i, if i ∈ S then 0 else m i) < rhoStar * ∑ i, m i * I.af i := by
  have ha0 := I.af_nonneg 0
  have ha1 := I.af_nonneg 1
  have ha2 := I.af_nonneg 2
  have hm0 := hm 0
  have hm1 := hm 1
  have hm2 := hm 2
  have hρ0 : (0 : ℝ) ≤ rhoStar := rhoStar_pos.le
  have hρ1 : (1 : ℝ) < rhoStar := one_lt_rhoStar
  rw [Fin.sum_univ_three] at hW
  have hWρ :
      m 0 * I.af 0 + m 1 * I.af 1 + m 2 * I.af 2 <
        rhoStar * (m 0 * I.af 0 + m 1 * I.af 1 + m 2 * I.af 2) := by
    have hp : 0 < (rhoStar - 1) *
        (m 0 * I.af 0 + m 1 * I.af 1 + m 2 * I.af 2) :=
      mul_pos (by linarith) hW
    nlinarith
  have lift_pair_lt : ∀ s : ℝ, 1 < s → 1 < rhoStar * s := fun s hs => by
    have hs0 : 0 < s := by linarith
    have hp := mul_pos (sub_pos.mpr one_lt_rhoStar) hs0
    nlinarith
  have lift_sum_lt : ∀ s : ℝ, 2 * Real.sqrt 2 - 1 < s →
      2 < rhoStar * s := fun s hs => by
    have hp := mul_lt_mul_of_pos_left hs rhoStar_pos
    nlinarith [rhoStar_mul_denom]
  have eUniv : (∑ i, if i ∈ (Finset.univ : Finset Terminal) then 0 else m i) = 0 := by
    simp
  have e0 : (∑ i, if i ∈ ({0} : Finset Terminal) then 0 else m i) = m 1 + m 2 := by
    simp [Fin.sum_univ_three]
  have e1 : (∑ i, if i ∈ ({1} : Finset Terminal) then 0 else m i) = m 0 + m 2 := by
    simp [Fin.sum_univ_three]
  have e2 : (∑ i, if i ∈ ({2} : Finset Terminal) then 0 else m i) = m 0 + m 1 := by
    simp [Fin.sum_univ_three]
  have e01 : (∑ i, if i ∈ ({0, 1} : Finset Terminal) then 0 else m i) = m 2 := by
    simp [Fin.sum_univ_three]
  have e02 : (∑ i, if i ∈ ({0, 2} : Finset Terminal) then 0 else m i) = m 1 := by
    simp [Fin.sum_univ_three]
  have e12 : (∑ i, if i ∈ ({1, 2} : Finset Terminal) then 0 else m i) = m 0 := by
    simp [Fin.sum_univ_three]
  by_cases h01 : I.Admissible {0, 1} <;>
    by_cases h02 : I.Admissible {0, 2} <;>
    by_cases h12 : I.Admissible {1, 2}
  · by_cases huniv : I.Admissible Finset.univ
    · refine ⟨Finset.univ, huniv, ?_⟩
      rw [eUniv, Fin.sum_univ_three]
      exact lt_trans (by linarith : (0 : ℝ) <
        m 0 * I.af 0 + m 1 * I.af 1 + m 2 * I.af 2) hWρ
    · have hsum : 1 ≤
          (1 : ℝ) * (I.af 0 + I.af 1 + I.af 2) := by
        simpa using (I.triple_blocked_af_lt h01 h12 huniv).le
      have core := weight_core_d hm0 hm1 hm2 ha0 ha1 ha2
        (show (0 : ℝ) ≤ 1 by norm_num) hsum
      rcases le_total (m 0) (m 1) with h01m | h01m
      · rcases le_total (m 0) (m 2) with h02m | h02m
        · rw [min_eq_left (le_min h01m h02m)] at core
          refine ⟨{1, 2}, h12, ?_⟩
          rw [e12, Fin.sum_univ_three]
          norm_num at core
          linarith
        · rw [min_eq_right (show m 2 ≤ m 1 by linarith),
            min_eq_right h02m] at core
          refine ⟨{0, 1}, h01, ?_⟩
          rw [e01, Fin.sum_univ_three]
          norm_num at core
          linarith
      · rcases le_total (m 1) (m 2) with h12m | h12m
        · rw [min_eq_left h12m, min_eq_right h01m] at core
          refine ⟨{0, 2}, h02, ?_⟩
          rw [e02, Fin.sum_univ_three]
          norm_num at core
          linarith
        · rw [min_eq_right h12m,
            min_eq_right (show m 2 ≤ m 0 by linarith)] at core
          refine ⟨{0, 1}, h01, ?_⟩
          rw [e01, Fin.sum_univ_three]
          norm_num at core
          linarith
  · have hik : 1 ≤ (1 : ℝ) * (I.af 1 + I.af 2) := by
      simpa using (I.blocked_af12_lt h12).le
    have core := weight_core_c (r := (1 : ℝ)) (ai := I.af 1) (aj := I.af 0)
      (ak := I.af 2) hm1 hm0 hm2 ha1 ha0 ha2 (by norm_num) hik
    rcases le_total (m 1) (m 2) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{0, 2}, h02, ?_⟩
      rw [e02, Fin.sum_univ_three]
      norm_num at core
      linarith
    · rw [min_eq_right hmin] at core
      refine ⟨{0, 1}, h01, ?_⟩
      rw [e01, Fin.sum_univ_three]
      norm_num at core
      linarith
  · have hik : 1 ≤ (1 : ℝ) * (I.af 0 + I.af 2) := by
      simpa using (I.blocked_af02_lt h02).le
    have core := weight_core_c (r := (1 : ℝ)) (ai := I.af 0) (aj := I.af 1)
      (ak := I.af 2) hm0 hm1 hm2 ha0 ha1 ha2 (by norm_num) hik
    rcases le_total (m 0) (m 2) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{1, 2}, h12, ?_⟩
      rw [e12, Fin.sum_univ_three]
      norm_num at core
      linarith
    · rw [min_eq_right hmin] at core
      refine ⟨{0, 1}, h01, ?_⟩
      rw [e01, Fin.sum_univ_three]
      norm_num at core
      linarith
  · have hik : 1 ≤ (1 : ℝ) * (I.af 0 + I.af 2) := by
      simpa using (I.blocked_af02_lt h02).le
    have hjk : 1 ≤ (1 : ℝ) * (I.af 1 + I.af 2) := by
      simpa using (I.blocked_af12_lt h12).le
    have core := weight_core_b (r := (1 : ℝ)) (ai := I.af 0) (aj := I.af 1)
      (ak := I.af 2) hm0 hm1 hm2 ha0 ha1 ha2 (by norm_num) hik hjk
    rcases le_total (m 0 + m 1) (m 2) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{2}, I.admissible_singleton 2, ?_⟩
      rw [e2, Fin.sum_univ_three]
      norm_num at core
      linarith
    · rw [min_eq_right hmin] at core
      refine ⟨{0, 1}, h01, ?_⟩
      rw [e01, Fin.sum_univ_three]
      norm_num at core
      linarith
  · have hik : 1 ≤ (1 : ℝ) * (I.af 0 + I.af 1) := by
      simpa using (I.blocked_af01_lt h01).le
    have core := weight_core_c (r := (1 : ℝ)) (ai := I.af 0) (aj := I.af 2)
      (ak := I.af 1) hm0 hm2 hm1 ha0 ha2 ha1 (by norm_num) hik
    rcases le_total (m 0) (m 1) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{1, 2}, h12, ?_⟩
      rw [e12, Fin.sum_univ_three]
      norm_num at core
      linarith
    · rw [min_eq_right hmin] at core
      refine ⟨{0, 2}, h02, ?_⟩
      rw [e02, Fin.sum_univ_three]
      norm_num at core
      linarith
  · have hik : 1 ≤ (1 : ℝ) * (I.af 0 + I.af 1) := by
      simpa using (I.blocked_af01_lt h01).le
    have hjk : 1 ≤ (1 : ℝ) * (I.af 2 + I.af 1) := by
      have h := (I.blocked_af12_lt h12).le
      nlinarith
    have core := weight_core_b (r := (1 : ℝ)) (ai := I.af 0) (aj := I.af 2)
      (ak := I.af 1) hm0 hm2 hm1 ha0 ha2 ha1 (by norm_num) hik hjk
    rcases le_total (m 0 + m 2) (m 1) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{1}, I.admissible_singleton 1, ?_⟩
      rw [e1, Fin.sum_univ_three]
      norm_num at core
      linarith
    · rw [min_eq_right hmin] at core
      refine ⟨{0, 2}, h02, ?_⟩
      rw [e02, Fin.sum_univ_three]
      norm_num at core
      linarith
  · have hik : 1 ≤ (1 : ℝ) * (I.af 1 + I.af 0) := by
      have h := (I.blocked_af01_lt h01).le
      nlinarith
    have hjk : 1 ≤ (1 : ℝ) * (I.af 2 + I.af 0) := by
      have h := (I.blocked_af02_lt h02).le
      nlinarith
    have core := weight_core_b (r := (1 : ℝ)) (ai := I.af 1) (aj := I.af 2)
      (ak := I.af 0) hm1 hm2 hm0 ha1 ha2 ha0 (by norm_num) hik hjk
    rcases le_total (m 1 + m 2) (m 0) with hmin | hmin
    · rw [min_eq_left hmin] at core
      refine ⟨{0}, I.admissible_singleton 0, ?_⟩
      rw [e0, Fin.sum_univ_three]
      norm_num at core
      linarith
    · rw [min_eq_right hmin] at core
      refine ⟨{1, 2}, h12, ?_⟩
      rw [e12, Fin.sum_univ_three]
      norm_num at core
      linarith
  · have r01 : 1 < rhoStar * (I.af 0 + I.af 1) :=
      lift_pair_lt _ (I.blocked_af01_lt h01)
    have r02 : 1 < rhoStar * (I.af 0 + I.af 2) :=
      lift_pair_lt _ (I.blocked_af02_lt h02)
    have r12 : 1 < rhoStar * (I.af 1 + I.af 2) :=
      lift_pair_lt _ (I.blocked_af12_lt h12)
    have rsum : 2 < rhoStar * (I.af 0 + I.af 1 + I.af 2) :=
      lift_sum_lt _ (I.all_blocked_af_lt h01 h12 h02)
    rcases le_total (m 0) (m 1) with hab | hab
    · rcases le_total (m 1) (m 2) with hbc | hbc
      · have core := weight_core_a_lt (r := rhoStar) (a1 := I.af 1) (a2 := I.af 0)
          (a3 := I.af 2) (m1 := m 1) (m2 := m 0) (m3 := m 2)
          hm0 hab hbc ha2 hρ0 r12
          (by simpa only [add_comm, add_left_comm, add_assoc] using rsum)
          (by simpa only [add_comm, add_left_comm, add_assoc] using hW)
        refine ⟨{2}, I.admissible_singleton 2, ?_⟩
        rw [e2, Fin.sum_univ_three]
        linarith
      · rcases le_total (m 0) (m 2) with hac | hac
        · have core := weight_core_a_lt (r := rhoStar) (a1 := I.af 2)
            (a2 := I.af 0) (a3 := I.af 1) (m1 := m 2) (m2 := m 0) (m3 := m 1)
            hm0 hac hbc ha1 hρ0
            (by simpa only [add_comm] using r12)
            (by simpa only [add_comm, add_left_comm, add_assoc] using rsum)
            (by simpa only [add_comm, add_left_comm, add_assoc] using hW)
          refine ⟨{1}, I.admissible_singleton 1, ?_⟩
          rw [e1, Fin.sum_univ_three]
          linarith
        · have core := weight_core_a_lt (r := rhoStar) (a1 := I.af 0)
            (a2 := I.af 2) (a3 := I.af 1) (m1 := m 0) (m2 := m 2) (m3 := m 1)
            hm2 hac hab ha1 hρ0 r01
            (by simpa only [add_comm, add_left_comm, add_assoc] using rsum)
            (by simpa only [add_comm, add_left_comm, add_assoc] using hW)
          refine ⟨{1}, I.admissible_singleton 1, ?_⟩
          rw [e1, Fin.sum_univ_three]
          linarith
    · rcases le_total (m 0) (m 2) with hac | hac
      · have core := weight_core_a_lt (r := rhoStar) (a1 := I.af 0) (a2 := I.af 1)
          (a3 := I.af 2) (m1 := m 0) (m2 := m 1) (m3 := m 2)
          hm1 hab hac ha2 hρ0 r02 rsum hW
        refine ⟨{2}, I.admissible_singleton 2, ?_⟩
        rw [e2, Fin.sum_univ_three]
        linarith
      · rcases le_total (m 1) (m 2) with hbc | hbc
        · have core := weight_core_a_lt (r := rhoStar) (a1 := I.af 2)
            (a2 := I.af 1) (a3 := I.af 0) (m1 := m 2) (m2 := m 1) (m3 := m 0)
            hm1 hbc hac ha0 hρ0
            (by simpa only [add_comm] using r02)
            (by simpa only [add_comm, add_left_comm, add_assoc] using rsum)
            (by simpa only [add_comm, add_left_comm, add_assoc] using hW)
          refine ⟨{0}, I.admissible_singleton 0, ?_⟩
          rw [e0, Fin.sum_univ_three]
          linarith
        · have core := weight_core_a_lt (r := rhoStar) (a1 := I.af 1)
            (a2 := I.af 2) (a3 := I.af 0) (m1 := m 1) (m2 := m 2) (m3 := m 0)
            hm2 hbc hab ha0 hρ0
            (by simpa only [add_comm] using r01)
            (by simpa only [add_comm, add_left_comm, add_assoc] using rsum)
            (by simpa only [add_comm, add_left_comm, add_assoc] using hW)
          refine ⟨{0}, I.admissible_singleton 0, ?_⟩
          rw [e0, Fin.sum_univ_three]
          linarith

/-! ### The reduction to nonnegative savings (Lemma 4) and the upper bound -/

/-- `fcost = base + Σᵢ afᵢ·savᵢ` (division form of `fcost_eq_base`).
@isnad1 id=eq.0h1v.s7.bfe803851b38 from=translated src=- shape=6dd2a8f7 vocab=c23ec8b7
-/
theorem fcost_af :
    I.fcost = I.base +
      (I.af 0 * I.sav 0 + I.af 1 * I.sav 1 + I.af 2 * I.sav 2) := by
  have key : ∀ i, I.af i * I.sav i = (I.d i - I.f i) * (I.WE i - I.WZ i) := by
    intro i
    have hd := (I.d_pos i).ne'
    rw [af, sav]
    field_simp
  rw [fcost_eq_base, Fin.sum_univ_three, ← key 0, ← key 1, ← key 2]

/-- **Theorem A, upper bound** (`ρ(H*) ≤ ρ*`): every SSUF instance on `H*`
admits an admissible unsplittable routing of cost at most
`ρ* = 2/(2√2 - 1)` times the fractional cost.
@isnad1 id=ex.0h1v.s5.6493ab57ed40 from=translated src=- shape=3e118fb1 vocab=333e21b9
-/
theorem exists_admissible_ucost_le :
    ∃ S : Finset Terminal, I.Admissible S ∧ I.ucost S ≤ rhoStar * I.fcost := by
  classical
  set m : Terminal → ℝ := fun i => max (I.sav i) 0 with hm_def
  have hm : ∀ i, 0 ≤ m i := fun i => le_max_right _ _
  obtain ⟨S, hSadm, hSw⟩ := I.exists_admissible_weight m hm
  set S' : Finset Terminal := S.filter (fun i => 0 ≤ I.sav i) with hS'_def
  have hS'sub : S' ⊆ S := Finset.filter_subset _ _
  refine ⟨S', I.admissible_mono hS'sub hSadm, ?_⟩
  have hρ1 : (1 : ℝ) ≤ rhoStar := one_le_rhoStar
  -- pointwise absorption of the negative savings parts
  have hP : ∀ i : Terminal, (if i ∈ S' then 0 else I.sav i) ≤
      (if i ∈ S then 0 else m i) + (rhoStar - 1) * (I.d i * I.WZ i) +
        rhoStar * (I.af i * min (I.sav i) 0) := by
    intro i
    have hdWZ : 0 ≤ I.d i * I.WZ i := mul_nonneg (I.d_pos i).le (I.WZ_nonneg i)
    have hsavlow := I.sav_lower i
    have haf0 := I.af_nonneg i
    have haf1 := I.af_le_one i
    by_cases hiS' : i ∈ S'
    · have hiS : i ∈ S := hS'sub hiS'
      have hsav0 : 0 ≤ I.sav i := (Finset.mem_filter.mp hiS').2
      simp only [hiS', hiS, ite_true]
      rw [min_eq_right hsav0]
      nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ rhoStar - 1) hdWZ]
    · simp only [hiS', ite_false]
      by_cases hiS : i ∈ S
      · have hsavneg : I.sav i < 0 :=
          lt_of_not_ge fun hpos => hiS' (Finset.mem_filter.mpr ⟨hiS, hpos⟩)
        simp only [hiS, ite_true]
        rw [min_eq_left hsavneg.le]
        rcases le_total (rhoStar * I.af i) 1 with hra | hra
        · nlinarith [mul_nonneg (sub_nonneg.2 hra) (neg_nonneg.2 hsavneg.le),
            mul_nonneg (by linarith : (0:ℝ) ≤ rhoStar - 1) hdWZ]
        · have t1 : 0 ≤ (I.d i * I.WZ i + I.sav i) * (rhoStar * I.af i - 1) :=
            mul_nonneg (by linarith) (by linarith)
          have t2 : 0 ≤ (I.d i * I.WZ i) * (rhoStar * (1 - I.af i)) :=
            mul_nonneg hdWZ (mul_nonneg (by linarith) (by linarith))
          nlinarith [t1, t2]
      · simp only [hiS, ite_false]
        rcases le_total 0 (I.sav i) with hsav | hsav
        · have hmi : m i = I.sav i := max_eq_left hsav
          rw [min_eq_right hsav, hmi]
          nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ rhoStar - 1) hdWZ]
        · have hmi : m i = 0 := max_eq_right hsav
          rw [min_eq_left hsav, hmi]
          rcases le_total (rhoStar * I.af i) 1 with hra | hra
          · nlinarith [mul_nonneg (sub_nonneg.2 hra) (neg_nonneg.2 hsav),
              mul_nonneg (by linarith : (0:ℝ) ≤ rhoStar - 1) hdWZ]
          · have t1 : 0 ≤ (I.d i * I.WZ i + I.sav i) * (rhoStar * I.af i - 1) :=
              mul_nonneg (by linarith) (by linarith)
            have t2 : 0 ≤ (I.d i * I.WZ i) * (rhoStar * (1 - I.af i)) :=
              mul_nonneg hdWZ (mul_nonneg (by linarith) (by linarith))
            nlinarith [t1, t2]
  -- combine: sum the pointwise bounds, apply the weight inequality
  have hid' : ∀ i : Terminal, rhoStar * (I.af i * I.sav i) =
      rhoStar * (I.af i * m i) + rhoStar * (I.af i * min (I.sav i) 0) := by
    intro i
    have hsum : m i + min (I.sav i) 0 = I.sav i := by
      rw [hm_def]
      dsimp only
      rw [max_add_min, add_zero]
    linear_combination (-(rhoStar * I.af i)) * hsum
  have hbase : I.base = I.d 0 * I.WZ 0 + I.d 1 * I.WZ 1 + I.d 2 * I.WZ 2 := by
    rw [base, Fin.sum_univ_three]
  have hbase' : rhoStar * I.base =
      rhoStar * (I.d 0 * I.WZ 0) + rhoStar * (I.d 1 * I.WZ 1) +
        rhoStar * (I.d 2 * I.WZ 2) := by
    rw [hbase]
    ring
  rw [ucost_eq_base, Fin.sum_univ_three, fcost_af]
  rw [Fin.sum_univ_three, Fin.sum_univ_three] at hSw
  linarith [hP 0, hP 1, hP 2, hSw, hid' 0, hid' 1, hid' 2, hbase, hbase']

/-- The negative-saving part of the signed reduction, isolated from the
routing choice. Its contribution together with the all-cheap base is at
most `ρ*` times the corresponding fractional-flow contribution.
@isnad1 id=le.0h1v.s6.6543fc80cfe7 from=translated src=- shape=b00fc000 vocab=3616829a
-/
theorem base_negative_savings_le :
    I.base + ∑ i, min (I.sav i) 0 ≤
      rhoStar * (I.base + ∑ i, I.af i * min (I.sav i) 0) := by
  have hρ1 : (1 : ℝ) ≤ rhoStar := one_le_rhoStar
  have hq : ∀ i : Terminal,
      min (I.sav i) 0 ≤
        (rhoStar - 1) * (I.d i * I.WZ i) +
          rhoStar * (I.af i * min (I.sav i) 0) := by
    intro i
    have hb0 : 0 ≤ I.d i * I.WZ i :=
      mul_nonneg (I.d_pos i).le (I.WZ_nonneg i)
    have hn0 : min (I.sav i) 0 ≤ 0 := min_le_right _ _
    have hnlower : -(I.d i * I.WZ i) ≤ min (I.sav i) 0 :=
      le_min (I.sav_lower i) (neg_nonpos.mpr hb0)
    have ha0 := I.af_nonneg i
    have ha1 := I.af_le_one i
    rcases le_total (rhoStar * I.af i) 1 with hra | hra
    · have t1 : 0 ≤ (1 - rhoStar * I.af i) * (-min (I.sav i) 0) :=
        mul_nonneg (by linarith) (neg_nonneg.mpr hn0)
      have t2 : 0 ≤ (rhoStar - 1) * (I.d i * I.WZ i) :=
        mul_nonneg (by linarith) hb0
      nlinarith
    · have t1 : 0 ≤ (I.d i * I.WZ i + min (I.sav i) 0) *
          (rhoStar * I.af i - 1) :=
        mul_nonneg (by linarith) (by linarith)
      have t2 : 0 ≤ (I.d i * I.WZ i) * (rhoStar * (1 - I.af i)) :=
        mul_nonneg hb0 (mul_nonneg rhoStar_pos.le (by linarith))
      nlinarith
  have hsum := Finset.sum_le_sum fun i (_ : i ∈ Finset.univ) => hq i
  simp only [Fin.sum_univ_three] at hsum
  rw [base]
  simp only [Fin.sum_univ_three]
  ring_nf at hsum ⊢
  linarith

/-- **Theorem A, strict upper bound.** Every positive-cost SSUF instance on
`H*` has an admissible unsplittable routing whose cost is strictly below
`ρ*` times the fractional cost. Consequently the sharp supremum is not
attained by any finite instance.
@isnad1 id=ex.1h1v.s5.7d6ebd8c70d3 from=translated src=- shape=60cba97d vocab=0cf27cd2
-/
theorem exists_admissible_ucost_lt (hfc : 0 < I.fcost) :
    ∃ S : Finset Terminal, I.Admissible S ∧ I.ucost S < rhoStar * I.fcost := by
  classical
  set m : Terminal → ℝ := fun i => max (I.sav i) 0 with hm_def
  set n : Terminal → ℝ := fun i => min (I.sav i) 0 with hn_def
  have hm : ∀ i, 0 ≤ m i := fun i => le_max_right _ _
  have hn : ∀ i, n i ≤ 0 := fun i => by
    rw [hn_def]
    exact min_le_right _ _
  have hsav : ∀ i, I.sav i = m i + n i := by
    intro i
    rw [hm_def, hn_def, max_add_min, add_zero]
  have hW0 : 0 ≤ ∑ i, m i * I.af i :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hm i) (I.af_nonneg i)
  have hfdec : I.fcost =
      I.base + (∑ i, m i * I.af i) + (∑ i, I.af i * n i) := by
    rw [fcost_af]
    simp only [Fin.sum_univ_three]
    rw [hsav 0, hsav 1, hsav 2]
    ring
  have hNV : (∑ i, n i) ≤ ∑ i, I.af i * n i := by
    apply Finset.sum_le_sum
    intro i _
    have t : (1 - I.af i) * n i ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr (I.af_le_one i)) (hn i)
    nlinarith
  by_cases hW : (∑ i, m i * I.af i) = 0
  · obtain ⟨S, hSadm, hSw⟩ := I.exists_admissible_weight m hm
    set S' : Finset Terminal := S.filter (fun i => 0 ≤ I.sav i) with hS'_def
    have hS'sub : S' ⊆ S := Finset.filter_subset _ _
    refine ⟨S', I.admissible_mono hS'sub hSadm, ?_⟩
    have hid : ∀ i : Terminal,
        (if i ∈ S' then 0 else I.sav i) =
          (if i ∈ S then 0 else m i) + n i := by
      intro i
      by_cases hiS : i ∈ S
      · by_cases hs : 0 ≤ I.sav i
        · simp [hS'_def, hiS, hs, hn_def]
        · have hs' : I.sav i ≤ 0 := (lt_of_not_ge hs).le
          simp [hS'_def, hiS, hs, hn_def, hs']
      · by_cases hs : 0 ≤ I.sav i
        · simp [hS'_def, hiS, hs, hm_def, hn_def]
        · have hs' : I.sav i ≤ 0 := (lt_of_not_ge hs).le
          simp [hS'_def, hiS, hs, hm_def, hn_def, hs']
    have hsumid :
        (∑ i, if i ∈ S' then 0 else I.sav i) =
          (∑ i, if i ∈ S then 0 else m i) + ∑ i, n i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hid i
    have hfcρ : I.fcost < rhoStar * I.fcost := by
      have hp := mul_pos (sub_pos.mpr one_lt_rhoStar) hfc
      nlinarith
    rw [hW, mul_zero] at hSw
    rw [ucost_eq_base, hsumid]
    nlinarith [hSw, hNV, hfdec, hfcρ]
  · have hWpos : 0 < ∑ i, m i * I.af i := lt_of_le_of_ne hW0 (Ne.symm hW)
    obtain ⟨S, hSadm, hSw⟩ := I.exists_admissible_weight_lt m hm hWpos
    set S' : Finset Terminal := S.filter (fun i => 0 ≤ I.sav i) with hS'_def
    have hS'sub : S' ⊆ S := Finset.filter_subset _ _
    refine ⟨S', I.admissible_mono hS'sub hSadm, ?_⟩
    have hid : ∀ i : Terminal,
        (if i ∈ S' then 0 else I.sav i) =
          (if i ∈ S then 0 else m i) + n i := by
      intro i
      by_cases hiS : i ∈ S
      · by_cases hs : 0 ≤ I.sav i
        · simp [hS'_def, hiS, hs, hn_def]
        · have hs' : I.sav i ≤ 0 := (lt_of_not_ge hs).le
          simp [hS'_def, hiS, hs, hn_def, hs']
      · by_cases hs : 0 ≤ I.sav i
        · simp [hS'_def, hiS, hs, hm_def, hn_def]
        · have hs' : I.sav i ≤ 0 := (lt_of_not_ge hs).le
          simp [hS'_def, hiS, hs, hm_def, hn_def, hs']
    have hsumid :
        (∑ i, if i ∈ S' then 0 else I.sav i) =
          (∑ i, if i ∈ S then 0 else m i) + ∑ i, n i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => hid i
    have hneg : I.base + ∑ i, n i ≤
        rhoStar * (I.base + ∑ i, I.af i * n i) := by
      simpa [hn_def] using I.base_negative_savings_le
    rw [ucost_eq_base, hsumid]
    calc
      I.base + ((∑ i, if i ∈ S then 0 else m i) + ∑ i, n i) <
          rhoStar * (∑ i, m i * I.af i) +
            rhoStar * (I.base + ∑ i, I.af i * n i) := by
              linarith
      _ = rhoStar * I.fcost := by rw [hfdec]; ring

end FlowInstance

end Goemans
