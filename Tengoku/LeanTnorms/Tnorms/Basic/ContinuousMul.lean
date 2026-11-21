/-
Copyright (c) 2026 Noah Walker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Noah Walker
-/

import Tengoku
import Tengoku.LeanTnorms.Tnorms.Basic.Defs

/-!
Here we prove that multiplication on a t-norm is continuous if and only if it is left adn right
  continuous. The `ConditionallyCompleteLinearOrder` assumption can't be weakened.  See the
  counterexample in the Counterexamples folder.

TODO:
  * We should be able to dualize things better after #41558 is merged
-/
namespace Tengoku.LeanTnorms end Tengoku.LeanTnorms open Tengoku.LeanTnorms
section LeftRightContinuousMul
local infixl:60 " ⇒ " => LImp


variable {M : Type*} [TopologicalSpace M] [ConditionallyCompleteLinearOrder M] [OrderTopology M]

private lemma aux_sInf_eq_sInf {x : ℕ → M} {p r : M}
    (hx : Filter.Tendsto x Filter.atTop (nhds p)) (n m : ℕ)
    (hr : sInf (x '' Set.Ici n) < r)
    (h : ∀ k, m ≤ k → r < x k) :
    sInf (x '' Set.Ici n) = sInf (x '' Set.Ico n m) := by
  refine csInf_eq_csInf_of_forall_exists_le ?_ ?_
  · simp only [Set.mem_image, Set.mem_Ici, Set.mem_Ico, exists_exists_and_eq_and,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    contrapose! hr
    rw [le_csInf_iff]
    · grind
    · exact BddBelow.mono (by simp) (Filter.Tendsto.bddBelow_range hx)
    · simp
  · simp
    grind

private lemma exists_index_eq_sInf_of_lt_limit {x : ℕ → M} {p : M}
    (hx : Filter.Tendsto x Filter.atTop (nhds p)) (n : ℕ)
    (hs : sInf (x '' Set.Ici n) < p) :
    ∃ k ∈ Set.Ici n, x k = sInf (x '' Set.Ici n) := by
  by_cases! hpq : ∃ r, sInf (x '' Set.Ici n) < r ∧ r < p
  · obtain ⟨r, hqr, hrp⟩ := hpq
    have hx₀ := hx
    rw [tendsto_order] at hx
    obtain ⟨hx, hx'⟩ := hx
    have hx'' := hx r hrp
    rw [Filter.eventually_atTop] at hx''
    obtain ⟨m, hm⟩ := hx''
    have hnm : n < m := by
      contrapose! hm
      apply exists_lt_of_csInf_lt at hqr
      · grind
      · simp
    rw [aux_sInf_eq_sInf hx₀ n m hqr hm]
    suffices sInf (x '' Set.Ico n m) ∈ x '' Set.Ico n m by grind
    refine Set.Nonempty.csInf_mem ?_ ?_
    · simp [hnm]
    · exact Set.Finite.image _ (Set.finite_Ico _ _)
  · contrapose! hs
    refine le_csInf (by simp) ?_
    simp only [Set.mem_image, Set.mem_Ici, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro k hnk
    specialize hs k
    have hxk : sInf (x '' Set.Ici n) ≤ x k := by
      refine csInf_le ?_ (by grind)
      exact BddBelow.mono (by simp) (Filter.Tendsto.bddBelow_range hx)
    grind

private lemma aux_mono_of_tendsto {x : ℕ → M} {p : M}
    (hx : Filter.Tendsto x Filter.atTop (nhds p)) :
    Monotone (fun n ↦ sInf (x '' Set.Ici n)) := by
  intro n k hnk
  refine csInf_le_csInf ?_ (by simp) <| Set.image_mono <| by grind
  exact BddBelow.mono (by simp) (Filter.Tendsto.bddBelow_range hx)

private lemma aux_le_of_tendsto {x : ℕ → M} {p : M} (hx : Filter.Tendsto x Filter.atTop (nhds p))
    (n : ℕ) :
    sInf (x '' Set.Ici n) ≤ x n := by
  refine csInf_le ?_ (by grind)
  exact BddBelow.mono (by simp) (Filter.Tendsto.bddBelow_range hx)

private lemma aux_tendsto_sInf_of_tendsto {x : ℕ → M} {p : M}
    (hx : Filter.Tendsto x Filter.atTop (nhds p)) :
    Filter.Tendsto (fun n ↦ sInf (x '' Set.Ici n)) Filter.atTop (nhds p) := by
  have hx₀ := hx
  simp only [tendsto_order, Filter.eventually_atTop, gt_iff_lt] at hx ⊢
  obtain ⟨hx, hx'⟩ := hx
  constructor
  · intro q hqp
    specialize hx q hqp
    obtain ⟨k, hx⟩ := hx
    use k
    intro m hmk
    by_cases! hap : sInf (x '' Set.Ici m) ≥ p
    · grind
    · obtain ⟨l, hl, hla⟩ := exists_index_eq_sInf_of_lt_limit hx₀ m hap
      grind
  · intro q hpq
    specialize hx' q hpq
    obtain ⟨k, hk⟩ := hx'
    use k
    intro m hkm
    specialize hk m hkm
    refine csInf_lt_of_lt ?_ (by grind) hk
    exact BddBelow.mono (by simp) (Filter.Tendsto.bddBelow_range hx₀)

lemma _root_.Tengoku.LeanTnorms.mono_of_tendsto {x : ℕ → M} {p : M} (hx : Filter.Tendsto x Filter.atTop (nhds p)) :
    ∃ a : ℕ → M, Monotone a ∧ (∀ n : ℕ, (a n) ≤ (x n)) ∧
    Filter.Tendsto a Filter.atTop (nhds p) := by
  use (fun n ↦ sInf (x '' Set.Ici n))
  constructorm* _ ∧ _
  · exact aux_mono_of_tendsto hx
  · exact aux_le_of_tendsto hx
  · exact aux_tendsto_sInf_of_tendsto hx

lemma _root_.Tengoku.LeanTnorms.mono_of_tendsto' {x : ℕ → M} {p q : M} (hxq : ∀ n, q < x n)
    (hx : Filter.Tendsto x Filter.atTop (nhds p)) :
    ∃ a : ℕ → M, Monotone a ∧ (∀ n : ℕ, a n ≤ x n) ∧ (∀ n, q ≤ a n) ∧
    Filter.Tendsto a Filter.atTop (nhds p) := by
  use (fun n ↦ sInf (x '' Set.Ici n))
  constructorm* _ ∧ _
  · exact aux_mono_of_tendsto hx
  · exact aux_le_of_tendsto hx
  · intro n
    exact le_csInf (by simp) (by grind)
  · exact aux_tendsto_sInf_of_tendsto hx

private lemma aux_sSup_eq_sSup {x : ℕ → M} {p r : M}
    (hx : Filter.Tendsto x Filter.atTop (nhds p)) (n m : ℕ)
    (hr : sSup (x '' Set.Ici n) > r)
    (h : ∀ k, m ≤ k → r > x k) :
    sSup (x '' Set.Ici n) = sSup (x '' Set.Ico n m) := by
  refine csSup_eq_csSup_of_forall_exists_le ?_ ?_
  · simp only [Set.mem_image, Set.mem_Ici, Set.mem_Ico, exists_exists_and_eq_and,
      forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    contrapose! hr
    rw [csSup_le_iff]
    · grind
    · exact BddAbove.mono (by simp) (Filter.Tendsto.bddAbove_range hx)
    · simp
  · simp
    grind

private lemma exists_index_eq_sSup_of_limit_lt
    {x : ℕ → M} {p : M}
    (hx : Filter.Tendsto x Filter.atTop (nhds p)) (n : ℕ)
    (hs : p < sSup (x '' Set.Ici n)) :
    ∃ k ∈ Set.Ici n, x k = sSup (x '' Set.Ici n) := by
  let q := sSup (x '' Set.Ici n)
  by_cases! hpq : ∃ r, q > r ∧ r > p
  · obtain ⟨r, hqr, hrp⟩ := hpq
    have hx₀ := hx
    rw [tendsto_order] at hx
    obtain ⟨hx, hx'⟩ := hx
    have hx'' := hx' r hrp
    rw [Filter.eventually_atTop] at hx''
    obtain ⟨m, hm⟩ := hx''
    have hnm : n < m := by
      contrapose! hm
      apply exists_lt_of_lt_csSup at hqr
      · grind
      · simp
    rw [aux_sSup_eq_sSup hx₀ n m hqr hm]
    suffices sSup (x '' Set.Ico n m) ∈ x '' Set.Ico n m by grind
    refine Set.Nonempty.csSup_mem ?_ ?_
    · simp [hnm]
    · exact Set.Finite.image _ (Set.finite_Ico _ _)
  · contrapose! hs
    refine csSup_le (by simp) ?_
    simp only [Set.mem_image, Set.mem_Ici, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
    intro k hnk
    specialize hs k
    have hxk : x k ≤ sSup (x '' Set.Ici n)  := by
      refine le_csSup ?_ (by grind)
      exact BddAbove.mono (by simp) (Filter.Tendsto.bddAbove_range hx)
    grind

private lemma aux_anti_of_tendsto {x : ℕ → M} {p : M}
    (hx : Filter.Tendsto x Filter.atTop (nhds p)) :
    Antitone (fun n ↦ sSup (x '' Set.Ici n)) := by
  intro n k hnk
  refine csSup_le_csSup ?_ (by simp) <| Set.image_mono <| by grind
  exact BddAbove.mono (by simp) (Filter.Tendsto.bddAbove_range hx)

private lemma aux_ge_of_tendsto {x : ℕ → M} {p : M} (hx : Filter.Tendsto x Filter.atTop (nhds p))
    (n : ℕ) :
    x n ≤ sSup (x '' Set.Ici n) := by
  refine le_csSup ?_ (by grind)
  exact BddAbove.mono (by simp) (Filter.Tendsto.bddAbove_range hx)

private lemma aux_tendsto_sSup_of_tendsto {x : ℕ → M} {p : M}
    (hx : Filter.Tendsto x Filter.atTop (nhds p)) :
    Filter.Tendsto (fun n ↦ sSup (x '' Set.Ici n)) Filter.atTop (nhds p) := by
  have hx₀ := hx
  simp only [tendsto_order, Filter.eventually_atTop, gt_iff_lt] at hx ⊢
  obtain ⟨hx, hx'⟩ := hx
  constructor
  · intro q hqp
    specialize hx q hqp
    obtain ⟨k, hk⟩ := hx
    use k
    intro m hmk
    specialize hk m hmk
    refine lt_csSup_of_lt ?_ (by grind) hk
    exact BddAbove.mono (by simp) (Filter.Tendsto.bddAbove_range hx₀)
  · intro q hpq
    specialize hx' q hpq
    obtain ⟨k, hk⟩ := hx'
    use k
    intro m hkm
    by_cases! hap : sSup (x '' Set.Ici m) ≤ p
    · grind
    · obtain ⟨l, hl, hla⟩ := exists_index_eq_sSup_of_limit_lt hx₀ m hap
      grind

lemma _root_.Tengoku.LeanTnorms.anti_of_tendsto {x : ℕ → M} {p : M} (hx : Filter.Tendsto x Filter.atTop (nhds p)) :
    ∃ a : ℕ → M, Antitone a ∧ (∀ n : ℕ, (x n) ≤ (a n)) ∧
    Filter.Tendsto a Filter.atTop (nhds p) := by
  use (fun n => sSup (x '' Set.Ici n))
  constructorm* _ ∧ _
  · exact aux_anti_of_tendsto hx
  · exact aux_ge_of_tendsto hx
  · exact aux_tendsto_sSup_of_tendsto hx

instance [CommMonoid M] [FirstCountableTopology M] [IsOrderedMonoid M]
    [LeftContinuousMul M] [RightContinuousMul M] : ContinuousMul M where
  continuous_mul := by
    refine SeqContinuous.continuous ?_
    intro z (p, q) hz
    rw [Prod.tendsto_iff] at hz
    obtain ⟨hx, hy⟩ := hz
    let ⟨a, ha⟩ := mono_of_tendsto hx
    let ⟨b, hb⟩ := anti_of_tendsto hx
    let ⟨c, hc⟩ := mono_of_tendsto hy
    let ⟨d, hd⟩ := anti_of_tendsto hy
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le
      (monotone_continuous_mul _ a c p q ha.1 hc.1 ha.2.2 hc.2.2)
      (antitone_continuous_mul _ b d p q hb.1 hd.1 hb.2.2 hd.2.2)
    · intro n
      simp only [Function.comp_apply]
      exact mul_le_mul' (ha.2.1 n) (hc.2.1 n)
    · intro n
      simp only [Function.comp_apply]
      exact mul_le_mul' (hb.2.1 n) (hd.2.1 n)

end LeftRightContinuousMul

section ContinuousMul

variable {M : Type*} [TopologicalSpace M] [ConditionallyCompleteLinearOrder M]
    [CommMonoid M] [IsOrderedMonoid M] [OrderTopology M] [FirstCountableTopology M]

theorem _root_.Tengoku.LeanTnorms.continuousMul_iff_separatelyContinuousMul :
    ContinuousMul M ↔ SeparatelyContinuousMul M := by
  constructor
  · intro h
    infer_instance
  · intro ⟨h₁, h₂⟩
    refine ContinuousMul.mk ?_
    rw [continuous_iff_seqContinuous]
    intro z ⟨p, q⟩ hz
    rw [Prod.tendsto_iff] at hz
    obtain ⟨hx, hy⟩ := hz
    simp only [tendsto_order, Function.comp_apply, Filter.eventually_atTop, gt_iff_lt]
    obtain ⟨a, hao, haz, hat⟩ := mono_of_tendsto hx
    obtain ⟨b, hbo, hbz, hbt⟩ := anti_of_tendsto hx
    obtain ⟨c, hco, hcz, hct⟩ := mono_of_tendsto hy
    obtain ⟨d, hdo, hdz, hdt⟩ := anti_of_tendsto hy
    simp_rw [continuous_iff_seqContinuous] at h₁ h₂
    specialize h₁ (a := p)
    constructor
    · intro r hr
      have hc := h₁ hct
      simp only [tendsto_order, Function.comp_apply, Filter.eventually_atTop, gt_iff_lt] at hc
      obtain ⟨N, hc⟩ := hc.1 r hr
      have ha := h₂ (a := c N) hat
      simp only [tendsto_order, Function.comp_apply, Filter.eventually_atTop, gt_iff_lt] at ha
      obtain ⟨M, ha⟩ := ha.1 r (by grind)
      use N ⊔ M
      intro n hn
      refine lt_of_lt_of_le (ha n (by grind)) ?_
      exact mul_le_mul' (haz n) <| le_trans (hco (le_of_max_le_left hn)) (hcz n)
    · intro r hr
      have hd := h₁ hdt
      simp only [tendsto_order, Function.comp_apply, Filter.eventually_atTop, gt_iff_lt] at hd
      obtain ⟨N, hd⟩ := hd.2 r hr
      have hb := h₂ (a := d N) hbt
      simp only [tendsto_order, Function.comp_apply, Filter.eventually_atTop, gt_iff_lt] at hb
      obtain ⟨M, hb⟩ := hb.2 r (by grind)
      use N ⊔ M
      intro n hn
      refine lt_of_le_of_lt ?_ (hb n (by grind))
      exact mul_le_mul' (hbz n) <| le_trans (hdz n) (hdo (le_of_max_le_left hn))

theorem _root_.Tengoku.LeanTnorms.continuousMul_iff_leftRightContinuousMul :
    ContinuousMul M ↔ LeftContinuousMul M ∧ RightContinuousMul M :=
  ⟨fun _ ↦ ⟨inferInstance, inferInstance⟩, fun ⟨_, _⟩ ↦ inferInstance⟩

end ContinuousMul
-- Tengoku: root names of this library moved to Tengoku.LeanTnorms so they do not collide with other libraries (generated)
