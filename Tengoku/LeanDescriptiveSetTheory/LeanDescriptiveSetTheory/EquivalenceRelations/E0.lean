/-
Copyright (c) 2026 Lean Descriptive Set Theory contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lean Descriptive Set Theory contributors
-/

import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Borel.FiniteHierarchy
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.EquivalenceRelations.Reducibility
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.Spaces.Cylinders
import Tengoku.LeanDescriptiveSetTheory.LeanDescriptiveSetTheory.StandardBorel.Code
import Tengoku.Seed.Logic.Equiv.Bool
import Tengoku.Seed.Topology.Baire.BaireMeasurable
import Tengoku.Seed.Topology.Baire.Lemmas
import Tengoku.Seed.Topology.Baire.LocallyCompactRegular
import Tengoku.Seed.Topology.Homeomorph.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The eventual-equality relation `E₀`

This file completes the first canonical infinite countable Borel equivalence-relation example.
Eventual equality on Cantor space has an `Fσ` graph and countable classes.  Its nonsmoothness is
proved by the Baire-category argument: every Baire-measurable set invariant under finite changes
is meagre or comeagre, so a measurable complete invariant into Cantor space is constant on a
comeagre set.  Such a set cannot fit inside one meagre `E₀`-class.

The proof uses only finite prefix toggles.  It does not invoke the Glimm--Effros dichotomy or any
classification theorem stronger than the definition of smoothness.
-/

open Filter MeasurableSpace Set TopologicalSpace Topology

namespace DescriptiveSetTheory

/-- Pairs of Cantor points agreeing from coordinate `N` onward.-/
def eventualEqStage (N : ℕ) : Set ((ℕ → Bool) × (ℕ → Bool)) :=
  {p | ∀ n, N ≤ n → p.1 n = p.2 n}

/-- Points agreeing with `x` from coordinate `N` onward.-/
def eventualEqTail (x : ℕ → Bool) (N : ℕ) : Set (ℕ → Bool) :=
  {y | ∀ n, N ≤ n → x n = y n}

@[simp] theorem mem_eventualEqStage {N : ℕ} {x y : ℕ → Bool} :
    (x, y) ∈ eventualEqStage N ↔ ∀ n, N ≤ n → x n = y n :=
  Iff.rfl

@[simp] theorem mem_eventualEqTail {x y : ℕ → Bool} {N : ℕ} :
    y ∈ eventualEqTail x N ↔ ∀ n, N ≤ n → x n = y n :=
  Iff.rfl

/-- Every fixed-tail stage of `E₀` is closed.-/
theorem isClosed_eventualEqStage (N : ℕ) : IsClosed (eventualEqStage N) := by
  rw [show eventualEqStage N =
      ⋂ n, ⋂ (_h : N ≤ n), {p | p.1 n = p.2 n} by
    ext p
    simp [eventualEqStage]]
  exact isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
    isClosed_eq ((continuous_apply n).comp continuous_fst)
      ((continuous_apply n).comp continuous_snd)

/-- Every fixed tail class is closed.-/
theorem isClosed_eventualEqTail (x : ℕ → Bool) (N : ℕ) :
    IsClosed (eventualEqTail x N) := by
  rw [show eventualEqTail x N = ⋂ n, ⋂ (_h : N ≤ n), {y | x n = y n} by
    ext y
    simp [eventualEqTail]]
  exact isClosed_iInter fun n ↦ isClosed_iInter fun _ ↦
    isClosed_eq continuous_const (continuous_apply n)

/-- The graph of eventual equality is the union of its closed fixed-tail stages.-/
theorem equivalenceRelationGraph_eventualEq :
    equivalenceRelationGraph eventualEq = ⋃ N, eventualEqStage N := by
  ext p
  simp [equivalenceRelationGraph, eventualEq, eventualEqStage]

/-- The graph of `E₀` is `Fσ` (`Sigma0 2`).-/
theorem sigma0_two_equivalenceRelationGraph_eventualEq :
    Sigma0 2 (equivalenceRelationGraph eventualEq) := by
  refine sigma0_two_iff_eq_iUnion_isClosed.2 ⟨eventualEqStage, ?_, ?_⟩
  · exact isClosed_eventualEqStage
  · exact equivalenceRelationGraph_eventualEq

/-- Eventual equality has a Borel graph.-/
theorem isBorelRelation_eventualEq : IsBorelRelation eventualEq :=
  show MeasurableSet (equivalenceRelationGraph eventualEq) from by
    rw [show (Prod.instMeasurableSpace : MeasurableSpace ((ℕ → Bool) × (ℕ → Bool))) =
      borel ((ℕ → Bool) × (ℕ → Bool)) from BorelSpace.measurable_eq]
    exact sigma0_two_equivalenceRelationGraph_eventualEq.measurableSet

/-- Replace the first `N` coordinates of `x` with a finite Boolean prefix.-/
def overwritePrefix (x : ℕ → Bool) {N : ℕ} (p : Fin N → Bool) : ℕ → Bool :=
  fun n ↦ if h : n < N then p ⟨n, h⟩ else x n

/-- A fixed tail class is covered by the finite-prefix replacements of its center.-/
theorem eventualEqTail_subset_range_overwritePrefix (x : ℕ → Bool) (N : ℕ) :
    eventualEqTail x N ⊆ Set.range (overwritePrefix x : (Fin N → Bool) → ℕ → Bool) := by
  intro y hy
  let p : Fin N → Bool := fun i ↦ y i
  refine ⟨p, funext fun n ↦ ?_⟩
  by_cases hn : n < N
  · simp [overwritePrefix, p, hn]
  · simp [overwritePrefix, hn, hy n (Nat.le_of_not_gt hn)]

/-- Every fixed tail class is countable (in fact finite).-/
theorem countable_eventualEqTail (x : ℕ → Bool) (N : ℕ) :
    (eventualEqTail x N).Countable :=
  (Set.countable_range (overwritePrefix x : (Fin N → Bool) → ℕ → Bool)).mono
    (eventualEqTail_subset_range_overwritePrefix x N)

/-- An `E₀`-class is the countable union of its fixed-tail pieces.-/
theorem equivalenceClass_eventualEq (x : ℕ → Bool) :
    equivalenceClass eventualEq x = ⋃ N, eventualEqTail x N := by
  ext y
  simp [equivalenceClass, eventualEq, eventualEqTail]

/-- Every `E₀`-class is countable.-/
theorem hasCountableClasses_eventualEq : HasCountableClasses eventualEq := by
  intro x
  rw [equivalenceClass_eventualEq]
  exact Set.countable_iUnion (countable_eventualEqTail x)

/-- Eventual equality is a countable Borel equivalence relation.-/
theorem isCountableBorelEquivalenceRelation_eventualEq :
    IsCountableBorelEquivalenceRelation eventualEq :=
  ⟨eventualEq_equivalence, isBorelRelation_eventualEq, hasCountableClasses_eventualEq⟩

/-- Each fixed-tail piece has empty interior, hence is nowhere dense.-/
theorem isNowhereDense_eventualEqTail (x : ℕ → Bool) (N : ℕ) :
    IsNowhereDense (eventualEqTail x N) := by
  rw [(isClosed_eventualEqTail x N).isNowhereDense_iff,
    interior_eq_empty_iff_dense_compl, dense_iff_inter_open]
  intro U hU hUne
  rcases hUne with ⟨z, hzU⟩
  rcases isTopologicalBasis_cantorCylinderBasis.exists_subset_of_mem_open hzU hU with
    ⟨C, ⟨c, k, rfl⟩, hzC, hCU⟩
  let m := max N k
  let y : ℕ → Bool := Function.update z m (!x m)
  have hyC : y ∈ PiNat.cylinder c k := by
    rw [PiNat.mem_cylinder_iff] at hzC ⊢
    intro i hi
    have him : i ≠ m := ne_of_lt (hi.trans_le (Nat.le_max_right N k))
    have hyi : y i = z i := by
      simp [y, him]
    rw [hyi]
    exact hzC i hi
  have hyTail : y ∉ eventualEqTail x N := by
    intro hy
    have hm := hy m (Nat.le_max_left N k)
    simp [y] at hm
  exact ⟨y, hCU hyC, hyTail⟩

/-- Every `E₀`-class is meagre.-/
theorem isMeagre_equivalenceClass_eventualEq (x : ℕ → Bool) :
    IsMeagre (equivalenceClass eventualEq x) := by
  rw [equivalenceClass_eventualEq]
  exact isMeagre_iUnion fun N ↦ (isNowhereDense_eventualEqTail x N).isMeagre

/-- Toggle a Boolean coordinate when the control bit is true.-/
def toggleBit (d b : Bool) : Bool :=
  if d then !b else b

@[simp] theorem toggleBit_false (b : Bool) : toggleBit false b = b := rfl

@[simp] theorem toggleBit_true (b : Bool) : toggleBit true b = !b := rfl

theorem toggleBit_involutive (d : Bool) : Function.Involutive (toggleBit d) := by
  intro b
  cases d <;> simp [toggleBit]

/-- Toggling by a fixed Boolean is an equivalence.-/
def toggleBitEquiv (d : Bool) : Bool ≃ Bool :=
  (toggleBit_involutive d).toPerm

/-- Toggling by a fixed Boolean is a homeomorphism of the discrete Boolean space.-/
def toggleBitHomeomorph (d : Bool) : Bool ≃ₜ Bool :=
  (toggleBitEquiv d).toHomeomorphOfDiscrete

/-- Toggle only the first `N` coordinates according to `d`.-/
def prefixToggle (N : ℕ) (d : Fin N → Bool) : (ℕ → Bool) ≃ₜ (ℕ → Bool) :=
  Homeomorph.piCongrRight fun n ↦
    toggleBitHomeomorph (if h : n < N then d ⟨n, h⟩ else false)

@[simp] theorem prefixToggle_apply (N : ℕ) (d : Fin N → Bool) (x : ℕ → Bool) (n : ℕ) :
    prefixToggle N d x n =
      toggleBit (if h : n < N then d ⟨n, h⟩ else false) (x n) :=
  rfl

/-- A finite prefix toggle changes only finitely many coordinates.-/
theorem eventualEq_prefixToggle (N : ℕ) (d : Fin N → Bool) (x : ℕ → Bool) :
    eventualEq x (prefixToggle N d x) := by
  refine ⟨N, fun n hn ↦ ?_⟩
  simp [prefixToggle_apply, Nat.not_lt.mpr hn]

/-- Some prefix toggle sends any point into any cylinder of the same length.-/
theorem exists_prefixToggle_mem_cylinder (c x : ℕ → Bool) (N : ℕ) :
    ∃ d : Fin N → Bool, prefixToggle N d x ∈ PiNat.cylinder c N := by
  let d : Fin N → Bool := fun i ↦ x i != c i
  refine ⟨d, ?_⟩
  rw [PiNat.mem_cylinder_iff]
  intro n hn
  simp only [prefixToggle_apply, dite_eq_left hn, d]
  cases x n <;> cases c n <;> simp [toggleBit]

/-- A set is invariant under `E₀` when finite coordinate changes preserve membership.-/
def IsEventualEqInvariant (s : Set (ℕ → Bool)) : Prop :=
  ∀ ⦃x y⦄, eventualEq x y → (x ∈ s ↔ y ∈ s)

/-- The category zero--one law for finite-change invariant sets with the Baire property.-/
theorem isMeagre_or_compl_isMeagre_of_baireMeasurable_eventualEqInvariant
    {s : Set (ℕ → Bool)} (hs : BaireMeasurableSet s) (hinv : IsEventualEqInvariant s) :
    IsMeagre s ∨ IsMeagre sᶜ := by
  rcases hs.residualEq_isOpen with ⟨U, hU, hsU⟩
  by_cases hUne : U.Nonempty
  · right
    rcases hUne with ⟨z, hzU⟩
    rcases isTopologicalBasis_cantorCylinderBasis.exists_subset_of_mem_open hzU hU with
      ⟨C, ⟨c, N, rfl⟩, _hzC, hCU⟩
    let bad : Set (ℕ → Bool) := {x | ¬ (x ∈ s ↔ x ∈ U)}
    have hbad : IsMeagre bad := by
      change badᶜ ∈ residual (ℕ → Bool)
      change ∀ᶠ x in residual (ℕ → Bool), x ∈ badᶜ
      filter_upwards [hsU.mem_iff] with x hx
      simpa [bad] using hx
    have hpre (d : Fin N → Bool) : IsMeagre ((prefixToggle N d) ⁻¹' bad) :=
      hbad.preimage_of_isOpenMap (prefixToggle N d).continuous (prefixToggle N d).isOpenMap
    refine (isMeagre_iUnion hpre).mono ?_
    intro x hxs
    simp only [mem_compl_iff, mem_iUnion] at hxs ⊢
    rcases exists_prefixToggle_mem_cylinder c x N with ⟨d, hd⟩
    refine ⟨d, ?_⟩
    change prefixToggle N d x ∈ bad
    have hnot : prefixToggle N d x ∉ s := by
      intro hmem
      exact hxs ((hinv (eventualEq_prefixToggle N d x)).2 hmem)
    intro hiff
    exact hnot (hiff.2 (hCU hd))
  · left
    change sᶜ ∈ residual (ℕ → Bool)
    have hUe : U = ∅ := not_nonempty_iff_eq_empty.mp hUne
    change ∀ᶠ x in residual (ℕ → Bool), x ∈ sᶜ
    filter_upwards [hsU.mem_iff] with x hx
    simpa [hUe] using hx

/-- A measurable complete invariant from `E₀` to Cantor equality is constant on a comeagre set.-/
theorem exists_residualEq_const_of_measurable_completeInvariant
    {f : (ℕ → Bool) → (ℕ → Bool)} (hf : Measurable f)
    (hrel : ∀ x y, eventualEq x y ↔ f x = f y) :
    ∃ b : ℕ → Bool, ∀ᶠ x in residual (ℕ → Bool), f x = b := by
  classical
  let A : ℕ → Set (ℕ → Bool) := fun n ↦ {x | f x n = true}
  have hAmeas (n : ℕ) : MeasurableSet (A n) := by
    exact measurableSet_eq_fun ((measurable_pi_apply n).comp hf) measurable_const
  have hAinv (n : ℕ) : IsEventualEqInvariant (A n) := by
    intro x y hxy
    have hfx : f x = f y := (hrel x y).1 hxy
    simp only [A, mem_ofPred_eq]
    rw [hfx]
  have hAzero (n : ℕ) : IsMeagre (A n) ∨ IsMeagre (A n)ᶜ :=
    isMeagre_or_compl_isMeagre_of_baireMeasurable_eventualEqInvariant
      (hAmeas n).baireMeasurableSet (hAinv n)
  let b : ℕ → Bool := fun n ↦ if IsMeagre (A n) then false else true
  have hcoord (n : ℕ) : ∀ᶠ x in residual (ℕ → Bool), f x n = b n := by
    by_cases hAm : IsMeagre (A n)
    · have hbn : b n = false := by simp [b, hAm]
      rw [hbn]
      change ∀ᶠ x in residual (ℕ → Bool), f x n = false
      change (A n)ᶜ ∈ residual (ℕ → Bool) at hAm
      filter_upwards [hAm] with x hx
      change f x n ≠ true at hx
      cases hfx : f x n <;> simp_all
    · have hAcm : IsMeagre (A n)ᶜ := (hAzero n).resolve_left hAm
      have hAr : A n ∈ residual (ℕ → Bool) := by
        simpa [IsMeagre] using hAcm
      have hbn : b n = true := by simp [b, hAm]
      rw [hbn]
      exact hAr
  refine ⟨b, ?_⟩
  filter_upwards [eventually_countable_forall.2 hcoord] with x hx
  funext n
  exact hx n

/-- Eventual equality is not smooth.-/
theorem not_isSmooth_eventualEq : ¬ IsSmooth eventualEq := by
  intro hsmooth
  rcases hsmooth with ⟨_, Y, mY, hY, f, hf, hrel⟩
  letI : MeasurableSpace Y := mY
  letI : StandardBorelSpace Y := hY
  obtain ⟨j, hj, hjinj⟩ :=
    MeasurableSpace.measurable_injection_nat_bool_of_countablySeparated Y
  let g : (ℕ → Bool) → (ℕ → Bool) := fun x ↦ j (f x)
  have hg : Measurable g := hj.comp hf
  have hgrel (x y : ℕ → Bool) : eventualEq x y ↔ g x = g y := by
    constructor
    · intro hxy
      exact congrArg j ((hrel x y).1 hxy)
    · intro hxy
      exact (hrel x y).2 (hjinj hxy)
  rcases exists_residualEq_const_of_measurable_completeInvariant hg hgrel with ⟨b, hb⟩
  let F : Set (ℕ → Bool) := {x | g x = b}
  have hFr : F ∈ residual (ℕ → Bool) := by
    exact hb
  have hFnm : ¬ IsMeagre F := not_isMeagre_of_mem_residual hFr
  rcases nonempty_of_not_isMeagre hFnm with ⟨x, hx⟩
  have hsub : F ⊆ equivalenceClass eventualEq x := by
    intro y hy
    exact (hgrel x y).2 (hx.trans hy.symm)
  exact hFnm ((isMeagre_equivalenceClass_eventualEq x).mono hsub)

end DescriptiveSetTheory
