/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Semantics.LTS.HasTau

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # IsSimulation and Similarity

A simulation is a binary relation on the states of two `LTS`s: if two states `s₁` and `s2` are
related by a simulation, then `s2` can mimic all transitions of `s₁` in their respective LTSs.
Furthermore, the derivatives reaches through these transitions remain related by the simulation.

Similarity is the largest simulation: given an `LTS`, it relates any two states that are related
by a simulation for that LTS.

The module provides abbreviations for the homogeneous case of comparing states in the same LTS.

For an introduction to theory of simulation, we refer to [Sangiorgi2011].

## Main definitions

- `IsSimulation lts₁ lts₂ r`: the relation `r` on the states of `lts₁` and `lts₂` is a simulation.
- `Similarity lts₁ lts₂` is the binary relation that relates any two states related by some
simulation on `lts₁` and `lts₂`.
- `SimulationEquiv lts₁ lts₂` is the binary relation on the states of `lts₁` and `lts₂` that relates
any two states similar to each other.

## Notations

- `s₁ ≤[lts₁, lts₂] s₂`: the states `s₁` and `s2` are similar under `lts₁` and `lts₂`.
- `s₁ ≤≥[lts₁, lts₂] s2`: the states `s₁` and `s2` are simulation equivalent under `lts₁` and
`lts₂`.

## Main statements

- `HomSimulationEquiv.eqv`: homogeneous simulation equivalence is an equivalence relation.

-/

@[expose] public section

namespace Cslib.LTS

universe u v

section Simulation

/-- A relation is a simulation if, whenever it relates two states in an lts,
any transition originating from the first state is mimicked by a transition from the second state
and the reached derivatives are themselves related.-/
def IsSimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) (r : State₁ → State₂ → Prop) :
    Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂'

/-- A homogeneous simulation is a simulation where the underlying LTSs are the same.-/
abbrev IsHomSimulation (lts : LTS State Label) := IsSimulation lts lts

/-- Two states are similar if they are related by some simulation.-/
def Similarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) : State₁ → State₂ → Prop :=
  fun s₁ s2 =>
    ∃ r : State₁ → State₂ → Prop, r s₁ s2 ∧ IsSimulation lts₁ lts₂ r

/--
Notation for similarity.

Differently from standard pen-and-paper presentations, we require the lts to be mentioned
explicitly.-/
scoped notation s:max " ≤[" lts₁ "," lts₂ "] " s':max => Similarity lts₁ lts₂ s s'

/-- Homogeneous similarity is similarity where the underlying LTSs are the same.-/
abbrev HomSimilarity (lts : LTS State Label) := Similarity lts lts

/-- Notation for homogeneous similarity.-/
scoped notation s:max " ≤[" lts "] " s':max => HomSimilarity lts s s'

/-- Homogeneous similarity is reflexive.
@isnad1 id=homsimil.0h4v.s4.adc7f7d1dca6 from=translated src=- shape=1afcdb06 vocab=aa46c3b6
-/
theorem HomSimilarity.refl (s : State) : s ≤[lts] s := by
  exists Eq
  grind [IsSimulation]

/-- The composition of two simulations is a simulation.
@isnad1 id=issimula.2h9v.s5.c7a15080da2e from=translated src=- shape=e704c357 vocab=022e4d0c
-/
theorem IsSimulation.comp
    (r1 : State₁ → State₂ → Prop)
    (r2 : State₂ → State₃ → Prop)
    (h1 : IsSimulation lts₁ lts₂ r1) (h2 : IsSimulation lts₂ lts₃ r2) :
    IsSimulation lts₁ lts₃ (Relation.Comp r1 r2) := by
  intro s₁ s2 hrc μ s₁' htr
  rcases hrc with ⟨sb, hr1, hr2⟩
  obtain ⟨s₁'', h1'tr, h1'⟩ := h1 hr1 μ s₁' htr
  obtain ⟨s2'', h2'tr, h2'⟩ := h2 hr2 μ s₁'' h1'tr
  use s2'', h2'tr, s₁'', h1', h2'

/-- Similarity is transitive.
@isnad1 id=similari.2h10v.s5.c8d578eda443 from=translated src=- shape=416464f7 vocab=23a9df42
-/
theorem Similarity.trans (h1 : s₁ ≤[lts₁,lts₂] s2) (h2 : s2 ≤[lts₂,lts₃] s₃) :
    s₁ ≤[lts₁,lts₃] s₃ := by
  obtain ⟨r1, hr1, hr1s⟩ := h1
  obtain ⟨r2, hr2, hr2s⟩ := h2
  use! Relation.Comp r1 r2, s2, hr1, hr2, IsSimulation.comp r1 r2 hr1s hr2s

/--
@isnad1 id=issimula.2h7v.s6.990ab7207e55 from=translated src=- shape=27a6349f vocab=f8f4d515
-/
theorem IsSimulation.sup (hr : IsSimulation lts₁ lts₂ r)
    (hs : IsSimulation lts₁ lts₂ s) : IsSimulation lts₁ lts₂ (r ⊔ s) := by
  rintro s₁ s₂ (hrel | hrel) μ s₁' htr
  · obtain ⟨s₂', htr', hrel'⟩ := hr hrel μ s₁' htr
    use s₂', htr', Or.inl hrel'
  · obtain ⟨s₂', htr', hrel'⟩ := hs hrel μ s₁' htr
    use s₂', htr', Or.inr hrel'

/--
@isnad1 id=ex.2h11v.s6.13f9d1e487b6 from=translated src=- shape=4ef105b1 vocab=80e65d45
-/
theorem IsSimulation.sim_trace (hr : IsSimulation lts₁ lts₂ r) (hrel : r s₁ s₂) :
    ∀ μs s₁', lts₁.MTr s₁ μs s₁' → ∃ s₂', lts₂.MTr s₂ μs s₂' ∧ r s₁' s₂' := by
  intro μs s₁' hmtr
  induction μs generalizing s₁ s₂ with
  | nil =>
    obtain rfl := hmtr.nil_eq
    exact ⟨s₂, MTr.refl, hrel⟩
  | cons μ μs ih =>
    cases hmtr
    case stepL s₁'' htr hmtr =>
      obtain ⟨s₂'', htr₂, hrel'⟩: ∃ s2', lts₂.Tr s₂ μ s2' ∧ r s₁'' s2' := hr hrel μ s₁'' htr
      obtain ⟨s₂', hmtr₂, hrel'⟩ := ih hrel' hmtr
      use s₂', hmtr₂.stepL htr₂, hrel'

/-- Simulation equivalence relates all states `s₁` and `s2` such that `s₁ ≤[lts₁ lts₂] s2` and
`s2 ≤[lts₂ lts₁] s₁`.-/
def SimulationEquiv (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    State₁ → State₂ → Prop :=
  fun s₁ s2 =>
    s₁ ≤[lts₁, lts₂] s2 ∧ s2 ≤[lts₂, lts₁] s₁

/--
Notation for simulation equivalence.-/
scoped notation s:max " ≤≥[" lts₁ "," lts₂ "] " s':max => SimulationEquiv lts₁ lts₂ s s'

/-- Homogeneous simulation equivalence.-/
abbrev HomSimulationEquiv (lts : LTS State Label) := SimulationEquiv lts lts

/-- Notation for homogeneous simulation equivalence.-/
scoped notation s:max " ≤≥[" lts "] " s':max => HomSimulationEquiv lts s s'

/-- Homogeneous simulation equivalence is reflexive.
@isnad1 id=homsimul.0h4v.s4.4457aa81e1d4 from=translated src=- shape=1afcdb06 vocab=12ade808
-/
theorem HomSimulationEquiv.refl (s : State) : s ≤≥[lts] s := by
  grind [SimulationEquiv, HomSimilarity.refl]

/-- Simulation equivalence is symmetric.
@isnad1 id=simulati.1h7v.s5.e383373bf6b9 from=translated src=- shape=5eca7ebc vocab=fc769caf
-/
theorem SimulationEquiv.symm {State₁ State₂ Label : Type*}
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {s₁ : State₁} {s2 : State₂}
    (h : s₁ ≤≥[lts₁,lts₂] s2) : s2 ≤≥[lts₂,lts₁] s₁ :=
  ⟨h.2, h.1⟩

/-- Simulation equivalence is transitive.
@isnad1 id=simulati.2h10v.s5.45fe9aa1bf3e from=translated src=- shape=416464f7 vocab=fc769caf
-/
theorem SimulationEquiv.trans (h1 : s₁ ≤≥[lts₁,lts₂] s2) (h2 : s2 ≤≥[lts₂,lts₃] s₃) :
    s₁ ≤≥[lts₁,lts₃] s₃ := by
  grind [SimulationEquiv, Similarity.trans]

/-- Homogeneous simulation equivalence is an equivalence relation.
@isnad1 id=equivale.0h3v.s4.db73fd7e0dcd from=translated src=- shape=53376e9b vocab=c93763b4
-/
theorem HomSimulationEquiv.eqv : Equivalence (· ≤≥[lts] ·) where
  refl := HomSimulationEquiv.refl
  symm := SimulationEquiv.symm
  trans := SimulationEquiv.trans

/-- `calc` support for simulation equivalence.-/
instance :
  Trans
    (SimulationEquiv lts₁ lts₂)
    (SimulationEquiv lts₂ lts₃)
    (SimulationEquiv lts₁ lts₃) where
  trans := SimulationEquiv.trans

/-- Helper for following a transition by the first state in a pair of a simulation.
@isnad1 id=ex.2h11v.s6.6a4d3d160170 from=translated src=- shape=dc7274e8 vocab=2b960783
-/
theorem IsSimulation.follow
    (hb : IsSimulation lts₁ lts₂ r) (hr : r s₁ s₂) (htr : lts₁.Tr s₁ μ s₁') :
    ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂' := hb hr μ _ htr

/-- Utility theorem for following internal transitions along a saturated lts.
@isnad1 id=ex.2h10v.s6.f58270c6b2fd from=translated src=- shape=09dd5b5d vocab=250712a0
-/
lemma IsSimulation.follow_internal [HasTau Label] {lts₁ : LTS State₁ Label}
    {lts₂ : LTS State₂ Label} (h : IsSimulation lts₁ lts₂.saturate r) (hr : r s₁ s₂)
    (hstr : lts₁.τSTr s₁ s₁') : ∃ s₂', lts₂.τSTr s₂ s₂' ∧ r s₁' s₂' := by
  induction hstr
  case refl =>
    use s₂, .refl
  case tail sb hrsb htrsb ih1 ih2 =>
    obtain ⟨sb2, htrsb2, hrb⟩ := ih2
    have ⟨sb2', htrsb2', hrb'⟩ := h hrb HasTau.τ _ ih1
    use sb2', htrsb2.trans (lts₂.sTr_τSTr_iff.mp htrsb2')

/-- If the right-hand lts is saturated, a simulation lifts along saturating the left-hand lts.
@isnad1 id=issimula.1h6v.s5.bcdc98358e07 from=translated src=- shape=07725b9e vocab=4482af61
-/
theorem IsSimulation.isSimulation_saturate_left [HasTau Label] {lts₁ : LTS State₁ Label}
    {lts₂ : LTS State₂ Label} (h : IsSimulation lts₁ lts₂.saturate r) :
    IsSimulation lts₁.saturate lts₂.saturate r := by
  intro s₁ s₂ hr μ s₁' h
  cases h
  case refl =>
    use s₂, .refl, hr
  case tr sb sb' hstr1 htr hstr2 =>
    obtain ⟨sb1, hstr1b, hrb⟩ := IsSimulation.follow_internal h hr hstr1
    obtain ⟨sb2', hstr1b', hrb'⟩ := h hrb μ _ htr
    obtain ⟨s₁', hstr1', hrb2⟩ := IsSimulation.follow_internal h hrb' hstr2
    rw [←sTr_τSTr_iff] at hstr1' hstr1b
    use s₁', STr.comp hstr1b hstr1b' hstr1', hrb2

/-- Simulation is preserved by removing transitions on the left, and adding transitions on the
right.
@isnad1 id=issimula.3h8v.s7.839c0402c3cf from=translated src=- shape=c72f4887 vocab=29105f9e
-/
theorem IsSimulation.mono (h₁ : lts₁'.Tr ≤ lts₁.Tr) (h₂ : lts₂.Tr ≤ lts₂'.Tr)
    (h : IsSimulation lts₁ lts₂ r) : IsSimulation lts₁' lts₂' r := by
  intro s₁ s₂ hr μ s₁' htr
  obtain ⟨s₂', htr', hr'⟩ := h hr μ s₁' (h₁ _ _ _ htr)
  use s₂', h₂ _ _ _ htr', hr'

/-- When a deterministic state matches a transition in a simulation, then the derivatives are still
in the simulation.-/
theorem IsSimulation.match_deterministic (hb : IsSimulation lts₁ lts₂ r) (hr : r s₁ s₂)
    (hdet : lts₂.DeterministicStateLabel s₂ μ) (htr₁ : lts₁.Tr s₁ μ s₁') (htr₂ : lts₂.Tr s₂ μ s₂') :
    r s₁' s₂' := by
  grind [follow hb hr]

/-- If a state is deterministic for `μ`, then any transition made by a related state in a
simulation is matched by a unique transition.
@isnad1 id=existsun.3h11v.s6.b272ae5a8852 from=translated src=- shape=e8007428 vocab=4af42902
-/
theorem IsSimulation.follow_deterministic (hb : IsSimulation lts₁ lts₂ r) (hr : r s₁ s₂)
    (hdet : lts₂.DeterministicStateLabel s₂ μ) (htr : lts₁.Tr s₁ μ s₁') :
    ∃! s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂' := by
  obtain ⟨s₂', htr₂, hr₂⟩ := follow hb hr htr
  exists s₂'
  grind

end Simulation

end Cslib.LTS
