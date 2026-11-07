/-
Copyright (c) 2025 Fabrizio Montesi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Fabrizio Montesi, Thomas Waring
-/

module

public import Tengoku.Cslib.Cslib.Foundations.Relation.Domain
public import Tengoku.Cslib.Cslib.Foundations.Semantics.LTS.TraceEq
public import Tengoku.Seed.Tactic.TFAE

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Bisimulation and Bisimilarity

A bisimulation is a binary relation on the states of two `LTS`s, which establishes a tight semantic
correspondence. More specifically, if two states `s₁` and `s₂` are related by a bisimulation, then
`s₁` can mimic all transitions of `s₂` and vice versa. Furthermore, the derivatives reached through
these transitions remain related by the bisimulation.

Bisimilarity is the largest bisimulation between two LTSs: it relates any two states that are
related by some bisimulation between those LTSs.

Weak bisimulation (resp. bisimilarity) is the relaxed version of bisimulation (resp. bisimilarity)
whereby internal actions performed by processes can be ignored.

For an introduction to theory of bisimulation, we refer to [Sangiorgi2011].

## Main definitions

- `IsBisimulation lts₁ lts₂ r`: the relation `r` is a bisimulation between `lts₁` and `lts₂`.
- `Bisimilarity lts₁ lts₂`: states related by some bisimulation between `lts₁` and `lts₂`.
- `UpToHomBisimilarity lts₁ lts₂ r`: the closure of `r` under bisimilarity in each LTS.
- `IsBisimulationUpTo lts₁ lts₂ r`: transitions from states related by `r` can be matched with
  derivatives in `UpToHomBisimilarity lts₁ lts₂ r`.
- `IsWeakBisimulation lts₁ lts₂ r`: the relation `r` is a weak bisimulation.
- `WeakBisimilarity lts₁ lts₂`: states related by some weak bisimulation.
- `IsSWBisimulation lts₁ lts₂ r`: a characterization of weak bisimulation using single-transition
  challenges, which we prove to be sound and complete.

The `Hom` variants specialize these definitions to comparing states in the same LTS.

## Notations

- `s₁ ~[lts₁,lts₂] s₂`: the states `s₁` and `s₂` are bisimilar under `lts₁` and `lts₂`.
- `s₁ ≈[lts₁,lts₂] s₂`: the states `s₁` and `s₂` are weakly bisimilar under `lts₁` and `lts₂`.
- `s₁ ~[lts] s₂` and `s₁ ≈[lts] s₂`: the corresponding homogeneous relations.

## Main statements

- `LTS.IsBisimulation.inv`: the inverse of a bisimulation is a bisimulation.
- `HomBisimilarity.eqv`: homogeneous bisimilarity is an equivalence relation (see `Equivalence`).
- `Bisimilarity.isBisimulation`: bisimilarity is itself a bisimulation.
- `IsBisimulation.le_bisimilarity`: bisimilarity is the largest bisimulation.
- `Bisimilarity.gfp`: the union of bisimilarity and any bisimulation is equal to bisimilarity.
- `LTS.IsBisimulationUpTo.isBisimulation`: if `r` is a bisimulation up to bisimilarity,
  `UpToHomBisimilarity lts₁ lts₂ r` is a bisimulation.
- `LTS.IsBisimulationUpTo.le_bisimilarity`: a bisimulation up to bisimilarity relates only
  bisimilar states.
- `LTS.IsBisimulation.traceEq`: any bisimulation that relates two states implies that they are
trace equivalent (see `TraceEq`).
- `Bisimilarity.deterministic_bisim_eq_traceEq`: in a deterministic LTS, bisimilarity and trace
equivalence coincide.
- `HomBisimilarity.symm_simulation`: homogeneous bisimilarity can be characterized through
  symmetric simulations.
- `WeakBisimilarity.weakBisim_eq_swBisim`: weak bisimulation and sw-bisimulation coincide.
- `HomWeakBisimilarity.eqv`: homogeneous weak bisimilarity is an equivalence relation.

-/

@[expose] public section

namespace Cslib.LTS

variable {State₁ State₂ Label : Type*} {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}

section Bisimulation

/-- A relation is a bisimulation if, whenever it relates two states,
the transitions originating from these states mimic each other and the reached
derivatives are themselves related.-/
def IsBisimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂')
  )

/-! ## Relation to simulation -/

/-- Any bisimulation is also a simulation.
@isnad1 id=issimula.1h6v.s5.10fcc73ae7a7 from=translated src=- shape=3095429b vocab=6cc45a09
-/
theorem IsBisimulation.isSimulation : IsBisimulation lts₁ lts₂ r → IsSimulation lts₁ lts₂ r := by
  grind [IsBisimulation, IsSimulation]

/-- The inverse of a bisimulation is a simulation.
@isnad1 id=issimula.1h6v.s5.d46babc7ccaf from=translated src=- shape=02cd4fde vocab=7cd7d26c
-/
theorem IsBisimulation.flip_isSimulation :
    IsBisimulation lts₁ lts₂ r → IsSimulation lts₂ lts₁ (flip r) := by
  grind [IsBisimulation, IsSimulation, flip]

/-- A relation is a bisimulation iff both it and its inverse are simulations.
@isnad1 id=iff.0h6v.s5.0f181f6df0f9 from=translated src=- shape=5c56b355 vocab=7cd7d26c
-/
theorem IsBisimulation.isSimulation_iff :
    IsBisimulation lts₁ lts₂ r ↔ (IsSimulation lts₁ lts₂ r ∧ IsSimulation lts₂ lts₁ (flip r)) := by
  have _ (s₁ s₂) : r s₁ s₂ → flip r s₂ s₁ := id
  grind [IsBisimulation, IsSimulation, flip]

/-- Helper for following a transition by the first state in a pair of a `Bisimulation`.
@isnad1 id=ex.2h11v.s6.4f5641eb44f9 from=translated src=- shape=f14f54e2 vocab=a5ac4af8
-/
theorem IsBisimulation.follow_fst
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) (htr : lts₁.Tr s₁ μ s₁') :
    ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂' :=
  IsSimulation.follow hb.isSimulation hr htr

/-- Helper for following a transition by the second state in a pair of a `Bisimulation`.
@isnad1 id=ex.2h11v.s6.1ea787356410 from=translated src=- shape=1bf95941 vocab=a5ac4af8
-/
theorem IsBisimulation.follow_snd
    (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) (htr : lts₂.Tr s₂ μ s₂') :
    ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂' :=
  IsSimulation.follow hb.flip_isSimulation hr htr

/-- If the unique transition of a state is matched by a related state in a bisimulation,
then the derivatives are still in the bisimulation.-/
theorem IsBisimulation.match_deterministic
    (hb : IsBisimulation lts₁ lts₂ r)
    (hr : r s₁ s₂)
    (hdet : lts₁.DeterministicStateLabel s₁ μ)
    (htr₁ : lts₁.Tr s₁ μ s₁')
    (htr₂ : lts₂.Tr s₂ μ s₂') : r s₁' s₂' := by
  have hr' : (flip r) s₂ s₁ := by grind [flip]
  apply IsSimulation.match_deterministic hb.flip_isSimulation hr' hdet htr₂ htr₁

/-- If the unique transition of a state is matched by a related state in the inverse of a
bisimulation, then the derivatives are still in the bisimulation.-/
theorem IsBisimulation.match_deterministic₂
    (hb : IsBisimulation lts₁ lts₂ r)
    (hr : r s₁ s₂)
    (hdet : lts₂.DeterministicStateLabel s₂ μ)
    (htr₁ : lts₁.Tr s₁ μ s₁')
    (htr₂ : lts₂.Tr s₂ μ s₂') : r s₁' s₂' := by
  apply IsSimulation.match_deterministic hb.isSimulation hr hdet htr₁ htr₂

/-- If a state is deterministic for `μ`, then any transition made by a related state in a
bisimulation is matched by a unique transition (left variant).
@isnad1 id=existsun.3h11v.s6.2ddc915b8570 from=translated src=- shape=b1422a4f vocab=b5c84c84
-/
theorem IsBisimulation.follow_fst_deterministic (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂)
    (hdet : lts₂.DeterministicStateLabel s₂ μ) (htr : lts₁.Tr s₁ μ s₁') :
    ∃! s₂', lts₂.Tr s₂ μ s₂' ∧ r s₁' s₂' :=
  IsSimulation.follow_deterministic hb.isSimulation hr hdet htr

/-- If a state is deterministic for `μ`, then any transition made by a related state in a
bisimulation is matched by a unique transition (right variant).
@isnad1 id=existsun.3h11v.s6.5fbbc4ef5700 from=translated src=- shape=34a5b8d7 vocab=b5c84c84
-/
theorem IsBisimulation.follow_snd_deterministic
    (hb : IsBisimulation lts₁ lts₂ r)
    (hr : r s₁ s₂)
    (hdet : lts₁.DeterministicStateLabel s₁ μ)
    (htr : lts₂.Tr s₂ μ s₂') : ∃! s₁', lts₁.Tr s₁ μ s₁' ∧ r s₁' s₂' :=
  IsSimulation.follow_deterministic hb.flip_isSimulation hr hdet htr

/-- A homogeneous bisimulation is a bisimulation where the underlying LTSs are the same.-/
abbrev IsHomBisimulation (lts : LTS State Label) := IsBisimulation lts lts

/-- Two states are bisimilar if they are related by some bisimulation.-/
@[scoped grind =]
def Bisimilarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) : State₁ → State₂ → Prop :=
  fun s₁ s₂ => ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsBisimulation lts₁ lts₂ r

/--
Notation for bisimilarity.

Differently from standard pen-and-paper presentations, we require the LTSs to be mentioned
explicitly.-/
scoped notation s:max " ~[" lts₁ "," lts₂ "] " s':max => Bisimilarity lts₁ lts₂ s s'

/-- Homogeneous bisimilarity is bisimilarity where the underlying LTSs are the same.-/
abbrev HomBisimilarity (lts : LTS State Label) := Bisimilarity lts lts

/-- Notation for homogeneous bisimilarity.-/
scoped notation s:max " ~[" lts "] " s':max => HomBisimilarity lts s s'

/-- Helper for following a transition by the first state in a pair of a `Bisimilarity`.
@isnad1 id=ex.2h9v.s5.433a5ab882e7 from=translated src=- shape=bf092d86 vocab=11aad91f
-/
theorem Bisimilarity.follow_fst (hr : s₁ ~[lts₁,lts₂] s₂) (htr : lts₁.Tr s₁ μ s₁') :
    ∃ s₂', lts₂.Tr s₂ μ s₂' ∧ s₁' ~[lts₁,lts₂ ] s₂' := by grind [IsBisimulation]

/-- Helper for following a transition by the first state in a pair of a `Bisimilarity`.
@isnad1 id=ex.2h9v.s5.5dcae5120df4 from=translated src=- shape=978a737f vocab=11aad91f
-/
theorem Bisimilarity.follow_snd (hr : s₁ ~[lts₁,lts₂] s₂) (htr : lts₂.Tr s₂ μ s₂') :
    ∃ s₁', lts₁.Tr s₁ μ s₁' ∧ s₁' ~[lts₁,lts₂] s₂' := by grind [IsBisimulation]

/-- Homogeneous bisimilarity is reflexive.
@isnad1 id=hombisim.0h4v.s4.6244de1d9e54 from=translated src=- shape=91bf1f87 vocab=97d80450
-/
@[scoped grind ., refl]
theorem HomBisimilarity.refl (s : State) : s ~[lts] s := by
  exists Eq
  grind [IsBisimulation]

/-- States with the same image function are bisimilar.
@isnad1 id=hombisim.1h5v.s5.d755da936381 from=translated src=- shape=7522d43a vocab=2f0ed72f
-/
theorem HomBisimilarity.of_image_eq {lts : LTS State Label} {s₁ s₂ : State}
    (h : lts.image s₁ = lts.image s₂) : s₁ ~[lts] s₂ := by
  refine ⟨fun s t => lts.image s = lts.image t, h, ?_⟩
  intro s t h μ
  have htr (s' : State) : lts.Tr s μ s' ↔ lts.Tr t μ s' :=
    Set.ext_iff.mp (congrFun h μ) s'
  exact ⟨fun s' hs' => ⟨s', (htr s').mp hs', rfl⟩,
    fun t' ht' => ⟨t', (htr t').mpr ht', rfl⟩⟩

/-- The inverse of a bisimulation is a bisimulation.
@isnad1 id=isbisimu.1h6v.s5.15d311a44ca1 from=translated src=- shape=ff7a67d8 vocab=4420533a
-/
@[scoped grind →]
theorem IsBisimulation.inv (h : IsBisimulation lts₁ lts₂ r) :
  IsBisimulation lts₂ lts₁ (flip r) := by grind [IsBisimulation, flip]

open scoped IsBisimulation in
/-- Bisimilarity is symmetric.
@isnad1 id=bisimila.1h7v.s5.eb55aa9dc2fd from=translated src=- shape=f4be1450 vocab=544b5425
-/
@[scoped grind →, symm]
theorem Bisimilarity.symm {State₁ State₂ : Type*}
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {s₁ : State₁} {s₂ : State₂}
    (h : s₁ ~[lts₁,lts₂] s₂) : s₂ ~[lts₂,lts₁] s₁ := by
  grind [flip]

/-- The composition of two bisimulations is a bisimulation.
@isnad1 id=isbisimu.2h9v.s5.1f9bf127daa6 from=translated src=- shape=4f82f3d8 vocab=56f7b9fe
-/
@[scoped grind .]
theorem IsBisimulation.comp
    (h1 : IsBisimulation lts₁ lts₂ r1) (h2 : IsBisimulation lts₂ lts₃ r2) :
  IsBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := by grind [IsBisimulation, Relation.Comp]

/-- Bisimilarity is transitive.
@isnad1 id=bisimila.2h10v.s5.c5794546eecf from=translated src=- shape=aa632320 vocab=544b5425
-/
@[scoped grind →]
theorem Bisimilarity.trans
    (h1 : s₁ ~[lts₁,lts₂] s₂) (h2 : s₂ ~[lts₂,lts₃] s₃) :
  s₁ ~[lts₁,lts₃] s₃ := by
  obtain ⟨r1, _, _⟩ := h1
  obtain ⟨r2, _, _⟩ := h2
  exists Relation.Comp r1 r2
  grind [IsBisimulation, Relation.Comp]

/-- Homogeneous bisimilarity is an equivalence relation.
@isnad1 id=equivale.0h3v.s3.6dce35a3dd59 from=translated src=- shape=e2817ce2 vocab=6dbff1ec
-/
theorem HomBisimilarity.eqv :
  Equivalence (HomBisimilarity lts) := {
    refl := HomBisimilarity.refl
    symm := Bisimilarity.symm
    trans := Bisimilarity.trans
  }

/-- Bisimulation implies simulation equivalence.
@isnad1 id=simulati.1h9v.s5.e84148dc9be5 from=translated src=- shape=20c30422 vocab=afcf7511
-/
theorem IsBisimulation.simulationEquiv (h : IsBisimulation lts₁ lts₂ r) (hrel : r s₁ s₂) :
    s₁ ≤≥[lts₁,lts₂] s₂ := ⟨⟨r, hrel, h.isSimulation⟩, flip r, hrel, h.inv.isSimulation⟩

/-- The union of two bisimulations is a bisimulation.
@isnad1 id=isbisimu.2h7v.s6.202df763dde3 from=translated src=- shape=0cf03f72 vocab=ac123b0f
-/
@[scoped grind .]
theorem IsBisimulation.sup (hrb : IsBisimulation lts₁ lts₂ r) (hsb : IsBisimulation lts₁ lts₂ s) :
    IsBisimulation lts₁ lts₂ (r ⊔ s) := by
  rw [IsBisimulation.isSimulation_iff] at hrb hsb ⊢
  rw [show flip (r ⊔ s) = flip r ⊔ flip s by ext; rfl]
  exact ⟨hrb.1.sup hsb.1, hrb.2.sup hsb.2⟩

/-- Bisimilarity is a bisimulation.
@isnad1 id=isbisimu.0h5v.s4.2671d479bdcd from=translated src=- shape=66e02242 vocab=5d6d9023
-/
@[scoped grind .]
theorem Bisimilarity.isBisimulation (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
  IsBisimulation lts₁ lts₂ (Bisimilarity lts₁ lts₂) := by grind [IsBisimulation]

/-- Bisimilarity is the largest bisimulation.
@isnad1 id=le.1h6v.s5.84bcf34d44b9 from=translated src=- shape=2ed00859 vocab=7238f987
-/
@[scoped grind →]
theorem IsBisimulation.le_bisimilarity (h : IsBisimulation lts₁ lts₂ r) :
    r ≤ (Bisimilarity lts₁ lts₂) := by
  intro s₁ s₂ hr
  exists r

/-- The union of bisimilarity with any bisimulation is bisimilarity.
@isnad1 id=eq.1h6v.s6.3094d4768a61 from=translated src=- shape=e3c18152 vocab=d1bcdef4
-/
@[scoped grind =, simp]
theorem Bisimilarity.gfp (r : State₁ → State₂ → Prop) (h : IsBisimulation lts₁ lts₂ r) :
    (Bisimilarity lts₁ lts₂) ⊔ r = Bisimilarity lts₁ lts₂ := sup_eq_left.mpr h.le_bisimilarity

/-- `calc` support for bisimilarity.-/
instance : Trans (Bisimilarity lts₁ lts₂) (Bisimilarity lts₂ lts₃) (Bisimilarity lts₁ lts₃) where
  trans := Bisimilarity.trans

section Order

/-! ## Order properties -/

instance : Max {r // IsBisimulation lts₁ lts₂ r} where
  max r s := ⟨r.1 ⊔ s.1, IsBisimulation.sup r.2 s.2⟩

/--
@isnad1 id=eq.0h7v.s7.c1cb0a2b996f from=translated src=- shape=cabea3fc vocab=5a2a2e36
-/
@[simp] lemma coe_sup (r s : {r // IsBisimulation lts₁ lts₂ r}) :
    (↑(r ⊔ s) : State₁ → State₂ → Prop) = (r : State₁ → State₂ → Prop) ⊔ s := rfl

/-- Bisimulations equipped with union form a join-semilattice.-/
instance : SemilatticeSup {r // IsBisimulation lts₁ lts₂ r} where
  sup r s := r ⊔ s
  le_sup_left r s := by simp [←Subtype.coe_le_coe]
  le_sup_right r s := by simp [←Subtype.coe_le_coe]
  sup_le r s t := by simp [←Subtype.coe_le_coe]; tauto

/-- The empty (heterogeneous) relation is a bisimulation.
@isnad1 id=isbisimu.0h5v.s4.d0ccdf050947 from=translated src=- shape=a9ee9373 vocab=0c6a8e08
-/
@[scoped grind .]
theorem IsBisimulation.bot : IsBisimulation lts₁ lts₂ Relation.emptyHRelation := by
  intro s₁ s₂ hr
  cases hr

instance : Bot {r // IsBisimulation lts₁ lts₂ r} :=
  ⟨Relation.emptyHRelation, IsBisimulation.bot⟩

instance : Top {r // IsBisimulation lts₁ lts₂ r} :=
  ⟨Bisimilarity lts₁ lts₂, Bisimilarity.isBisimulation ..⟩

/-- In the inclusion order on bisimulations:

- The empty relation is the bottom element.
- Bisimilarity is the top element.-/
instance : BoundedOrder {r // IsBisimulation lts₁ lts₂ r} where
  top := ⊤
  bot := ⊥
  le_top r := r.property.le_bisimilarity
  bot_le r := by simp [Bot.bot, LE.le]

end Order

/-! ## Bisimulation up-to -/

/-- The closure of `r` under bisimilarity in each LTS: `s₁` and `s₂` are related if there are
`t₁` and `t₂` with `s₁ ~[lts₁] t₁`, `r t₁ t₂`, and `t₂ ~[lts₂] s₂`.-/
def UpToHomBisimilarity (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : State₁ → State₂ → Prop :=
  Relation.Comp (HomBisimilarity lts₁) (Relation.Comp r (HomBisimilarity lts₂))

/-- A relation `r` is a bisimulation up to homogeneous bisimilarity if, whenever it relates two
states, their transitions can be matched with derivatives related by
`UpToHomBisimilarity lts₁ lts₂ r`.-/
def IsBisimulationUpTo (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.Tr s₂ μ s₂' ∧
      (UpToHomBisimilarity lts₁ lts₂ r) s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.Tr s₁ μ s₁' ∧
      (UpToHomBisimilarity lts₁ lts₂ r) s₁' s₂')
  )

/-- If `r` is a bisimulation up to bisimilarity, its closure
`UpToHomBisimilarity lts₁ lts₂ r` is a bisimulation.
@isnad1 id=isbisimu.1h6v.s5.7b3c458b5452 from=translated src=- shape=72a96bc3 vocab=93920ed4
-/
@[scoped grind →]
theorem IsBisimulationUpTo.isBisimulation (h : IsBisimulationUpTo lts₁ lts₂ r) :
    IsBisimulation lts₁ lts₂ (UpToHomBisimilarity lts₁ lts₂ r) := by
  intro s₁ s₂ hr μ
  rcases hr with ⟨s₁b, hr1b, s₂b, hrb, hr2b⟩
  constructor
  case left =>
    intro s₁' htr1
    obtain ⟨s₁b', hs₁b'tr, hs₁b'r⟩ := hr1b.follow_fst htr1
    obtain ⟨s₂b', hs₂b'tr, hs₂b'r⟩ := (h hrb μ).1 s₁b' hs₁b'tr
    obtain ⟨s₂', hs₂btr, hs₂br⟩ := hr2b.follow_fst hs₂b'tr
    use s₂', hs₂btr
    obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs₂b'r
    use smid1, hs₁b'r.trans hsmidb, smid2, hsmidr
    exact hsmidrb.trans hs₂br
  case right =>
    intro s₂' htr2
    obtain ⟨s₂b', hs₂b'tr, hs₂b'r⟩ := hr2b.follow_snd htr2
    obtain ⟨s₁b', hs₁b'tr, hs₁b'r⟩ := (h hrb μ).2 s₂b' hs₂b'tr
    obtain ⟨s₁', hs₁btr, hs₁br⟩ := hr1b.follow_snd hs₁b'tr
    use s₁', hs₁btr
    obtain ⟨smid1, hsmidb, smid2, hsmidr, hsmidrb⟩ := hs₁b'r
    use smid1, hs₁br.trans hsmidb, smid2, hsmidr
    exact hsmidrb.trans hs₂b'r

/-- A bisimulation up to bisimilarity relates only bisimilar states.
@isnad1 id=le.1h6v.s5.2edccfdae87d from=translated src=- shape=2ed00859 vocab=525fe2ab
-/
theorem IsBisimulationUpTo.le_bisimilarity (h : IsBisimulationUpTo lts₁ lts₂ r) :
    r ≤ Bisimilarity lts₁ lts₂ := by
  intro s₁ s₂ hr
  exact h.isBisimulation.le_bisimilarity s₁ s₂
    ⟨s₁, HomBisimilarity.refl s₁, s₂, hr, HomBisimilarity.refl s₂⟩

/-- If two states are related by a bisimulation, they can mimic each other's multi-step
transitions.
@isnad1 id=ex.2h11v.s6.744f5d648058 from=translated src=- shape=e60bd947 vocab=138c56ae
-/
theorem IsBisimulation.bisim_trace (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) :
    ∀ μs s₁', lts₁.MTr s₁ μs s₁' → ∃ s₂', lts₂.MTr s₂ μs s₂' ∧ r s₁' s₂' :=
  hb.isSimulation.sim_trace hr

/-! ## Relation to trace equivalence -/

/-- Any bisimulation implies trace equivalence.
@isnad1 id=traceeq.1h9v.s5.f5422ce29639 from=translated src=- shape=20c30422 vocab=1272dc92
-/
@[scoped grind =>]
theorem IsBisimulation.traceEq (hb : IsBisimulation lts₁ lts₂ r) (hr : r s₁ s₂) :
    s₁ ~tr[lts₁,lts₂] s₂ := (hb.simulationEquiv hr).traceEq

/-- Bisimilarity is included in trace equivalence.
@isnad1 id=le.0h5v.s5.c1da5715abc5 from=translated src=- shape=76166ba1 vocab=ab585fa6
-/
@[scoped grind .]
theorem Bisimilarity.le_traceEq : Bisimilarity lts₁ lts₂ ≤ TraceEq lts₁ lts₂ := by
  intro s₁ s₂ h
  obtain ⟨r, hr, hb⟩ := h
  apply hb.traceEq hr

/- One of the standard motivating examples for bisimulation: `1` and `5` are trace equivalent, but
not bisimilar. -/
private inductive BisimMotTr : ℕ → Char → ℕ → Prop where
-- First process, `1`
| one2two : BisimMotTr 1 'a' 2
| two2three : BisimMotTr 2 'b' 3
| two2four : BisimMotTr 2 'c' 4
-- Second process, `5`
| five2six : BisimMotTr 5 'a' 6
| six2seven : BisimMotTr 6 'b' 7
| five2eight : BisimMotTr 5 'a' 8
| eight2nine : BisimMotTr 8 'c' 9

/-- In general, trace equivalence is not a bisimulation (extra conditions are needed, see for
example `Bisimulation.deterministic_trace_eq_is_bisim`).
@isnad1 id=ex.0h0v.s4.f2a77419cafd from=translated src=- shape=d39a8b5f vocab=b173f926
-/
theorem IsBisimulation.traceEq_not_bisim :
    ∃ (State : Type) (Label : Type) (lts : LTS State Label),
      ¬(IsHomBisimulation lts (HomTraceEq lts)) := by
  let lts := LTS.mk BisimMotTr
  exists ℕ, Char, lts
  intro h
  have htreq : (1 ~tr[lts] 5) := by
    have htraces₁ : lts.traces 1 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
      ext μs
      constructor
      case mp =>
        rintro ⟨_, (_ | ⟨⟨_⟩, (_ | ⟨(_ | _), (_ | ⟨⟨_⟩, _⟩)⟩)⟩)⟩
        all_goals simp
      case mpr =>
        rintro (rfl | rfl | rfl | rfl)
        · exact ⟨1, .refl⟩
        · exact ⟨2, MTr.single lts .one2two⟩
        · exact ⟨3, MTr.stepL .one2two <| MTr.single lts .two2three⟩
        · exact ⟨4, MTr.stepL .one2two <| MTr.single lts .two2four⟩
    have htraces₅ : lts.traces 5 = {[], ['a'], ['a', 'b'], ['a', 'c']} := by
      ext μs
      constructor
      case mp =>
        rintro ⟨_, (_ | ⟨(_ | _), (_ | ⟨⟨_⟩, (_ | ⟨⟨_⟩, _⟩)⟩)⟩)⟩
        all_goals simp
      case mpr =>
        rintro (rfl | rfl | rfl | rfl)
        · exact ⟨5, .refl⟩
        · exact ⟨6, MTr.single lts .five2six⟩
        · exact ⟨7, MTr.stepL .five2six <| MTr.single lts .six2seven⟩
        · exact ⟨9, MTr.stepL .five2eight <| MTr.single lts .eight2nine⟩
    exact htraces₁.trans htraces₅.symm
  obtain ⟨h1, h2⟩ := h htreq 'a'
  obtain ⟨s₂', htr5, cih⟩ := h1 2 (by constructor)
  have htraces₂ : {['b'], ['c']} ⊆ lts.traces 2 := by
    intro μs h
    rcases h with (rfl | rfl)
    · refine ⟨3, MTr.single lts .two2three⟩
    · refine ⟨4, MTr.single lts .two2four⟩
  cases htr5
  case five2six =>
    suffices ['c'] ∉ lts.traces 6 by grind [TraceEq]
    rintro ⟨_, (_ | h)⟩
    cases h
  case five2eight =>
    suffices ['b'] ∉ lts.traces 8 by grind [TraceEq]
    rintro ⟨_, (_ | h)⟩
    cases h

/-- In general, bisimilarity and trace equivalence are distinct.
@isnad1 id=ex.0h0v.s4.070804dcb759 from=translated src=- shape=27b328de vocab=49a1e2d3
-/
theorem Bisimilarity.bisimilarity_neq_traceEq :
    ∃ (State : Type) (Label : Type) (lts : LTS State Label),
      HomBisimilarity lts ≠ HomTraceEq lts := by
  obtain ⟨State, Label, lts, h⟩ := IsBisimulation.traceEq_not_bisim
  grind [Bisimilarity.isBisimulation lts lts]

/-- In any deterministic LTS, trace equivalence is a bisimulation.
@isnad1 id=isbisimu.0h5v.s5.70435b1ef9f3 from=translated src=- shape=15682d8c vocab=93532a40
-/
theorem IsBisimulation.deterministic_traceEq_isBisimulation
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] :
    (IsBisimulation lts₁ lts₂ (TraceEq lts₁ lts₂)) := by
  rw [IsBisimulation.isSimulation_iff, TraceEq.flip_eq]
  exact ⟨Deterministic.isSimulation_traceEq, Deterministic.isSimulation_traceEq⟩

/-- In deterministic LTSs, trace equivalence implies bisimilarity.
@isnad1 id=bisimila.1h7v.s5.49e54ebde231 from=translated src=- shape=cdfb9e4d vocab=2d48b76d
-/
theorem Bisimilarity.deterministic_traceEq_bisim {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] (h : s₁ ~tr[lts₁,lts₂] s₂) :
    (s₁ ~[lts₁,lts₂] s₂) := by
  use TraceEq lts₁ lts₂, h, IsBisimulation.deterministic_traceEq_isBisimulation

/-- In a deterministic lts, bisimilarity, trace equivalence, and simulation equivalence are
equivalent to one-another.
@isnad1 id=tfae.0h7v.s5.c9c9a51d625d from=translated src=- shape=5c17b82a vocab=61317eba
-/
theorem Deterministic.bisim_tfae {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] (s₁ : State₁) (s₂ : State₂) :
    [s₁ ~[lts₁,lts₂] s₂, s₁ ~tr[lts₁,lts₂] s₂, s₁ ≤≥[lts₁,lts₂] s₂].TFAE := by
  tfae_have 2 ↔ 3 := Deterministic.traceEq_iff_simulationEquiv s₁ s₂
  tfae_have 1 → 2 := Bisimilarity.le_traceEq s₁ s₂
  tfae_have 2 → 1 := Bisimilarity.deterministic_traceEq_bisim
  tfae_finish

/-- In deterministic LTSs, bisimilarity and trace equivalence coincide.
@isnad1 id=eq.0h5v.s5.59f980617de7 from=translated src=- shape=8a55dde8 vocab=2d48b76d
-/
theorem Bisimilarity.deterministic_bisim_eq_traceEq
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    [lts₁.Deterministic] [lts₂.Deterministic] : Bisimilarity lts₁ lts₂ = TraceEq lts₁ lts₂ := by
  ext s₁ s₂
  exact (Deterministic.bisim_tfae s₁ s₂).out 1 2

/-- Homogeneous bisimilarity can also be characterized through symmetric simulations.
@isnad1 id=eq.0h3v.s5.7378d3fa549d from=translated src=- shape=16a51c53 vocab=9cb44128
-/
theorem HomBisimilarity.symm_simulation :
  HomBisimilarity lts =
    fun s₁ s₂ => ∃ r, r s₁ s₂ ∧ Std.Symm r ∧ IsHomSimulation lts r := by
  ext s₁ s₂
  constructor
  · intro h
    use lts.HomBisimilarity, h
    exact ⟨⟨fun _ _ => Bisimilarity.symm⟩, (Bisimilarity.isBisimulation lts lts).isSimulation⟩
  · intro ⟨r, hrel, ⟨hsymm⟩, hsim⟩
    use r, hrel
    have : r = flip r := by grind [flip]
    simpa [IsBisimulation.isSimulation_iff, ←this]

end Bisimulation

section WeakBisimulation

/-! ## Weak bisimulation and weak bisimilarity -/

/-- A weak bisimulation is similar to a `Bisimulation`, but allows for the related processes to do
internal work. Technically, this is defined as a `Bisimulation` on the saturation of the LTSs.-/
def IsWeakBisimulation [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) :=
  IsBisimulation (lts₁.saturate) (lts₂.saturate) r

/-- A homogeneous bisimulation is a bisimulation where the underlying LTSs are the same.-/
abbrev IsHomWeakBisimulation [HasTau Label] (lts : LTS State Label) := IsWeakBisimulation lts lts

/-- Two states are weakly bisimilar if they are related by some weak bisimulation.-/
def WeakBisimilarity [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    State₁ → State₂ → Prop :=
  fun s₁ s₂ =>
    ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsWeakBisimulation lts₁ lts₂ r

/-- Notation for weak bisimilarity.-/
scoped notation s:max " ≈[" lts₁ "," lts₂ "] " s':max => WeakBisimilarity lts₁ lts₂ s s'

/-- Homogeneous bisimilarity is bisimilarity where the underlying LTSs are the same.-/
abbrev HomWeakBisimilarity [HasTau Label] (lts : LTS State Label) := WeakBisimilarity lts lts

/-- Notation for homogeneous bisimilarity.-/
scoped notation s:max " ≈[" lts "] " s':max => HomWeakBisimilarity lts s s'

/-- An `SWBisimulation` is a more convenient definition of weak bisimulation, because the challenge
is a single transition. We prove later that this technique is sound, following a strategy inspired
by [Sangiorgi2011].-/
def IsSWBisimulation [HasTau Label] (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label)
    (r : State₁ → State₂ → Prop) : Prop :=
  ∀ ⦃s₁ s₂⦄, r s₁ s₂ → ∀ μ, (
    (∀ s₁', lts₁.Tr s₁ μ s₁' → ∃ s₂', lts₂.STr s₂ μ s₂' ∧ r s₁' s₂')
    ∧
    (∀ s₂', lts₂.Tr s₂ μ s₂' → ∃ s₁', lts₁.STr s₁ μ s₁' ∧ r s₁' s₂')
  )

/--
@isnad1 id=issimula.1h6v.s5.265d1a7b49c8 from=translated src=- shape=07680415 vocab=cc5c0ca3
-/
lemma IsSWBisimulation.isSimulation [HasTau Label] (h : IsSWBisimulation lts₁ lts₂ r) :
    IsSimulation lts₁ lts₂.saturate r := by
  intro s₁ s₂ hr μ
  exact (h hr μ).1

/--
@isnad1 id=issimula.1h6v.s5.38d9b83abfff from=translated src=- shape=601ac969 vocab=47ec9eb4
-/
lemma IsSWBisimulation.isSimulation_flip [HasTau Label] (h : IsSWBisimulation lts₁ lts₂ r) :
    IsSimulation lts₂ lts₁.saturate (flip r) := by
  intro s₂ s₁ hr μ
  exact (h hr μ).2

/--
@isnad1 id=iff.0h6v.s5.94586131c1b4 from=translated src=- shape=6b20cc9e vocab=47ec9eb4
-/
theorem IsSWBisimulation.iff_isSimulation [HasTau Label] :
    IsSWBisimulation lts₁ lts₂ r ↔
      IsSimulation lts₁ lts₂.saturate r ∧ IsSimulation lts₂ lts₁.saturate (flip r) := by
  refine ⟨fun h => ⟨h.isSimulation, h.isSimulation_flip⟩, ?_⟩
  intro ⟨h, hflip⟩ s₁ s₂ hr μ
  exact ⟨h hr μ, hflip hr μ⟩

/-- We can now prove that any relation is a `WeakBisimulation` iff it is an `SWBisimulation`.
This formalises lemma 4.2.10 in [Sangiorgi2011].
@isnad1 id=iff.0h6v.s5.b19a119b5b09 from=translated src=- shape=17e63b1a vocab=6e7206ef
-/
theorem isWeakBisimulation_iff_isSWBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} :
    IsWeakBisimulation lts₁ lts₂ r ↔ IsSWBisimulation lts₁ lts₂ r := by
  apply Iff.intro
  case mp =>
    intro h
    rw [IsSWBisimulation.iff_isSimulation]
    exact ⟨h.isSimulation.mono lts₁.tr_le_tr_saturate le_rfl,
      h.inv.isSimulation.mono lts₂.tr_le_tr_saturate le_rfl⟩
  case mpr =>
    intro h
    rw [IsWeakBisimulation, IsBisimulation.isSimulation_iff]
    exact ⟨h.isSimulation.isSimulation_saturate_left,
      h.isSimulation_flip.isSimulation_saturate_left⟩

/--
@isnad1 id=isswbisi.1h6v.s5.6b7293b9c65c from=translated src=- shape=de9eeee8 vocab=6e7206ef
-/
theorem IsWeakBisimulation.isSwBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {r : State₁ → State₂ → Prop}
    (h : IsWeakBisimulation lts₁ lts₂ r) :
  IsSWBisimulation lts₁ lts₂ r := isWeakBisimulation_iff_isSWBisimulation.1 h

/--
@isnad1 id=isweakbi.1h6v.s5.891901a18ce6 from=translated src=- shape=de9eeee8 vocab=6e7206ef
-/
theorem IsSWBisimulation.isWeakBisimulation
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {r : State₁ → State₂ → Prop}
    (h : IsSWBisimulation lts₁ lts₂ r) :
  IsWeakBisimulation lts₁ lts₂ r := isWeakBisimulation_iff_isSWBisimulation.2 h

/-- Weak bisimilarity can also be characterized through sw-bisimulations.
@isnad1 id=eq.0h5v.s5.3418cc9ead10 from=translated src=- shape=27d1072f vocab=498db1b6
-/
@[scoped grind =]
theorem WeakBisimilarity.weakBisim_eq_swBisim [HasTau Label]
    (lts₁ : LTS State₁ Label) (lts₂ : LTS State₂ Label) :
    WeakBisimilarity lts₁ lts₂ =
      fun s₁ s₂ => ∃ r : State₁ → State₂ → Prop, r s₁ s₂ ∧ IsSWBisimulation lts₁ lts₂ r := by
  grind [WeakBisimilarity, isWeakBisimulation_iff_isSWBisimulation.1,
    isWeakBisimulation_iff_isSWBisimulation.2]

/- The weak laws below reuse the strong laws on the saturated LTSs. -/

/-- Homogeneous weak bisimilarity is reflexive.
@isnad1 id=homweakb.0h4v.s4.54e90d1de04d from=translated src=- shape=8bafcb42 vocab=94f14b48
-/
theorem HomWeakBisimilarity.refl [HasTau Label] {lts : LTS State Label} (s : State) :
    s ≈[lts] s := HomBisimilarity.refl s

/-- The inverse of a weak bisimulation is a weak bisimulation.
@isnad1 id=isweakbi.1h6v.s5.7faea3e68014 from=translated src=- shape=f8124baa vocab=45916f4f
-/
theorem IsWeakBisimulation.inv [HasTau Label]
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (r : State₁ → State₂ → Prop) (h : IsWeakBisimulation lts₁ lts₂ r) :
    IsWeakBisimulation lts₂ lts₁ (flip r) := IsBisimulation.inv h

/-- Weak bisimilarity is symmetric.
@isnad1 id=weakbisi.1h7v.s5.31235209ab27 from=translated src=- shape=8d298767 vocab=fe078d8c
-/
theorem WeakBisimilarity.symm [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label}
    (h : s₁ ≈[lts₁,lts₂] s₂) : s₂ ≈[lts₂,lts₁] s₁ := Bisimilarity.symm h

/-- The composition of two weak bisimulations is a weak bisimulation.
@isnad1 id=isweakbi.2h9v.s6.dcaafa8f215d from=translated src=- shape=056aa6e5 vocab=24a773cc
-/
theorem IsWeakBisimulation.comp
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : IsWeakBisimulation lts₁ lts₂ r1) (h2 : IsWeakBisimulation lts₂ lts₃ r2) :
    IsWeakBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := IsBisimulation.comp h1 h2

/-- The composition of two sw-bisimulations is an sw-bisimulation.
@isnad1 id=isswbisi.2h9v.s6.18bf8178feab from=translated src=- shape=056aa6e5 vocab=5f8c560c
-/
theorem IsSWBisimulation.comp
    [HasTau Label] {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : IsSWBisimulation lts₁ lts₂ r1) (h2 : IsSWBisimulation lts₂ lts₃ r2) :
    IsSWBisimulation lts₁ lts₃ (Relation.Comp r1 r2) := by
  simp_all only [isWeakBisimulation_iff_isSWBisimulation.symm]
  apply IsWeakBisimulation.comp h1 h2

/-- Weak bisimilarity is transitive.
@isnad1 id=weakbisi.2h10v.s5.7419cf821984 from=translated src=- shape=58cf7302 vocab=fe078d8c
-/
theorem WeakBisimilarity.trans [HasTau Label]
    {lts₁ : LTS State₁ Label} {lts₂ : LTS State₂ Label} {lts₃ : LTS State₃ Label}
    (h1 : s₁ ≈[lts₁,lts₂] s₂) (h2 : s₂ ≈[lts₂,lts₃] s₃) : s₁ ≈[lts₁,lts₃] s₃ :=
  Bisimilarity.trans h1 h2

/-- Homogeneous weak bisimilarity is an equivalence relation.
@isnad1 id=equivale.0h3v.s4.b32c38f323a9 from=translated src=- shape=1173c98b vocab=62c0a1ea
-/
theorem HomWeakBisimilarity.eqv [HasTau Label] {lts : LTS State Label} :
    Equivalence (HomWeakBisimilarity lts) where
  refl := HomWeakBisimilarity.refl
  symm := WeakBisimilarity.symm
  trans := WeakBisimilarity.trans

end WeakBisimulation

end Cslib.LTS
