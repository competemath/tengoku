/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku

/-!
# The induced (Scott) topology and the way-below relation (Scott 1972, §2)

This file formalizes the core of Scott's §2 *Continuous Lattices*: the topology a
complete
lattice carries intrinsically (Scott's "induced topology", today the **Scott
topology**),
the **way-below relation** `≪`, the basic properties of `≪` (Scott's Proposition
2.2), and
the definition of a **continuous lattice** (Scott's Definition 2.3).

Scott defines the induced topology on a partially ordered set `D` by declaring `U`
open iff

* (i)  `U` is an upper set; and
* (ii) whenever `S ⊆ D` is directed (and, in this paper, non-empty), `⊔S` exists
and
       `⊔S ∈ U`, then `S ∩ U ≠ ∅`.

He then defines `x ≪ y` ("`x` is way below `y`") to mean `y ∈ interior {z | x ⊑
z}`, the
interior being taken in this induced topology. We encode "Scott-open" as the
predicate
`ScottOpen` and `≪` as `WayBelow`, witnessing the interior by a Scott-open
neighbourhood
contained in the principal up-set `Set.Ici x = {z | x ≤ z}`. This is faithful to
Scott's
topological definition (rather than the order-theoretic shortcut), and as a result
Scott's
Proposition 2.2 (vi) and (vii) fall straight out of the open-set axioms.

This is the classical/topological version of the theory, so we reason classically.
-/

@[expose] public section

namespace Domain.ContinuousLattice

variable {D : Type*} [CompleteLattice D]

/-- **Scott 1972, §2, the induced topology.** `U` is *Scott-open* when it is an
upper set and
is inaccessible by suprema of non-empty directed sets: if a non-empty directed `S`
has its
supremum in `U`, then some member of `S` already lies in `U`. -/
def ScottOpen (U : Set D) : Prop :=
  IsUpperSet U ∧
    ∀ ⦃S : Set D⦄, S.Nonempty → DirectedOn (· ≤ ·) S → sSup S ∈ U → (S ∩ U).Nonempty

/--
@isnad1 id=isuppers.1h2v.s4.c711e5beb3a7 from=translated src=- shape=93e860ac vocab=f5944a02
-/
theorem ScottOpen.isUpperSet {U : Set D} (h : ScottOpen U) : IsUpperSet U := h.1

/--
@isnad1 id=scottope.0h1v.s3.e2bc219ceac9 from=translated src=- shape=84bfdc15 vocab=ebda0d2a
-/
theorem scottOpen_univ : ScottOpen (Set.univ : Set D) := by
  refine ⟨isUpperSet_univ, fun S hS _ _ => ?_⟩
  simp_all

/--
@isnad1 id=scottope.2h3v.s4.a3cc94c468d5 from=translated src=- shape=0540dca0 vocab=2fcc4462
-/
theorem scottOpen_inter {U V : Set D} (hU : ScottOpen U) (hV : ScottOpen V) :
    ScottOpen (U ∩ V) := by
  refine ⟨hU.1.inter hV.1, fun S hS hSdir hmem => ?_⟩
  obtain ⟨s₁, hs₁S, hs₁U⟩ := hU.2 hS hSdir hmem.1
  obtain ⟨s₂, hs₂S, hs₂V⟩ := hV.2 hS hSdir hmem.2
  obtain ⟨s₃, hs₃S, h₁, h₂⟩ := hSdir s₁ hs₁S s₂ hs₂S
  exact ⟨s₃, hs₃S, hU.1 h₁ hs₁U, hV.1 h₂ hs₂V⟩

/--
@isnad1 id=scottope.1h2v.s5.7a65109ceb3a from=translated src=- shape=5a8b5f56 vocab=9cdc9353
-/
theorem scottOpen_sUnion {C : Set (Set D)} (hC : ∀ U ∈ C, ScottOpen U) :
    ScottOpen (⋃₀ C) := by
  refine ⟨isUpperSet_sUnion fun U hU => (hC U hU).1, fun S hS hSdir hmem => ?_⟩
  obtain ⟨U, hUC, hUmem⟩ := hmem
  obtain ⟨s, hsS, hsU⟩ := (hC U hUC).2 hS hSdir hUmem
  exact ⟨s, hsS, U, hUC, hsU⟩

/-- **Scott 1972, §2.** The *way-below* relation: `x ≪ y` iff `y` lies in the
interior of the
principal up-set `Set.Ici x` for the induced topology, witnessed by a Scott-open
neighbourhood of `y` contained in `Set.Ici x`. -/
def WayBelow (x y : D) : Prop :=
  ∃ U : Set D, ScottOpen U ∧ y ∈ U ∧ U ⊆ Set.Ici x

@[inherit_doc] scoped infix:50 " ≪ " => WayBelow

/-- **Scott 1972, Proposition 2.2(v).** `x ≪ y` implies `x ≤ y`.
@isnad1 id=le.1h3v.s4.ae0d7f090d90 from=translated src=- shape=4ab508a5 vocab=49fef249
-/
theorem WayBelow.le {x y : D} (h : x ≪ y) : x ≤ y := by
  obtain ⟨U, _, hyU, hsub⟩ := h
  exact hsub hyU

/-- **Scott 1972, Proposition 2.2(i).** `⊥ ≪ x` for every `x`.
@isnad1 id=waybelow.0h2v.s4.6c7ec82a3ac7 from=translated src=- shape=9add3c02 vocab=d97b4b86
-/
theorem bot_wayBelow (x : D) : (⊥ : D) ≪ x :=
  ⟨Set.univ, scottOpen_univ, Set.mem_univ x, fun _ _ => bot_le⟩

/-- **Scott 1972, Proposition 2.2(iii).** `x ≪ y` and `y ≤ z` imply `x ≪ z`
(monotone on the
right).
@isnad1 id=waybelow.2h4v.s5.95bcc85de8b8 from=translated src=- shape=ed0e08c7 vocab=49fef249
-/
theorem WayBelow.trans_le {x y z : D} (h : x ≪ y) (hyz : y ≤ z) : x ≪ z := by
  obtain ⟨U, hU, hyU, hsub⟩ := h
  exact ⟨U, hU, hU.1 hyz hyU, hsub⟩

/-- **Scott 1972, Proposition 2.2(iv).** `x ≤ y` and `y ≪ z` imply `x ≪ z`
(monotone on the
left).
@isnad1 id=waybelow.2h4v.s5.4ca53798ef98 from=translated src=- shape=135ae950 vocab=49fef249
-/
theorem WayBelow.le_trans {x y z : D} (hxy : x ≤ y) (h : y ≪ z) : x ≪ z := by
  obtain ⟨U, hU, hzU, hsub⟩ := h
  refine ⟨U, hU, hzU, fun w hw => ?_⟩
  have hyw : y ≤ w := Set.mem_Ici.1 (hsub hw)
  exact Set.mem_Ici.2 (hxy.trans hyw)

/-- **Scott 1972, Proposition 2.2(ii).** `x ≪ z` and `y ≪ z` imply `x ⊔ y ≪ z`.
@isnad1 id=waybelow.2h4v.s5.c0cb8782def2 from=translated src=- shape=13f67537 vocab=0e288847
-/
theorem WayBelow.sup {x y z : D} (hx : x ≪ z) (hy : y ≪ z) : x ⊔ y ≪ z := by
  obtain ⟨U, hU, hzU, hUsub⟩ := hx
  obtain ⟨V, hV, hzV, hVsub⟩ := hy
  refine ⟨U ∩ V, scottOpen_inter hU hV, ⟨hzU, hzV⟩, fun w hw => ?_⟩
  exact Set.mem_Ici.2 (sup_le (hUsub hw.1) (hVsub hw.2))

/-- Auxiliary: the up-set `{z | x ≪ z}` is itself Scott-open. (This is *not*
Scott's
Proposition 2.2(vi) — see `wayBelow_self_iff_scottOpen_Ici` for that — but it is a
standard
and useful fact, the openness of the sets `↟x`.)
@isnad1 id=scottope.0h2v.s4.0a17b102c996 from=translated src=- shape=a07958af vocab=900eaf3f
-/
theorem scottOpen_wayBelow (x : D) : ScottOpen {z | x ≪ z} := by
  refine ⟨fun a b hab ha => ha.trans_le hab, fun S hS hSdir hmem => ?_⟩
  obtain ⟨U, hU, hsupU, hsub⟩ := hmem
  obtain ⟨s, hsS, hsU⟩ := hU.2 hS hSdir hsupU
  exact ⟨s, hsS, ⟨U, hU, hsU, hsub⟩⟩

/-- **Scott 1972, Proposition 2.2(vi).** `x ≪ x` iff the principal up-set `{z | x
⊑ z}` (i.e.
`Set.Ici x`) is Scott-open. This characterizes the *compact* (finite, isolated)
elements:
`x` is compact exactly when `↑x` is open.
@isnad1 id=iff.0h2v.s4.3a11714338d5 from=translated src=- shape=cecfa3da vocab=633ef7b0
-/
theorem wayBelow_self_iff_scottOpen_Ici {x : D} : x ≪ x ↔ ScottOpen (Set.Ici x) := by
  constructor
  · rintro ⟨U, hU, hxU, hsub⟩
    -- `Ici x = U`: `Ici x ⊆ U` since `U` is upper and `x ∈ U`; `U ⊆ Ici x` is
    -- `hsub`.
    have hIci : Set.Ici x = U :=
      le_antisymm (fun w hw => hU.1 (Set.mem_Ici.1 hw) hxU) hsub
    rw [hIci]; exact hU
  · intro hopen
    exact ⟨Set.Ici x, hopen, Set.self_mem_Ici, le_refl _⟩

/-- **Scott 1972, Proposition 2.2(vii).** For a non-empty directed set `S`, `x ≪
⊔S` iff
`x ≪ y` for some `y ∈ S`. The forward direction is exactly inaccessibility of a
Scott-open
set; the backward direction is monotonicity on the right.
@isnad1 id=iff.2h3v.s6.6bd0a8ce58f0 from=translated src=- shape=9a447cda vocab=190f9aee
-/
theorem wayBelow_sSup_iff {x : D} {S : Set D} (hS : S.Nonempty)
    (hSdir : DirectedOn (· ≤ ·) S) : x ≪ sSup S ↔ ∃ y ∈ S, x ≪ y := by
  constructor
  · rintro ⟨U, hU, hsupU, hsub⟩
    obtain ⟨s, hsS, hsU⟩ := hU.2 hS hSdir hsupU
    exact ⟨s, hsS, U, hU, hsU, hsub⟩
  · rintro ⟨y, hyS, hxy⟩
    exact hxy.trans_le (le_sSup hyS)

/-- **Scott 1972, Definition 2.3.** A complete lattice `D` is a *continuous
lattice* when every
element is the supremum of the elements way below it: `y = ⊔ {x | x ≪ y}`. -/
def IsContinuousLattice (D : Type*) [CompleteLattice D] : Prop :=
  ∀ y : D, IsLUB {x | x ≪ y} y

/-- In a continuous lattice, `y` is the actual supremum of `{x | x ≪ y}`.
@isnad1 id=eq.1h2v.s4.c14154eb269a from=translated src=- shape=2fc11c6f vocab=ea96ec8d
-/
theorem IsContinuousLattice.sSup_wayBelow (h : IsContinuousLattice D) (y : D) :
    sSup {x | x ≪ y} = y :=
  (h y).sSup_eq

/-- The set `{x | x ≪ y}` of elements way below `y` is directed: it is closed
under binary
joins by Proposition 2.2(ii) (`WayBelow.sup`). This holds in *any* complete
lattice.
@isnad1 id=directed.0h2v.s5.4f758fbcca44 from=translated src=- shape=726e7c2e vocab=be622dff
-/
theorem directedOn_wayBelow (y : D) : DirectedOn (· ≤ ·) {x | x ≪ y} :=
  fun a ha b hb => ⟨a ⊔ b, ha.sup hb, le_sup_left, le_sup_right⟩

/-- **Interpolation property of `≪`.** In a continuous lattice, the way-below
relation
interpolates: `a ≪ c` implies there is some `b` with `a ≪ b ≪ c`.

The proof runs Scott's standard argument: the set `M = {m | ∃ x, m ≪ x ∧ x ≪ c}`
is directed
(using directedness of `{· ≪ x}` twice) and has supremum `c` (using continuity
twice). Hence
`a ≪ c = ⊔M` with `M` directed forces `a ≪ m` for some `m ∈ M`, say `m ≪ x ≪ c`;
then
`a ≪ m ≤ x` gives `a ≪ x ≪ c`, so `b := x` works.
@isnad1 id=ex.2h3v.s5.fbcd666b8c0f from=translated src=- shape=f90ba9eb vocab=d3ab5caf
-/
theorem wayBelow_interpolate (hD : IsContinuousLattice D) {a c : D} (hac : a ≪ c) :
    ∃ b, a ≪ b ∧ b ≪ c := by
  set M : Set D := {m | ∃ x, m ≪ x ∧ x ≪ c} with hM
  have hMdir : DirectedOn (· ≤ ·) M := by
    rintro m₁ ⟨x₁, hm₁x₁, hx₁c⟩ m₂ ⟨x₂, hm₂x₂, hx₂c⟩
    obtain ⟨x₃, hx₃c, hx₁₃, hx₂₃⟩ := directedOn_wayBelow c x₁ hx₁c x₂ hx₂c
    obtain ⟨m₃, hm₃x₃, hm₁m₃, hm₂m₃⟩ :=
      directedOn_wayBelow x₃ m₁ (hm₁x₁.trans_le hx₁₃) m₂ (hm₂x₂.trans_le hx₂₃)
    exact ⟨m₃, ⟨x₃, hm₃x₃, hx₃c⟩, hm₁m₃, hm₂m₃⟩
  have hMne : M.Nonempty := ⟨⊥, a, bot_wayBelow a, hac⟩
  have hsupM : sSup M = c := by
    refine le_antisymm (sSup_le ?_) ?_
    · rintro m ⟨x, hmx, hxc⟩
      exact hmx.le.trans hxc.le
    · rw [← hD.sSup_wayBelow c]
      refine sSup_le fun x hxc => ?_
      rw [← hD.sSup_wayBelow x]
      exact sSup_le fun m hmx => le_sSup ⟨x, hmx, hxc⟩
  rw [← hsupM] at hac
  obtain ⟨m, ⟨x, hmx, hxc⟩, ham⟩ := (wayBelow_sSup_iff hMne hMdir).1 hac
  exact ⟨x, ham.trans_le hmx.le, hxc⟩

/-- In a continuous lattice the sets `↟a = {z | a ≪ z}` form a basis of the Scott
topology:
every Scott-open `U` containing `z` contains some basic neighbourhood `↟a` of `z`.
Indeed
`z = ⊔{a | a ≪ z}` is a directed supremum lying in the open set `U`, so some `a ≪
z` already
lies in `U`, and then `↟a ⊆ ↑a ⊆ U`.
@isnad1 id=ex.3h3v.s5.168d5578eb40 from=translated src=- shape=ee4c5fc7 vocab=113e68d1
-/
theorem exists_wayBelow_subset (hD : IsContinuousLattice D) {U : Set D} (hU : ScottOpen U)
    {z : D} (hz : z ∈ U) : ∃ a, a ≪ z ∧ {w | a ≪ w} ⊆ U := by
  have hne : {a | a ≪ z}.Nonempty := ⟨⊥, bot_wayBelow z⟩
  have hsup : sSup {a | a ≪ z} ∈ U := by rw [hD.sSup_wayBelow z]; exact hz
  obtain ⟨a, haz, haU⟩ := hU.2 hne (directedOn_wayBelow z) hsup
  exact ⟨a, haz, fun w hw => hU.1 hw.le haU⟩

/-- A strengthening of `exists_wayBelow_subset`: the witness `a ≪ z` can be taken
with the whole
principal up-set `Set.Ici a` (not merely `↟a`) inside `U`. The element `a`
produced lies in the
open `U`, which is upper, so `↑a ⊆ U`.
@isnad1 id=ex.3h3v.s5.a444e61cd171 from=translated src=- shape=dab9f9a9 vocab=4b6ca78b
-/
theorem exists_wayBelow_Ici_subset (hD : IsContinuousLattice D) {U : Set D} (hU : ScottOpen U)
    {z : D} (hz : z ∈ U) : ∃ a, a ≪ z ∧ Set.Ici a ⊆ U := by
  have hne : {a | a ≪ z}.Nonempty := ⟨⊥, bot_wayBelow z⟩
  have hsup : sSup {a | a ≪ z} ∈ U := by rw [hD.sSup_wayBelow z]; exact hz
  obtain ⟨a, haz, haU⟩ := hU.2 hne (directedOn_wayBelow z) hsup
  exact ⟨a, haz, fun w hw => hU.1 (Set.mem_Ici.1 hw) haU⟩

/-- The infimum of a Scott-open neighbourhood of `y` is way below `y`: the open
set is itself
the required witness. Scott uses this in moving between Definition 2.3 and
Proposition 2.4.
@isnad1 id=waybelow.2h3v.s5.c85158f4c101 from=translated src=- shape=2d507a90 vocab=ad337000
-/
theorem sInf_wayBelow {U : Set D} (hU : ScottOpen U) {y : D} (hy : y ∈ U) :
    sInf U ≪ y :=
  ⟨U, hU, hy, fun _ hz => Set.mem_Ici.2 (sInf_le hz)⟩

/-- **Scott 1972, Proposition 2.4.** A complete lattice is continuous iff every
element is the
supremum of the infima of its open neighbourhoods: `y = ⊔ {⊓U : y ∈ U open}`. This
is Scott's
alternate form of Definition 2.3.
@isnad1 id=iff.0h1v.s5.d98a9599f79b from=translated src=- shape=c48ee13e vocab=325a29ec
-/
theorem isContinuousLattice_iff_isLUB_sInf_nhds :
    IsContinuousLattice D ↔
      ∀ y : D, IsLUB {a : D | ∃ U, ScottOpen U ∧ y ∈ U ∧ a = sInf U} y := by
  constructor
  · intro h y
    refine ⟨?_, ?_⟩
    · rintro a ⟨U, hU, hyU, rfl⟩
      exact (sInf_wayBelow hU hyU).le
    · intro b hb
      refine (h y).2 ?_
      intro x hx
      obtain ⟨U, hU, hyU, hsub⟩ := hx
      have hxle : x ≤ sInf U := le_sInf fun _ hz => Set.mem_Ici.1 (hsub hz)
      exact hxle.trans (hb ⟨U, hU, hyU, rfl⟩)
  · intro h y
    refine ⟨fun x hx => hx.le, ?_⟩
    intro b hb
    refine (h y).2 ?_
    rintro a ⟨U, hU, hyU, rfl⟩
    exact hb (sInf_wayBelow hU hyU)

end Domain.ContinuousLattice
