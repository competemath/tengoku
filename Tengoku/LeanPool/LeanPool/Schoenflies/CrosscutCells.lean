/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Tengoku.LeanPool.LeanPool.Schoenflies.Curve
public import Tengoku.LeanPool.LeanPool.Schoenflies.Concatenate
public import Tengoku.LeanPool.LeanPool.Schoenflies.Topology

/-!
# Separating curves, absorption, and the two cells of a crosscut

Definition 2.4 calls a Jordan curve *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with the curve as its boundary. Everything Part I proves
about a polygonal curve and Part II proves about a general one is packaged in that single
predicate, and the two lemmas below are the ones needed on both sides of the divide: they are
proved from the definition alone.

## The interface: `inside` and `outside` are total functions

The blueprint writes `Int(C)` and `Ext(C)` for the two regions and its consumers — the two
crosscut theorems — name them in their *statements*. So the two regions must be functions of
`C`, not sets produced by an existential inside the definition of separation. They are defined
here for an arbitrary set: `inside C` is the union of the bounded components of the complement
and `outside C` the union of the unbounded ones; together they partition `Cᶜ`.
Separation is then the assertion that each of the two halves is *one* region with boundary `C`
(Definition 2.4); that one is bounded and the other unbounded is then automatic, and so is
"exactly two regions", since a connected clopen piece of `Cᶜ` is a component of it.

`IsRegionOf C Ω` says `Ω` is one of the two, and `IsRegionPair C Ω Ω'` that `Ω, Ω'` are the two
in one order or the other. That is what lets Lemma 2.6 be stated once instead of twice: the
blueprint's `Ω` is sometimes `Int(C)` and sometimes `Ext(C)`, and every step of its proof is
symmetric in that choice.

## What the crosscut lemma actually needs

Lemma 2.6 is stated for a crosscut `P` of a separating curve `C` with arcs `A₁, A₂`, but its
proof never uses that `P` and the `Aᵢ` are arcs, nor the endpoints `p, q`, nor even that
`C = A₁ ∪ A₂`. What it uses is: `Aᵢ ⊆ C`, `P ∩ C ⊆ Aᵢ` (the crosscut meets the curve only in
the shared endpoints, which lie on both arcs), `Jᵢ = Aᵢ ∪ P` separating, and `A₁ ≠ A₂`. The
lemmas below are therefore stated at that level of generality, with `arcs_ne` supplying
`A₁ ≠ A₂` from the arc picture and `isJordanCurve_union` supplying the sentence "these are
Jordan curves" from `IsJordanCurve.of_two_arcs`.

One further hypothesis of the blueprint is dropped: `Ω` is described there as the region
containing `P ∖ {p, q}`, but what actually pins the roles of `Ω`, `Ω†`, `Wᵢ` and `Vᵢ` is the
inclusion `Ω† ⊆ Wᵢ`, which is a hypothesis here. A consumer supplies it by
`IsSeparating.exists_isRegionPair_subset`, which is the formal content of the blueprint's
"being connected it lies in one region of `ℝ² ∖ Jᵢ`, so `Wᵢ` and `Vᵢ` are well defined".

## Blueprint

* `inside`, `outside`, `IsSeparating` — Definition 2.4 (separating Jordan curve).
* `IsSeparating.absorption` — Lemma 2.5 (absorption).
* `crosscut_cells` — Lemma 2.6 (crosscut cells), all three parts, with the per-part lemmas
  `cell_subset_region_diff`, `cell_isComponent`, `closure_cell_inter_curve` stated separately
  because the bundled form carries the hypotheses of both indices at once.
-/

@[expose] public section

open Bornology Set

namespace Schoenflies

variable {C J P A A₁ A₂ Ω Ω' W V : Set Plane} {x p q : Plane}

/-! ### The inside and the outside of a set

Both are defined for an arbitrary set, without any separation hypothesis: `inside C` collects
the points whose component in the complement is bounded, `outside C` the rest of the
complement. -/

/-- The union of the bounded components of the complement — the blueprint's `Int(C)` once `C`
is known to be separating. -/
def inside (C : Set Plane) : Set Plane :=
  {x | x ∉ C ∧ IsBounded (connectedComponentIn Cᶜ x)}

/-- The union of the unbounded components of the complement — the blueprint's `Ext(C)` once `C`
is known to be separating. -/
def outside (C : Set Plane) : Set Plane :=
  {x | x ∉ C ∧ ¬ IsBounded (connectedComponentIn Cᶜ x)}

/--
@isnad1 id=iff.0h2v.s6.68c3393cae6b from=translated src=- shape=69bbd1b6 vocab=d52adc92
-/
theorem mem_inside_iff : x ∈ inside C ↔ x ∉ C ∧ IsBounded (connectedComponentIn Cᶜ x) := Iff.rfl

/--
@isnad1 id=iff.0h2v.s6.fb9d0f774bad from=translated src=- shape=4b73cc7a vocab=d4076474
-/
theorem mem_outside_iff : x ∈ outside C ↔ x ∉ C ∧ ¬ IsBounded (connectedComponentIn Cᶜ x) :=
  Iff.rfl

/--
@isnad1 id=le.0h1v.s4.d1192cdaaecc from=translated src=- shape=90c803c0 vocab=17cd338a
-/
theorem inside_subset_compl : inside C ⊆ Cᶜ := fun _ hx => hx.1

/--
@isnad1 id=le.0h1v.s4.8fff90baa4d2 from=translated src=- shape=90c803c0 vocab=67e208b1
-/
theorem outside_subset_compl : outside C ⊆ Cᶜ := fun _ hx => hx.1

/--
@isnad1 id=eq.0h1v.s4.dd0ae6458a75 from=translated src=- shape=f3ab5751 vocab=a36dc13b
-/
theorem inside_union_outside (C : Set Plane) : inside C ∪ outside C = Cᶜ := by
  ext z
  constructor
  · rintro (⟨hz, -⟩ | ⟨hz, -⟩) <;> exact hz
  · intro hz
    by_cases hb : IsBounded (connectedComponentIn Cᶜ z)
    · exact Or.inl ⟨hz, hb⟩
    · exact Or.inr ⟨hz, hb⟩

/--
@isnad1 id=disjoint.0h1v.s5.49ab02734ac7 from=translated src=- shape=90cedf2a vocab=3a0ad5e8
-/
theorem disjoint_inside_outside : Disjoint (inside C) (outside C) := by
  rw [Set.disjoint_left]
  rintro z ⟨-, hb⟩ ⟨-, hb'⟩
  exact hb' hb

/-- Boundedness of the component is constant along a component, so the inside is a union of
whole components.
@isnad1 id=le.1h2v.s6.e06ccbefad8c from=translated src=- shape=bd20f0d1 vocab=5d8d84ea
-/
theorem connectedComponentIn_subset_inside (hx : x ∈ inside C) :
    connectedComponentIn Cᶜ x ⊆ inside C := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact hx.2

/--
@isnad1 id=le.1h2v.s6.e5d707d060fc from=translated src=- shape=bd20f0d1 vocab=2f1dab13
-/
theorem connectedComponentIn_subset_outside (hx : x ∈ outside C) :
    connectedComponentIn Cᶜ x ⊆ outside C := by
  intro z hz
  refine ⟨connectedComponentIn_subset _ _ hz, ?_⟩
  rw [← connectedComponentIn_eq hz]
  exact hx.2

/-- A union of components of an open set is open.
@isnad1 id=isopen.1h1v.s6.3b24d5865f74 from=translated src=- shape=73379b06 vocab=cffa462d
-/
theorem isOpen_inside (hC : IsClosed C) : IsOpen (inside C) := by
  rw [isOpen_iff_forall_mem_open]
  exact fun z hz => ⟨connectedComponentIn Cᶜ z, connectedComponentIn_subset_inside hz,
    Plane.isOpen_connectedComponentIn hC.isOpen_compl, mem_connectedComponentIn hz.1⟩

/--
@isnad1 id=isopen.1h1v.s6.7c17ba8c6005 from=translated src=- shape=73379b06 vocab=fe0b1a77
-/
theorem isOpen_outside (hC : IsClosed C) : IsOpen (outside C) := by
  rw [isOpen_iff_forall_mem_open]
  exact fun z hz => ⟨connectedComponentIn Cᶜ z, connectedComponentIn_subset_outside hz,
    Plane.isOpen_connectedComponentIn hC.isOpen_compl, mem_connectedComponentIn hz.1⟩

/-! ### Definition 2.4: a separating Jordan curve -/

/-- Definition 2.4. A Jordan curve is *separating* when its complement has exactly two regions,
one bounded and one unbounded, each with boundary `C`.

Since `inside C` and `outside C` always partition the complement into the bounded-component
part and the unbounded-component part, "exactly two regions, one bounded and one unbounded"
says precisely that each part is a single region; and the boundedness of one and unboundedness
of the other are then consequences rather than hypotheses (`IsSeparating.isBounded_inside`,
`IsSeparating.not_isBounded_outside`). -/
structure IsSeparating (C : Set Plane) : Prop where
  /-- The set is a Jordan curve. -/
  isJordanCurve : IsJordanCurve C
  /-- The bounded part of the complement is a single region. -/
  isConnected_inside : IsConnected (inside C)
  /-- The unbounded part of the complement is a single region. -/
  isConnected_outside : IsConnected (outside C)
  /-- The inside has the curve as its boundary. -/
  frontier_inside : frontier (inside C) = C
  /-- The outside has the curve as its boundary. -/
  frontier_outside : frontier (outside C) = C

namespace IsSeparating

/--
@isnad1 id=isclosed.1h1v.s5.cd7489fa801f from=translated src=- shape=f3db9897 vocab=994fbb3b
-/
theorem isClosed (h : IsSeparating C) : IsClosed C := h.isJordanCurve.isClosed

/--
@isnad1 id=isopen.1h1v.s5.e660eb4f5c00 from=translated src=- shape=314ae98c vocab=715404ac
-/
theorem isOpen_inside (h : IsSeparating C) : IsOpen (Schoenflies.inside C) :=
  Schoenflies.isOpen_inside h.isClosed

/--
@isnad1 id=isopen.1h1v.s5.3a63002bc164 from=translated src=- shape=314ae98c vocab=93668101
-/
theorem isOpen_outside (h : IsSeparating C) : IsOpen (Schoenflies.outside C) :=
  Schoenflies.isOpen_outside h.isClosed

/-- The inside is bounded: it is connected and lies inside the complement, hence inside the
component of any of its points, which is bounded by definition of `inside`.
@isnad1 id=isbounde.1h1v.s5.12a0ad66a649 from=translated src=- shape=314ae98c vocab=0a701576
-/
theorem isBounded_inside (h : IsSeparating C) : IsBounded (Schoenflies.inside C) := by
  obtain ⟨z, hz⟩ := h.isConnected_inside.nonempty
  exact hz.2.subset
    (h.isConnected_inside.isPreconnected.subset_connectedComponentIn hz inside_subset_compl)

/-- The outside is unbounded: it contains an unbounded component.
@isnad1 id=not.1h1v.s5.04175a9032f8 from=translated src=- shape=0fc8dc4c vocab=09298985
-/
theorem not_isBounded_outside (h : IsSeparating C) : ¬ IsBounded (Schoenflies.outside C) := by
  obtain ⟨z, hz⟩ := h.isConnected_outside.nonempty
  exact fun hb => hz.2 (hb.subset (connectedComponentIn_subset_outside hz))

/-- The inside really is one *region* of the complement, that is, a connected component of it:
it is a union of components which is itself connected. Together with its twin below this is
the "exactly two regions" clause of Definition 2.4.
@isnad1 id=eq.2h2v.s6.e90caf9025d0 from=translated src=- shape=f179dc08 vocab=8461eb02
-/
theorem connectedComponentIn_eq_inside (h : IsSeparating C) (hx : x ∈ Schoenflies.inside C) :
    connectedComponentIn Cᶜ x = Schoenflies.inside C :=
  Set.Subset.antisymm (connectedComponentIn_subset_inside hx)
    (h.isConnected_inside.isPreconnected.subset_connectedComponentIn hx inside_subset_compl)

/-- The outside is a connected component of the complement.
@isnad1 id=eq.2h2v.s6.9878416df175 from=translated src=- shape=f179dc08 vocab=36cddc0f
-/
theorem connectedComponentIn_eq_outside (h : IsSeparating C) (hx : x ∈ Schoenflies.outside C) :
    connectedComponentIn Cᶜ x = Schoenflies.outside C :=
  Set.Subset.antisymm (connectedComponentIn_subset_outside hx)
    (h.isConnected_outside.isPreconnected.subset_connectedComponentIn hx outside_subset_compl)

end IsSeparating

/-! ### The two regions, named

`IsRegionOf C Ω` is "`Ω` is a region of `ℝ² ∖ C`" and `IsRegionPair C Ω Ω'` is "`Ω` and `Ω'`
are *the* two regions". Both are stated without a separation hypothesis; the facts that make
them useful carry one. -/

/-- `Ω` is a region of the complement of `C`. -/
def IsRegionOf (C Ω : Set Plane) : Prop := Ω = inside C ∨ Ω = outside C

/-- `Ω` and `Ω'` are the two regions of the complement of `C`, in one order or the other. -/
def IsRegionPair (C Ω Ω' : Set Plane) : Prop :=
  (Ω = inside C ∧ Ω' = outside C) ∨ (Ω = outside C ∧ Ω' = inside C)

/-- Every component of the complement is one of the two regions: there are no others. This is
the last clause of "exactly two regions".
@isnad1 id=isregion.2h2v.s6.87a0590b4d02 from=translated src=- shape=01855be3 vocab=230d91ca
-/
theorem IsSeparating.isRegionOf_connectedComponentIn (h : IsSeparating C) (hx : x ∉ C) :
    IsRegionOf C (connectedComponentIn Cᶜ x) := by
  have hx' : x ∈ inside C ∪ outside C := by rw [inside_union_outside]; exact hx
  rcases hx' with hx' | hx'
  · exact Or.inl (h.connectedComponentIn_eq_inside hx')
  · exact Or.inr (h.connectedComponentIn_eq_outside hx')

namespace IsRegionOf

/--
@isnad1 id=isregion.0h1v.s2.227b49155bb7 from=translated src=- shape=802d6110 vocab=9ffa444f
-/
theorem inside (C : Set Plane) : IsRegionOf C (Schoenflies.inside C) := Or.inl rfl

/--
@isnad1 id=isregion.0h1v.s2.f20a45e75dd1 from=translated src=- shape=802d6110 vocab=76c0a00f
-/
theorem outside (C : Set Plane) : IsRegionOf C (Schoenflies.outside C) := Or.inr rfl

/--
@isnad1 id=le.1h2v.s4.22803ddf58e1 from=translated src=- shape=6c25268a vocab=8fff8af7
-/
theorem subset_compl (h : IsRegionOf C Ω) : Ω ⊆ Cᶜ := by
  rcases h with rfl | rfl
  · exact inside_subset_compl
  · exact outside_subset_compl

/--
@isnad1 id=isopen.2h2v.s5.398801665ecd from=translated src=- shape=476406cc vocab=641fb010
-/
theorem isOpen (h : IsRegionOf C Ω) (hC : IsSeparating C) : IsOpen Ω := by
  rcases h with rfl | rfl
  · exact hC.isOpen_inside
  · exact hC.isOpen_outside

/--
@isnad1 id=isconnec.2h2v.s5.d3f440275039 from=translated src=- shape=476406cc vocab=2548026e
-/
theorem isConnected (h : IsRegionOf C Ω) (hC : IsSeparating C) : IsConnected Ω := by
  rcases h with rfl | rfl
  · exact hC.isConnected_inside
  · exact hC.isConnected_outside

/-- A region is a connected component of the complement.
@isnad1 id=eq.3h3v.s6.56e00f861aa3 from=translated src=- shape=fdd11a26 vocab=230d91ca
-/
theorem connectedComponentIn_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) (hx : x ∈ Ω) :
    connectedComponentIn Cᶜ x = Ω := by
  rcases h with rfl | rfl
  · exact hC.connectedComponentIn_eq_inside hx
  · exact hC.connectedComponentIn_eq_outside hx

/--
@isnad1 id=eq.2h2v.s5.54f8bda3d046 from=translated src=- shape=2b527e6f vocab=f67ff14c
-/
theorem frontier_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) : frontier Ω = C := by
  rcases h with rfl | rfl
  · exact hC.frontier_inside
  · exact hC.frontier_outside

/-- Every point of the curve is a limit of points of the region: this is the half of
`frontier Ω = C` that absorption uses.
@isnad1 id=le.2h2v.s5.052dc9084018 from=translated src=- shape=b7c96f67 vocab=b86ce2b8
-/
theorem subset_closure (h : IsRegionOf C Ω) (hC : IsSeparating C) : C ⊆ closure Ω := by
  rw [← h.frontier_eq hC]
  exact frontier_subset_closure

/-- The closure of a region is the region together with the curve.
@isnad1 id=eq.2h2v.s6.453dab85c82d from=translated src=- shape=b3cc0cc5 vocab=87d84702
-/
theorem closure_eq (h : IsRegionOf C Ω) (hC : IsSeparating C) : closure Ω = Ω ∪ C := by
  have hfr := h.frontier_eq hC
  rw [(h.isOpen hC).frontier_eq] at hfr
  rw [← hfr, Set.union_sdiff_cancel _root_.subset_closure]

end IsRegionOf

namespace IsRegionPair

/--
@isnad1 id=isregion.1h3v.s4.75ab80b5a34b from=translated src=- shape=3c3f6799 vocab=e086b2b1
-/
theorem left (h : IsRegionPair C Ω Ω') : IsRegionOf C Ω := by
  rcases h with ⟨rfl, -⟩ | ⟨rfl, -⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/--
@isnad1 id=isregion.1h3v.s4.f2e765ec724e from=translated src=- shape=b4562e4e vocab=e086b2b1
-/
theorem right (h : IsRegionPair C Ω Ω') : IsRegionOf C Ω' := by
  rcases h with ⟨-, rfl⟩ | ⟨-, rfl⟩
  · exact Or.inr rfl
  · exact Or.inl rfl

/--
@isnad1 id=isregion.1h3v.s4.38ac78157cdd from=translated src=- shape=d00cff6e vocab=62c83480
-/
theorem symm (h : IsRegionPair C Ω Ω') : IsRegionPair C Ω' Ω := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact Or.inl ⟨rfl, rfl⟩

/--
@isnad1 id=eq.1h3v.s4.376eb2734a54 from=translated src=- shape=f9714d0f vocab=b1561fa3
-/
theorem union_eq (h : IsRegionPair C Ω Ω') : Ω ∪ Ω' = Cᶜ := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact inside_union_outside C
  · rw [Set.union_comm]
    exact inside_union_outside C

/--
@isnad1 id=disjoint.1h3v.s5.d590a7305ce3 from=translated src=- shape=38d94b79 vocab=938c7d51
-/
theorem disjoint (h : IsRegionPair C Ω Ω') : Disjoint Ω Ω' := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact disjoint_inside_outside
  · exact disjoint_inside_outside.symm

/-- A connected set off the curve and off one region lies in the other. This is the only place
where "exactly two regions" is used, and it is used in exactly that form.
@isnad1 id=le.6h4v.s6.3ff0a999621f from=translated src=- shape=0e9d7303 vocab=2a7fd639
-/
theorem subset_left_of_isPreconnected (h : IsRegionPair C Ω Ω') (hC : IsSeparating C)
    {S : Set Plane} (hS : IsPreconnected S) (hne : S.Nonempty) (hSC : S ⊆ Cᶜ)
    (hSΩ' : Disjoint S Ω') : S ⊆ Ω := by
  obtain ⟨z, hz⟩ := hne
  have hcover : S ⊆ Ω ∪ Ω' := by rw [h.union_eq]; exact hSC
  have hzΩ : z ∈ Ω := (hcover hz).resolve_right fun hz' => Set.disjoint_left.1 hSΩ' hz hz'
  exact hS.subset_left_of_subset_union (h.left.isOpen hC) (h.right.isOpen hC) h.disjoint hcover
    ⟨z, hz, hzΩ⟩

end IsRegionPair

/-- A nonempty connected set disjoint from the curve lies in one of the two regions. This is
the well-definedness clause of Lemma 2.6: "being connected it lies in one region of
`ℝ² ∖ Jᵢ`, so `Wᵢ` and `Vᵢ` are well defined".
@isnad1 id=ex.4h2v.s6.d9895ef42376 from=translated src=- shape=e6e10cb9 vocab=4e8b9931
-/
theorem IsSeparating.exists_isRegionPair_subset (hC : IsSeparating C) {S : Set Plane}
    (hS : IsPreconnected S) (hne : S.Nonempty) (hSC : Disjoint S C) :
    ∃ W V, IsRegionPair C W V ∧ S ⊆ W := by
  obtain ⟨z, hz⟩ := hne
  have hSc : S ⊆ Cᶜ := fun w hw => Set.disjoint_left.1 hSC hw
  have hcover : S ⊆ inside C ∪ outside C := by rw [inside_union_outside]; exact hSc
  by_cases hzin : z ∈ inside C
  · exact ⟨inside C, outside C, Or.inl ⟨rfl, rfl⟩,
      hS.subset_left_of_subset_union hC.isOpen_inside hC.isOpen_outside disjoint_inside_outside
        hcover ⟨z, hz, hzin⟩⟩
  · refine ⟨outside C, inside C, Or.inr ⟨rfl, rfl⟩, ?_⟩
    refine hS.subset_left_of_subset_union hC.isOpen_outside hC.isOpen_inside
      disjoint_inside_outside.symm ?_ ⟨z, hz, (hcover hz).resolve_left hzin⟩
    rw [Set.union_comm]
    exact hcover

/-! ### Lemma 2.5: absorption -/

/-- Lemma 2.5 (absorption), set-theoretic core. If every point of `C` is a limit of points of
`Ω`, and `Ω` sits inside an open `V` whose frontier lies in `J`, then `C` misses `V` only where
`J` does.
@isnad1 id=le.4h4v.s7.011ba3aa9003 from=translated src=- shape=c9bfe9f6 vocab=b6d6a81f
-/
theorem absorption_of_subset_closure (hCΩ : C ⊆ closure Ω) (hV : IsOpen V)
    (hfr : frontier V ⊆ J) (hsub : Ω ⊆ V) : C \ J ⊆ V := by
  rintro z ⟨hzC, hzJ⟩
  by_contra hzV
  -- `z` lies in the closure of `V` but not in `V`, so it lies on the frontier, hence in `J`.
  exact hzJ (hfr (by rw [hV.frontier_eq]; exact ⟨closure_mono hsub (hCΩ hzC), hzV⟩))

/-- Lemma 2.5 (absorption). If a region `Ω` of the complement of a separating curve `C` is
contained in a region `V` of the complement of a separating curve `J`, then all of `C` off `J`
lies in `V`.
@isnad1 id=le.5h4v.s5.479f54647a79 from=translated src=- shape=d35d6ad6 vocab=7dc2f0e8
-/
theorem IsSeparating.absorption (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionOf C Ω) (hV : IsRegionOf J V) (hsub : Ω ⊆ V) : C \ J ⊆ V :=
  absorption_of_subset_closure (hΩ.subset_closure hC) (hV.isOpen hJ)
    (hV.frontier_eq hJ).subset hsub

/-! ### Lemma 2.6: the two cells of a crosscut

The setting: `C` is a separating curve, `Ω` and `Ω'` its two regions, `J` a separating curve
with `P ⊆ J ⊆ C ∪ P`, and `W, V` the two regions of `ℝ² ∖ J`, with `Ω' ⊆ W`. The blueprint's
`J` is `Aᵢ ∪ P` for one of the two arcs `Aᵢ`; the proof only needs the two inclusions. -/

/-- The far region `Ω'` absorbs all of `C` off `J`, so the near cell `V` misses `C` entirely:
the part of `C` off `J` is in `W`, and the part on `J` is off `V` because `V` misses `J`.
@isnad1 id=disjoint.5h5v.s6.f2f2d819d684 from=translated src=- shape=d6bd3b24 vocab=39f0b0f0
-/
theorem disjoint_cell_curve (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ' : IsRegionOf C Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) : Disjoint V C := by
  have hCW : C \ J ⊆ W := hC.absorption hJ hΩ' hWV.left hΩW
  rw [Set.disjoint_left]
  intro z hzV hzC
  by_cases hzJ : z ∈ J
  · exact hWV.right.subset_compl hzV hzJ
  · exact Set.disjoint_left.1 hWV.symm.disjoint hzV (hCW ⟨hzC, hzJ⟩)

/-- Lemma 2.6, first half of (a): the cell `V` is contained in `Ω ∖ P`. It misses `C`, it is
connected, and it misses `Ω'` because `Ω' ⊆ W`; so it lies in `Ω`. It misses `P` because it
misses `J ⊇ P`.
@isnad1 id=le.6h7v.s6.6363d042b30c from=translated src=- shape=cc7171b0 vocab=2b211b18
-/
theorem cell_subset_region_diff (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionPair C Ω Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) (hPJ : P ⊆ J) : V ⊆ Ω \ P := by
  have hVC : Disjoint V C := disjoint_cell_curve hC hJ hΩ.right hWV hΩW
  have hVJ : V ⊆ Jᶜ := hWV.right.subset_compl
  -- `V` and `W` are the two regions of `ℝ² ∖ J`, and `Ω'` sits inside `W`.
  have hVΩ' : Disjoint V Ω' := hWV.symm.disjoint.mono_right hΩW
  have hVΩ : V ⊆ Ω :=
    hΩ.subset_left_of_isPreconnected hC (hWV.right.isConnected hJ).isPreconnected
      (hWV.right.isConnected hJ).nonempty (fun z hz => Set.disjoint_left.1 hVC hz) hVΩ'
  exact fun z hz => ⟨hVΩ hz, fun hzP => hVJ hz (hPJ hzP)⟩

/-- Lemma 2.6 (a): the cell `V` is a connected component of `Ω ∖ P`. Its frontier is `J`, which
lies in `C ∪ P` and so misses the open set `Ω ∖ P`; Lemma 1.7 does the rest.
@isnad1 id=eq.8h8v.s7.d0010f81bd2e from=translated src=- shape=0328c835 vocab=d2413ab2
-/
theorem cell_isComponent (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ : IsRegionPair C Ω Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) (hPJ : P ⊆ J) (hJCP : J ⊆ C ∪ P) :
    ∀ z ∈ V, connectedComponentIn (Ω \ P) z = V := by
  intro z hz
  refine Plane.connectedComponentIn_eq_of_frontier_disjoint (hWV.right.isOpen hJ)
    (hWV.right.isConnected hJ).isPreconnected
    (cell_subset_region_diff hC hJ hΩ hWV hΩW hPJ) ?_ hz
  rw [hWV.right.frontier_eq hJ]
  refine Set.eq_empty_iff_forall_notMem.2 ?_
  rintro w ⟨hwJ, hwΩ, hwP⟩
  rcases hJCP hwJ with hwC | hwP'
  · exact hΩ.left.subset_compl hwΩ hwC
  · exact hwP hwP'

/-- Lemma 2.6 (c): the closure of the cell meets `C` exactly in `J ∩ C`. The closure is
`V ∪ J`, and `V` misses `C`.
@isnad1 id=eq.5h5v.s6.f5e7b2d976e2 from=translated src=- shape=6a5937e3 vocab=ed33fc1a
-/
theorem closure_cell_inter_curve (hC : IsSeparating C) (hJ : IsSeparating J)
    (hΩ' : IsRegionOf C Ω') (hWV : IsRegionPair J W V)
    (hΩW : Ω' ⊆ W) : closure V ∩ C = J ∩ C := by
  have hVC : Disjoint V C := disjoint_cell_curve hC hJ hΩ' hWV hΩW
  rw [hWV.right.closure_eq hJ, Set.union_inter_distrib_right, hVC.inter_eq, Set.empty_union]

/-! ### The arc-level side conditions

Two small facts turn the blueprint's arc picture into the hypotheses the lemmas above take. -/

/-- The two curves of Lemma 2.6 are Jordan curves: an arc from `p` to `q` and a second arc from
`p` to `q` meeting it only at those two points glue to a Jordan curve.
@isnad1 id=isjordan.3h4v.s5.9a2acc59e6e4 from=translated src=- shape=fd7d17c6 vocab=f8068257
-/
theorem isJordanCurve_union (hA : IsArcBetween A p q) (hP : IsArcBetween P p q)
    (hmeet : ∀ z ∈ A, z ∈ P → z = p ∨ z = q) : IsJordanCurve (A ∪ P) :=
  IsJordanCurve.of_two_arcs hA hP.reverse hmeet

/-- Lemma 2.6 (b), arc side: the two arcs of `C` from `p` to `q` are distinct, because they
meet only at `p` and `q` while neither is just `{p, q}`.
@isnad1 id=ne.2h4v.s6.42b6a79c8269 from=translated src=- shape=28e1daaf vocab=18f2e8cf
-/
theorem arcs_ne (hmeet : A₁ ∩ A₂ ⊆ {p, q}) (hA : ¬ A₁ ⊆ {p, q}) : A₁ ≠ A₂ := by
  rintro rfl
  exact hA fun z hz => hmeet ⟨hz, hz⟩

/-! ### Lemma 2.6, bundled -/

/-- **Lemma 2.6 (crosscut cells).** Let `C` be a separating curve with regions `Ω` and `Ω'`,
let `A₁, A₂ ⊆ C` be the two arcs cut out by a crosscut `P` which meets `C` only in points of
both arcs, and suppose the two curves `Jᵢ = Aᵢ ∪ P` are separating. Let `Wᵢ` be the region of
`ℝ² ∖ Jᵢ` containing `Ω'` and `Vᵢ` the other one. Then

* (a) each `Vᵢ` is a connected component of `Ω ∖ P`;
* (b) `V₁ ≠ V₂`;
* (c) `closure Vᵢ ∩ C = Aᵢ`.

The blueprint proves (b) from the boundaries; here it falls straight out of (c), since
`V₁ = V₂` would make `A₁ = A₂`.
@isnad1 id=and.13h10v.s8.aa4e0671e100 from=translated src=- shape=00b93dad vocab=57981218
-/
theorem crosscut_cells (hC : IsSeparating C)
    (hJ₁ : IsSeparating (A₁ ∪ P)) (hJ₂ : IsSeparating (A₂ ∪ P))
    (hA₁ : A₁ ⊆ C) (hA₂ : A₂ ⊆ C) (hP₁ : P ∩ C ⊆ A₁) (hP₂ : P ∩ C ⊆ A₂) (hne : A₁ ≠ A₂)
    (hΩ : IsRegionPair C Ω Ω')
    {W₁ V₁ W₂ V₂ : Set Plane}
    (hWV₁ : IsRegionPair (A₁ ∪ P) W₁ V₁) (hΩW₁ : Ω' ⊆ W₁)
    (hWV₂ : IsRegionPair (A₂ ∪ P) W₂ V₂) (hΩW₂ : Ω' ⊆ W₂) :
    (V₁ ⊆ Ω \ P ∧ ∀ z ∈ V₁, connectedComponentIn (Ω \ P) z = V₁) ∧
      (V₂ ⊆ Ω \ P ∧ ∀ z ∈ V₂, connectedComponentIn (Ω \ P) z = V₂) ∧
      V₁ ≠ V₂ ∧ closure V₁ ∩ C = A₁ ∧ closure V₂ ∩ C = A₂ := by
  -- The two inclusions that replace the arc hypotheses.
  have hPJ : ∀ A : Set Plane, P ⊆ A ∪ P := fun A => Set.subset_union_right
  have hJCP : ∀ {A : Set Plane}, A ⊆ C → A ∪ P ⊆ C ∪ P := fun hA =>
    Set.union_subset_union_left P hA
  -- (c): `(Aᵢ ∪ P) ∩ C = Aᵢ`, since `Aᵢ ⊆ C` and `P ∩ C ⊆ Aᵢ`.
  have hinter : ∀ {A : Set Plane}, A ⊆ C → P ∩ C ⊆ A → (A ∪ P) ∩ C = A := by
    intro A hAC hPC
    refine Set.Subset.antisymm ?_ fun z hz => ⟨Or.inl hz, hAC hz⟩
    rintro z ⟨hz | hz, hzC⟩
    · exact hz
    · exact hPC ⟨hz, hzC⟩
  have hc₁ : closure V₁ ∩ C = A₁ := by
    rw [closure_cell_inter_curve hC hJ₁ hΩ.right hWV₁ hΩW₁]; exact hinter hA₁ hP₁
  have hc₂ : closure V₂ ∩ C = A₂ := by
    rw [closure_cell_inter_curve hC hJ₂ hΩ.right hWV₂ hΩW₂]; exact hinter hA₂ hP₂
  refine ⟨⟨cell_subset_region_diff hC hJ₁ hΩ hWV₁ hΩW₁ (hPJ A₁),
      cell_isComponent hC hJ₁ hΩ hWV₁ hΩW₁ (hPJ A₁) (hJCP hA₁)⟩,
    ⟨cell_subset_region_diff hC hJ₂ hΩ hWV₂ hΩW₂ (hPJ A₂),
      cell_isComponent hC hJ₂ hΩ hWV₂ hΩW₂ (hPJ A₂) (hJCP hA₂)⟩, ?_, hc₁, hc₂⟩
  -- (b): equal cells would have equal closures, hence equal arcs.
  rintro rfl
  exact hne (hc₁.symm.trans hc₂)

end Schoenflies
