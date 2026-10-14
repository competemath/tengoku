/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Definition610
public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Exercise222
public import Tengoku

/-!
# Lecture VI — Proposition 6.11 (Scott 1981, PRG-19): the subsystems of `E` form a
domain

**Proposition 6.11.** For a given neighbourhood system `E`, the set of subsystems

`{D ∣ D ◁ E}`

forms a domain in its own right.

Scott derives this as a one-line corollary of the remark preceding it: *the union
of a directed
family of subdomains of `E` is again a subdomain*. We make this precise using the
project's
**abstract representation theorem** (Exercise 2.22, `Exercise222.reprIso`): a
family `C` of sets
that is closed under (i) non-empty intersection and (ii) directed union is
order-isomorphic to a
domain `|reprSystem C|` — exactly the route used for "the open sets form a domain"
(Exercise 3.25)
and "the function space is a domain" (Exercise 3.27).

The faithful translation runs as follows. A subsystem `D ◁ E` is, by
`NeighborhoodSystem.ext` and
the standing `D.master = E.master`, completely determined by its **family of
neighbourhoods**
`{X ∣ D.mem X}`. So we represent the poset `({D ∣ D ◁ E}, ◁)` by the family

`subFam E = { {X ∣ D.mem X} ∣ D ◁ E } ⊆ 𝒫(𝒫(Δ))`,

ordered by `⊆`. By Scott's remark (`Subsystem.subsystem_iff_subset_of_common`) the
subdomain
relation `◁` between two subsystems of `E` is just inclusion of their
neighbourhood families, so
`({D ∣ D ◁ E}, ◁) ≃o (subFam E, ⊆)` (`subIso`). The two closure properties hold:

* **non-empty intersections** (`subFam_sInter_mem`): the intersection of a
non-empty family of
  subdomains is the subdomain `interSys` whose neighbourhoods are the common
  neighbourhoods;
* **directed unions** (`subFam_sUnion_mem`): the union of a directed family of
subdomains is the
  subdomain `unionSys` (Scott's remark) — directedness is used exactly to verify
  closure under
  consistent intersection.

The capstone `subsystemReprIso : {D ∣ D ◁ E} ≃o |reprSystem (subFam E) …|`
composes `subIso` with
`Exercise222.reprIso`, witnessing that the subsystems of `E` *are* (isomorphic to)
a domain.

**Axioms.** The combinatorial heart — `subFam` and its closure under
intersection/union, the
subsystem constructions `interSys`/`unionSys`, and `subIso` — is **choice-free**
(`#print axioms ⊆ {propext, Quot.sound}`). The final `subsystemReprIso` inherits
`Classical.choice`
solely through Exercise 2.22's representation isomorphism (the "for set theorists"
exercise, which
picks witnesses of non-emptiness and uses finite-set induction), exactly as
Exercise 3.27 does.
-/

@[expose] public section

namespace Domain.Neighborhood.Proposition611

open Domain.Neighborhood NeighborhoodSystem Set Domain.Neighborhood.Exercise222

variable {α : Type*}

/-! ### The representing family of neighbourhood-sets. -/

/-- The family of **neighbourhood-sets of subdomains of `E`**: a set of subsets of
`Δ` lies in
`subFam E` exactly when it is `{X ∣ D.mem X}` for some subsystem `D ◁ E`. This is
the concrete
family of sets that, by Exercise 2.22, represents `{D ∣ D ◁ E}` as a domain. -/
def subFam (E : NeighborhoodSystem α) : Set (Set (Set α)) :=
  {𝒮 | ∃ D : NeighborhoodSystem α, D ◁ E ∧ 𝒮 = {X | D.mem X}}

/-- The master `Δ = E.master` belongs to the neighbourhood-set of any subdomain (a
subsystem shares
`E`'s master and contains it).
@isnad1 id=mem.1h3v.s5.f9485f7b5256 from=translated src=- shape=87220944 vocab=05559139
-/
theorem subFam_master_mem (E : NeighborhoodSystem α) {𝒮 : Set (Set α)}
    (h : 𝒮 ∈ subFam E) : E.master ∈ 𝒮 := by
  obtain ⟨D, hD, rfl⟩ := h
  rw [← hD.master_eq]
  exact D.master_mem

/-- Every member of a subdomain's neighbourhood-set is an `E`-neighbourhood (`D ⊆
E`).
@isnad1 id=mem.2h4v.s5.800b43b3b3c3 from=translated src=- shape=c43f5939 vocab=12ed5501
-/
theorem subFam_mem_E (E : NeighborhoodSystem α) {𝒮 : Set (Set α)} {X : Set α}
    (h : 𝒮 ∈ subFam E) (hX : X ∈ 𝒮) : E.mem X := by
  obtain ⟨D, hD, rfl⟩ := h
  exact hD.sub hX

/-- Consistency is inherited from `E` (Definition 6.10's essential clause): if `X,
Y` lie in a
subdomain's neighbourhood-set and `X ∩ Y ∈ E`, then `X ∩ Y` lies in it too.
@isnad1 id=mem.4h5v.s6.9bd9fdc6479f from=translated src=- shape=4bc424ef vocab=2cb873ae
-/
theorem subFam_inter_closed (E : NeighborhoodSystem α) {𝒮 : Set (Set α)} {X Y : Set α}
    (h : 𝒮 ∈ subFam E) (hX : X ∈ 𝒮) (hY : Y ∈ 𝒮) (hXY : E.mem (X ∩ Y)) : X ∩ Y ∈ 𝒮 := by
  obtain ⟨D, hD, rfl⟩ := h
  exact hD.inter_closed hX hY hXY

/-- `subFam E` is non-empty: `E` itself is a subsystem (`Subsystem.refl`), so its
own
neighbourhood-set `{X ∣ E.mem X}` is a member.
@isnad1 id=nonempty.0h2v.s3.02a0b045e316 from=translated src=- shape=736a821b vocab=c204a04a
-/
theorem subFam_nonempty (E : NeighborhoodSystem α) : (subFam E).Nonempty :=
  ⟨{X | E.mem X}, E, Subsystem.refl E, rfl⟩

/-! ### Closure under non-empty intersection. -/

/-- The **intersection subdomain** of a non-empty family `ℱ` of subdomain
neighbourhood-sets: its
neighbourhoods are the sets common to *every* member of `ℱ`. -/
def interSys (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : NeighborhoodSystem α where
  mem X := ∀ 𝒮 ∈ ℱ, X ∈ 𝒮
  master := E.master
  master_mem := fun 𝒮 h𝒮 => subFam_master_mem E (hℱ h𝒮)
  inter_mem := by
    intro X Y Z hX hY hZ hsub 𝒮 h𝒮
    have hEX : E.mem X := subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮)
    have hEY : E.mem Y := subFam_mem_E E (hℱ h𝒮) (hY 𝒮 h𝒮)
    have hEZ : E.mem Z := subFam_mem_E E (hℱ h𝒮) (hZ 𝒮 h𝒮)
    exact subFam_inter_closed E (hℱ h𝒮) (hX 𝒮 h𝒮) (hY 𝒮 h𝒮) (E.inter_mem hEX hEY hEZ hsub)
  sub_master := by
    intro X hX
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact E.sub_master (subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮))

/-- The intersection subdomain is a subsystem of `E`.
@isnad1 id=subsyste.2h3v.s5.4f582e64bbe2 from=translated src=- shape=c516dd80 vocab=3e141280
-/
theorem interSys_subsystem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : interSys E ℱ hne hℱ ◁ E where
  master_eq := rfl
  sub := by
    intro X hX
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact subFam_mem_E E (hℱ h𝒮) (hX 𝒮 h𝒮)
  inter_closed := by
    intro X Y hX hY hEXY 𝒮 h𝒮
    exact subFam_inter_closed E (hℱ h𝒮) (hX 𝒮 h𝒮) (hY 𝒮 h𝒮) hEXY

/-- The neighbourhood-set of the intersection subdomain is exactly `⋂₀ ℱ`.
@isnad1 id=eq.2h3v.s5.4e7171345581 from=translated src=- shape=36a472f0 vocab=70574ce1
-/
theorem interSys_nbset (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) :
    {X | (interSys E ℱ hne hℱ).mem X} = ⋂₀ ℱ := by
  ext X
  exact Set.mem_sInter.symm

/-- **Closure under non-empty intersection** (Exercise 2.22's hypothesis (i)).
@isnad1 id=mem.2h3v.s5.4f6c1020a421 from=translated src=- shape=48642849 vocab=4ec5fa56
-/
theorem subFam_sInter_mem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) : ⋂₀ ℱ ∈ subFam E :=
  ⟨interSys E ℱ hne hℱ, interSys_subsystem E ℱ hne hℱ, (interSys_nbset E ℱ hne hℱ).symm⟩

/-! ### Closure under directed union (Scott's remark). -/

/-- The **union subdomain** of a directed family `ℱ` of subdomain
neighbourhood-sets: its
neighbourhoods are those lying in *some* member of `ℱ`. Directedness is what makes
this closed
under consistent intersection. -/
def unionSys (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    NeighborhoodSystem α where
  mem X := ∃ 𝒮 ∈ ℱ, X ∈ 𝒮
  master := E.master
  master_mem := by
    obtain ⟨𝒮, h𝒮⟩ := hne
    exact ⟨𝒮, h𝒮, subFam_master_mem E (hℱ h𝒮)⟩
  inter_mem := by
    intro X Y Z hX hY hZ hsub
    obtain ⟨𝒮x, h𝒮x, hXx⟩ := hX
    obtain ⟨𝒮y, h𝒮y, hYy⟩ := hY
    obtain ⟨𝒮z, h𝒮z, hZz⟩ := hZ
    obtain ⟨𝒮s, h𝒮s, hxs, hys⟩ := hdir 𝒮x h𝒮x 𝒮y h𝒮y
    have hXs : X ∈ 𝒮s := hxs hXx
    have hYs : Y ∈ 𝒮s := hys hYy
    have hEX : E.mem X := subFam_mem_E E (hℱ h𝒮s) hXs
    have hEY : E.mem Y := subFam_mem_E E (hℱ h𝒮s) hYs
    have hEZ : E.mem Z := subFam_mem_E E (hℱ h𝒮z) hZz
    exact ⟨𝒮s, h𝒮s, subFam_inter_closed E (hℱ h𝒮s) hXs hYs (E.inter_mem hEX hEY hEZ hsub)⟩
  sub_master := by
    intro X hX
    obtain ⟨𝒮, h𝒮, hX𝒮⟩ := hX
    exact E.sub_master (subFam_mem_E E (hℱ h𝒮) hX𝒮)

/-- The union subdomain is a subsystem of `E` (Scott's remark: the directed union
of subdomains is
again a subdomain).
@isnad1 id=subsyste.3h3v.s5.e27330ac4829 from=translated src=- shape=3b84efda vocab=8d766427
-/
theorem unionSys_subsystem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    unionSys E ℱ hne hℱ hdir ◁ E where
  master_eq := rfl
  sub := by
    intro X hX
    obtain ⟨𝒮, h𝒮, hX𝒮⟩ := hX
    exact subFam_mem_E E (hℱ h𝒮) hX𝒮
  inter_closed := by
    intro X Y hX hY hEXY
    obtain ⟨𝒮x, h𝒮x, hXx⟩ := hX
    obtain ⟨𝒮y, h𝒮y, hYy⟩ := hY
    obtain ⟨𝒮s, h𝒮s, hxs, hys⟩ := hdir 𝒮x h𝒮x 𝒮y h𝒮y
    exact ⟨𝒮s, h𝒮s, subFam_inter_closed E (hℱ h𝒮s) (hxs hXx) (hys hYy) hEXY⟩

/-- The neighbourhood-set of the union subdomain is exactly `⋃₀ ℱ`.
@isnad1 id=eq.3h3v.s6.5b2cedd40ff6 from=translated src=- shape=967f9116 vocab=d027cfb1
-/
theorem unionSys_nbset (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    {X | (unionSys E ℱ hne hℱ hdir).mem X} = ⋃₀ ℱ := by
  ext X
  exact Set.mem_sUnion.symm

/-- **Closure under directed union** (Exercise 2.22's hypothesis (ii)) — Scott's
remark.
@isnad1 id=mem.3h3v.s6.1664f1743649 from=translated src=- shape=5c333f3a vocab=eabe0756
-/
theorem subFam_sUnion_mem (E : NeighborhoodSystem α) (ℱ : Set (Set (Set α)))
    (hne : ℱ.Nonempty) (hℱ : ℱ ⊆ subFam E) (hdir : DirectedOn (· ⊆ ·) ℱ) :
    ⋃₀ ℱ ∈ subFam E :=
  ⟨unionSys E ℱ hne hℱ hdir, unionSys_subsystem E ℱ hne hℱ hdir,
    (unionSys_nbset E ℱ hne hℱ hdir).symm⟩

/-! ### The poset of subsystems and its representation. -/

/-- The subsystems of `E`, ordered by the **subdomain relation** `◁`, form a
partial order
(reflexive, transitive, antisymmetric — Definition 6.10's API). -/
instance subPartialOrder (E : NeighborhoodSystem α) :
    PartialOrder {D : NeighborhoodSystem α // D ◁ E} where
  le D₀ D₁ := D₀.1 ◁ D₁.1
  le_refl D := Subsystem.refl D.1
  le_trans _ _ _ h₁ h₂ := h₁.trans h₂
  le_antisymm _ _ h₁ h₂ := Subtype.ext (h₁.antisymm h₂)

/-- Rebuild a subsystem of `E` from its neighbourhood-set `𝒮 ∈ subFam E`. The data
(the `mem`
predicate `· ∈ 𝒮` and the master `E.master`) depends only on `𝒮`; the proof
obligations are
discharged from `subFam` membership. -/
def ofMem (E : NeighborhoodSystem α) (𝒮 : Set (Set α)) (h : 𝒮 ∈ subFam E) :
    NeighborhoodSystem α where
  mem X := X ∈ 𝒮
  master := E.master
  master_mem := subFam_master_mem E h
  inter_mem := by
    intro X Y Z hX hY hZ hsub
    exact subFam_inter_closed E h hX hY
      (E.inter_mem (subFam_mem_E E h hX) (subFam_mem_E E h hY) (subFam_mem_E E h hZ) hsub)
  sub_master := fun hX => E.sub_master (subFam_mem_E E h hX)

/-- `ofMem` lands in the subsystems of `E`.
@isnad1 id=subsyste.1h3v.s5.5dc852ec7226 from=translated src=- shape=91652080 vocab=c192d95c
-/
theorem ofMem_subsystem (E : NeighborhoodSystem α) (𝒮 : Set (Set α)) (h : 𝒮 ∈ subFam E) :
    ofMem E 𝒮 h ◁ E where
  master_eq := rfl
  sub := subFam_mem_E E h
  inter_closed := subFam_inter_closed E h

/-- **The poset of subsystems is the family `subFam E`.** The subsystems of `E`,
ordered by `◁`,
are order-isomorphic to `subFam E` ordered by `⊆`. A subsystem is sent to its
family of
neighbourhoods `{X ∣ D.mem X}`, and recovered by `ofMem`; order is preserved and
reflected by
Scott's remark `Subsystem.subsystem_iff_subset_of_common`. -/
def subIso (E : NeighborhoodSystem α) :
    {D : NeighborhoodSystem α // D ◁ E} ≃o {𝒮 : Set (Set α) // 𝒮 ∈ subFam E} where
  toFun D := ⟨{X | D.1.mem X}, ⟨D.1, D.2, rfl⟩⟩
  invFun 𝒮 := ⟨ofMem E 𝒮.1 𝒮.2, ofMem_subsystem E 𝒮.1 𝒮.2⟩
  left_inv := by
    intro D
    apply Subtype.ext
    apply NeighborhoodSystem.ext
    · intro X; exact Iff.rfl
    · exact D.2.master_eq.symm
  right_inv := by
    intro 𝒮
    apply Subtype.ext
    ext X
    exact Iff.rfl
  map_rel_iff' := by
    intro a b
    change ({X | a.1.mem X} : Set (Set α)) ⊆ {X | b.1.mem X} ↔ a.1 ◁ b.1
    constructor
    · intro hsub
      refine (Subsystem.subsystem_iff_subset_of_common a.2 b.2).mpr ?_
      simp_all
    · intro hsub X hX
      exact hsub.sub hX

/-- **Proposition 6.11 (Scott 1981, PRG-19).** For a neighbourhood system `E`, the
set of
subsystems `{D ∣ D ◁ E}`, ordered by the subdomain relation `◁`, *forms a domain
in its own
right*: it is order-isomorphic to the domain `|reprSystem (subFam E) …|` produced
by the abstract
representation theorem (Exercise 2.22), using that `subFam E` is closed under
non-empty
intersections (`subFam_sInter_mem`) and directed unions (Scott's remark,
`subFam_sUnion_mem`). -/
def subsystemReprIso (E : NeighborhoodSystem α) :
    {D : NeighborhoodSystem α // D ◁ E} ≃o
      (reprSystem (subFam E) (subFam_sInter_mem E) (subFam_nonempty E)).Element :=
  (subIso E).trans
    (reprIso (subFam E) (subFam_sInter_mem E) (subFam_nonempty E) (subFam_sUnion_mem E)).symm

end Domain.Neighborhood.Proposition611
