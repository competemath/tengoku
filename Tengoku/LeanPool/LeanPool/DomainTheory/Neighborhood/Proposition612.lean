/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Definition610
public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.FunctionSpace
public import Tengoku

/-!
# Lecture VI — Proposition 6.12 (Scott 1981, PRG-19): a subdomain yields a
projection pair

**Proposition 6.12.** If `D ◁ E`, then there exists a *projection pair* of
approximable mappings

`i : D → E` and `j : E → D`

with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`, determined as element-wise functions by

`i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}` and `j(y) = y ∩ D`.

Scott leaves the proof "for the exercises". We give it directly at the level of
the neighbourhood
relations (Definition 2.1), which keeps everything **choice-free**.

* The injection `i` (`Subsystem.inj`) is the relation `X i Y ↔ X ∈ D ∧ Y ∈ E ∧ X ⊆
Y` — it sends a
  `D`-neighbourhood to all the `E`-neighbourhoods it refines.
* The projection `j` (`Subsystem.proj`) is the relation `Y j X ↔ Y ∈ E ∧ X ∈ D ∧ Y
⊆ X` — it
  intersects an `E`-element with `D`.

The two laws are then short relational calculations:

* `Subsystem.proj_comp_inj : j ∘ i = I_D`. Both round trips factor as `X ⊆ Y ⊆ Z`,
giving exactly
  the identity relation `X ⊆ Z` on `D`. (Proved with the **choice-free**
  relational extensionality
  `ApproximableMap.ext`.)
* `Subsystem.inj_comp_proj_le : i ∘ j ⊆ I_E`. A round trip `Y ⊆ X ⊆ Y'` through a
common
  `D`-neighbourhood `X` is in particular `Y ⊆ Y'` on `E` — but not conversely, so
  this direction is
  only an inclusion. The crucial clause of `D ◁ E` (consistency inherited from
  `E`) is what makes
  `j`'s output-intersection law hold (`inter_right`).

The element-wise descriptions Scott records are `Subsystem.toElementMap_inj` and
`Subsystem.toElementMap_proj`.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

@[expose] public section

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α : Type*}

namespace Subsystem

variable {D E : NeighborhoodSystem α}

/-- **The injection `i : D → E` of Proposition 6.12.** As a neighbourhood
relation,
`X i Y ↔ X ∈ D ∧ Y ∈ E ∧ X ⊆ Y`. Element-wise (see `toElementMap_inj`) it is
Scott's
`i(x) = {Y ∈ E ∣ ∃ X ∈ x, X ⊆ Y}`. -/
def inj (h : D ◁ E) : ApproximableMap D E where
  rel X Y := D.mem X ∧ E.mem Y ∧ X ⊆ Y
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨D.master_mem, E.master_mem, h.master_eq.subset⟩
  inter_right := by
    rintro X Y Y' ⟨hX, hY, hXY⟩ ⟨_, hY', hXY'⟩
    exact ⟨hX, E.inter_mem hY hY' (h.sub hX) (Set.subset_inter hXY hXY'),
      Set.subset_inter hXY hXY'⟩
  mono := by
    rintro X X' Y Y' ⟨_, _, hXY⟩ hX'X hYY' hX' hY'
    exact ⟨hX', hY', (hX'X.trans hXY).trans hYY'⟩

/--
@isnad1 id=iff.1h5v.s5.c9e7928d5845 from=translated src=- shape=74f9ffae vocab=82b388f2
-/
@[simp] theorem inj_rel (h : D ◁ E) {X Y : Set α} :
    (h.inj).rel X Y ↔ D.mem X ∧ E.mem Y ∧ X ⊆ Y := Iff.rfl

/-- **The projection `j : E → D` of Proposition 6.12.** As a neighbourhood
relation,
`Y j X ↔ Y ∈ E ∧ X ∈ D ∧ Y ⊆ X`. Element-wise (see `toElementMap_proj`) it is
Scott's
`j(y) = y ∩ D`. The `inter_right` law is exactly where Definition 6.10's
consistency clause
(`inter_closed`) is used. -/
def proj (h : D ◁ E) : ApproximableMap E D where
  rel Y X := E.mem Y ∧ D.mem X ∧ Y ⊆ X
  rel_dom hr := hr.1
  rel_cod hr := hr.2.1
  master_rel := ⟨E.master_mem, D.master_mem, h.master_eq.symm.subset⟩
  inter_right := by
    rintro Y X X' ⟨hY, hX, hYX⟩ ⟨_, hX', hYX'⟩
    have hEinter : E.mem (X ∩ X') :=
      E.inter_mem (h.sub hX) (h.sub hX') hY (Set.subset_inter hYX hYX')
    exact ⟨hY, h.inter_closed hX hX' hEinter, Set.subset_inter hYX hYX'⟩
  mono := by
    rintro Y Y' X X' ⟨_, _, hYX⟩ hY'Y hXX' hY' hX'
    exact ⟨hY', hX', (hY'Y.trans hYX).trans hXX'⟩

/--
@isnad1 id=iff.1h5v.s5.84f43c5dd70f from=translated src=- shape=839cfdec vocab=67ab195a
-/
@[simp] theorem proj_rel (h : D ◁ E) {Y X : Set α} :
    (h.proj).rel Y X ↔ E.mem Y ∧ D.mem X ∧ Y ⊆ X := Iff.rfl

/-- **Element-wise description of `i` (Scott's equation).** `i(x) = {Y ∈ E ∣ ∃ X ∈
x, X ⊆ Y}`.
@isnad1 id=iff.1h5v.s5.71a342a306cc from=translated src=- shape=ac504f74 vocab=7df7f7b2
-/
theorem toElementMap_inj (h : D ◁ E) (x : D.Element) {Y : Set α} :
    (h.inj.toElementMap x).mem Y ↔ E.mem Y ∧ ∃ X, x.mem X ∧ X ⊆ Y := by
  constructor
  · rintro ⟨X, hX, _, hY, hXY⟩
    exact ⟨hY, X, hX, hXY⟩
  · rintro ⟨hY, X, hX, hXY⟩
    exact ⟨X, hX, x.sub hX, hY, hXY⟩

/-- **Element-wise description of `j` (Scott's equation).** `j(y) = y ∩ D`: the
neighbourhoods of
`j(y)` are exactly the `D`-neighbourhoods that already belong to `y`.
@isnad1 id=iff.1h5v.s5.faae7da08bb9 from=translated src=- shape=7c58b7fe vocab=0c3293db
-/
theorem toElementMap_proj (h : D ◁ E) (y : E.Element) {X : Set α} :
    (h.proj.toElementMap y).mem X ↔ y.mem X ∧ D.mem X := by
  constructor
  · rintro ⟨Y, hY, hEY, hX, hYX⟩
    exact ⟨y.up_mem hY (h.sub hX) hYX, hX⟩
  · rintro ⟨hX, hDX⟩
    exact ⟨X, hX, y.sub hX, hDX, subset_rfl⟩

/-- **Proposition 6.12, first law: `j ∘ i = I_D`.** Each side relates `X` and `Z`
exactly when
`X, Z ∈ D` and `X ⊆ Z`: a round trip `X ⊆ Y ⊆ Z` through an `E`-neighbourhood `Y`
collapses to
`X ⊆ Z` (forward), and `X ⊆ Z` factors through `Y = Z` (backward). Proved
relationally, so
**choice-free**.
@isnad1 id=eq.1h3v.s5.47773e1261ae from=translated src=- shape=83eb8320 vocab=7cfdc978
-/
theorem proj_comp_inj (h : D ◁ E) : h.proj.comp h.inj = idMap D := by
  apply ApproximableMap.ext
  intro X Z
  rw [comp_rel, idMap_rel]
  constructor
  · rintro ⟨Y, ⟨hX, _, hXY⟩, _, hZ, hYZ⟩
    exact ⟨hX, hZ, hXY.trans hYZ⟩
  · rintro ⟨hX, hZ, hXZ⟩
    exact ⟨Z, ⟨hX, h.sub hZ, hXZ⟩, h.sub hZ, hZ, subset_rfl⟩

/-- **Proposition 6.12, second law: `i ∘ j ⊆ I_E`.** A round trip `Y ⊆ X ⊆ Y'`
through a common
`D`-neighbourhood `X` is in particular `Y ⊆ Y'` on `E`. The reverse inclusion
fails (not every
consistent `E`-pair factors through `D`), so this is an inclusion of relations,
not an equality.
@isnad1 id=le.1h3v.s5.175b6d73245f from=translated src=- shape=ceb0016d vocab=cdb0fa96
-/
theorem inj_comp_proj_le (h : D ◁ E) : h.inj.comp h.proj ≤ idMap E := by
  intro Y Y' hr
  obtain ⟨X, ⟨hEY, _, hYX⟩, _, hEY', hXY'⟩ := hr
  exact ⟨hEY, hEY', hYX.trans hXY'⟩

/-- **A projection pair (Definition 6.13 vocabulary).** Bundles Scott's `i, j`
together with the two
laws, ready for reuse in monotone/continuous-on-domains functors and the existence
Theorem 6.14. -/
structure ProjectionPair (D E : NeighborhoodSystem α) where
  /-- The injection `i : D → E`. -/
  inj : ApproximableMap D E
  /-- The projection `j : E → D`. -/
  proj : ApproximableMap E D
  /-- `j ∘ i = I_D`. -/
  proj_comp_inj : proj.comp inj = idMap D
  /-- `i ∘ j ⊆ I_E`. -/
  inj_comp_proj_le : inj.comp proj ≤ idMap E

/-- **Proposition 6.12 (Scott 1981, PRG-19).** Every subdomain relation `D ◁ E`
gives rise to a
projection pair `i : D → E`, `j : E → D` with `j ∘ i = I_D` and `i ∘ j ⊆ I_E`. -/
def projectionPair (h : D ◁ E) : ProjectionPair D E where
  inj := h.inj
  proj := h.proj
  proj_comp_inj := h.proj_comp_inj
  inj_comp_proj_le := h.inj_comp_proj_le

end Subsystem

end Domain.Neighborhood
