/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.Proposition612
public import Tengoku

/-!
# Lecture VI — Exercise 6.25 (Scott 1981, PRG-19): the Galois connection of a
projection pair

**Exercise 6.25.** For a projection pair `g : 𝒟 → ℰ` and `h : ℰ → 𝒟` show that for
`x ∈ |𝒟|` and
`y ∈ |ℰ|` we have

`g(x) ⊑ y ↔ x ⊑ h(y)`.

Thus conclude

`h(y) = ⊔ {x ∈ |𝒟| ∣ g(x) ⊑ y}`   and   `g(x) = ⊓ {y ∈ |ℰ| ∣ x ⊑ h(y)}`,

so each of the two functions determines the other. Check that the set in the first
equation is
directed, and that the set in the second is non-empty. Prove also that `g` maps
consistent sets to
consistent sets and **preserves `⊔`** (not just *directed* unions).

## Dictionary to the codebase

Scott's `g` is the injection `i` and his `h` is the projection `j` of Proposition
6.12; we carry
them abstractly in `Subsystem.ProjectionPair 𝒟 ℰ` (fields `inj = g`, `proj = h`)
together with the
two defining laws

* `proj_comp_inj : h ∘ g = I_𝒟`  (`P.proj.comp P.inj = idMap 𝒟`), and
* `inj_comp_proj_le : g ∘ h ⊆ I_ℰ`  (`P.inj.comp P.proj ≤ idMap ℰ`).

On *elements* (`toElementMap`) these read `h(g(x)) = x` (`proj_inj_apply`) and
`g(h(y)) ⊑ y`
(`inj_proj_apply_le`); everything below is a short consequence of these two facts
plus monotonicity
of approximable maps on elements (`toElementMap_mono`).

* `galois` — the adjunction `g(x) ⊑ y ↔ x ⊑ h(y)`.
* `proj_eq_sSup` / `lowerSet_directed` — `h(y) = ⊔ {x ∣ g(x) ⊑ y}`; the set is a
down-set of
  `h(y)`, hence directed and bounded by `h(y)`.
* `inj_eq_sInf` — `g(x) = ⊓ {y ∣ x ⊑ h(y)}`; the set is an up-set of `g(x)`, hence
non-empty
  (it contains `g(x)`).
* `inj_bounded` — `g` maps bounded ("consistent") sets to bounded sets.
* `inj_sSup` — `g` preserves **all** existing least upper bounds: `g(⊔S) = ⊔ {g(s)
∣ s ∈ S}`.
  This is the hallmark of a lower adjoint and is the substance of the last
  sentence of the exercise.

Everything here is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`): the
`sSup`/`sInf` of
Exercises 1.18/1.27 are the only constructions used and are themselves
choice-free.
-/

@[expose] public section

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap Subsystem

variable {α : Type*} {D E : NeighborhoodSystem α}

namespace Subsystem.ProjectionPair

/-- **`h(g(x)) = x`.** The first projection-pair law `h ∘ g = I_𝒟`, read on
elements.
@isnad1 id=eq.0h5v.s5.2b7bb6aa6fa5 from=translated src=- shape=b897e510 vocab=cecee026
-/
theorem proj_inj_apply (P : ProjectionPair D E) (x : D.Element) :
    P.proj.toElementMap (P.inj.toElementMap x) = x := by
  rw [← toElementMap_comp, P.proj_comp_inj, toElementMap_idMap]

/-- **`g(h(y)) ⊑ y`.** The second projection-pair law `g ∘ h ⊆ I_ℰ`, read on
elements.
@isnad1 id=le.0h5v.s5.25d57f09c688 from=translated src=- shape=0046158f vocab=1eb0e882
-/
theorem inj_proj_apply_le (P : ProjectionPair D E) (y : E.Element) :
    P.inj.toElementMap (P.proj.toElementMap y) ≤ y := by
  have h := (le_iff_toElementMap_le.mp P.inj_comp_proj_le) y
  rwa [toElementMap_comp, toElementMap_idMap] at h

/-- **Exercise 6.25, the Galois connection.** For `x ∈ |𝒟|`, `y ∈ |ℰ|`:
`g(x) ⊑ y ↔ x ⊑ h(y)`. So `g` (lower adjoint) and `h` (upper adjoint) determine
each other.

`→`: apply the monotone `h` to `g(x) ⊑ y` and use `h(g(x)) = x`.
`←`: apply the monotone `g` to `x ⊑ h(y)` and use `g(h(y)) ⊑ y`.
@isnad1 id=iff.0h6v.s6.d9f87a4bb591 from=translated src=- shape=8a4ac37b vocab=1eb0e882
-/
theorem galois (P : ProjectionPair D E) (x : D.Element) (y : E.Element) :
    P.inj.toElementMap x ≤ y ↔ x ≤ P.proj.toElementMap y := by
  constructor
  · intro hxy
    have := P.proj.toElementMap_mono hxy
    rwa [P.proj_inj_apply x] at this
  · intro hxy
    exact (P.inj.toElementMap_mono hxy).trans (P.inj_proj_apply_le y)

/-! ### First extremal formula: `h(y) = ⊔ {x ∣ g(x) ⊑ y}`. -/

/-- The set `{x ∈ |𝒟| ∣ g(x) ⊑ y}` of the first formula. By the Galois connection
it is the
down-set `{x ∣ x ⊑ h(y)}` of `h(y)`. -/
def lowerSet (P : ProjectionPair D E) (y : E.Element) : Set D.Element :=
  {x | P.inj.toElementMap x ≤ y}

/--
@isnad1 id=iff.0h6v.s6.212f0e4406f9 from=translated src=- shape=a2889175 vocab=8123f69b
-/
@[simp] theorem mem_lowerSet (P : ProjectionPair D E) {y : E.Element} {x : D.Element} :
    x ∈ P.lowerSet y ↔ P.inj.toElementMap x ≤ y := Iff.rfl

/-- The set `{x ∣ g(x) ⊑ y}` is bounded: `h(y)` is an upper bound (it is in fact
the top).
@isnad1 id=bounded.0h5v.s4.26cd9a6bcb1c from=translated src=- shape=8aa31085 vocab=54354252
-/
theorem lowerSet_bounded (P : ProjectionPair D E) (y : E.Element) :
    D.Bounded (P.lowerSet y) :=
  ⟨P.proj.toElementMap y, fun _ hx => (P.galois _ y).mp hx⟩

/-- **Exercise 6.25 — "check that the set on the right is directed".** Any two
members of
`{x ∣ g(x) ⊑ y}` have a common upper bound *inside the set*, namely `h(y)` itself
(the down-set of
`h(y)` has `h(y)` as a top, so it is trivially directed).
@isnad1 id=ex.2h7v.s7.d991f7376aca from=translated src=- shape=4339709f vocab=e4324705
-/
theorem lowerSet_directed (P : ProjectionPair D E) (y : E.Element) :
    ∀ a ∈ P.lowerSet y, ∀ b ∈ P.lowerSet y,
      ∃ c ∈ P.lowerSet y, a ≤ c ∧ b ≤ c := by
  intro a ha b hb
  exact ⟨P.proj.toElementMap y, P.inj_proj_apply_le y,
    (P.galois a y).mp ha, (P.galois b y).mp hb⟩

/-- **Exercise 6.25, first extremal formula.** `h(y) = ⊔ {x ∈ |𝒟| ∣ g(x) ⊑ y}`.

`h(y)` is the *greatest* member of the set (`g(h(y)) ⊑ y`, so `h(y)` is in it;
every member is
`⊑ h(y)` by the Galois connection), hence it is the least upper bound.
@isnad1 id=eq.0h5v.s5.41a1e4c71bfc from=translated src=- shape=1cec0af6 vocab=8affa281
-/
theorem proj_eq_sSup (P : ProjectionPair D E) (y : E.Element) :
    P.proj.toElementMap y = D.sSup (P.lowerSet y) (P.lowerSet_bounded y) := by
  apply le_antisymm
  · exact D.le_sSup _ (P.lowerSet_bounded y) (P.inj_proj_apply_le y)
  · exact D.sSup_le _ (P.lowerSet_bounded y) fun x hx => (P.galois x y).mp hx

/-! ### Second extremal formula: `g(x) = ⊓ {y ∣ x ⊑ h(y)}`. -/

/-- The set `{y ∈ |ℰ| ∣ x ⊑ h(y)}` of the second formula. By the Galois connection
it is the
up-set `{y ∣ g(x) ⊑ y}` of `g(x)`. -/
def upperSet (P : ProjectionPair D E) (x : D.Element) : Set E.Element :=
  {y | x ≤ P.proj.toElementMap y}

/--
@isnad1 id=iff.0h6v.s6.70fb07570f20 from=translated src=- shape=c476aa00 vocab=e5f5d9ae
-/
@[simp] theorem mem_upperSet (P : ProjectionPair D E) {x : D.Element} {y : E.Element} :
    y ∈ P.upperSet x ↔ x ≤ P.proj.toElementMap y := Iff.rfl

/-- **Exercise 6.25 — "check that the set on the right is non-empty".** `g(x)`
itself lies in
`{y ∣ x ⊑ h(y)}`, since `x ⊑ h(g(x)) = x`.
@isnad1 id=nonempty.0h5v.s4.17fccd20c0c8 from=translated src=- shape=9ab17579 vocab=9180c8ea
-/
theorem upperSet_nonempty (P : ProjectionPair D E) (x : D.Element) :
    (P.upperSet x).Nonempty :=
  ⟨P.inj.toElementMap x, by rw [mem_upperSet, P.proj_inj_apply x]⟩

/-- **Exercise 6.25, second extremal formula.** `g(x) = ⊓ {y ∈ |ℰ| ∣ x ⊑ h(y)}`.

`g(x)` is the *least* member of the set (`x ⊑ h(g(x)) = x`, so `g(x)` is in it;
every member is
`⊒ g(x)` by the Galois connection), hence it is the greatest lower bound.
@isnad1 id=eq.0h5v.s5.4a424c739a9f from=translated src=- shape=3f2573e5 vocab=026d0f8c
-/
theorem inj_eq_sInf (P : ProjectionPair D E) (x : D.Element) :
    P.inj.toElementMap x = E.sInf (P.upperSet x) (P.upperSet_nonempty x) := by
  apply le_antisymm
  · exact E.le_sInf _ (P.upperSet_nonempty x) _ fun y hy => (P.galois x y).mpr hy
  · refine E.sInf_le _ (P.upperSet_nonempty x) ?_
    rw [mem_upperSet, P.proj_inj_apply x]

/-! ### `g` preserves consistency and all least upper bounds. -/

/-- **Exercise 6.25 — `g` maps consistent sets to consistent sets.** "Consistent"
for sets of
elements is "bounded" (Exercise 1.27). If `S` is bounded by `b`, its image `{g(s)
∣ s ∈ S}` is
bounded by `g(b)` (monotonicity).
@isnad1 id=bounded.1h5v.s5.6dafdfcbeef4 from=translated src=- shape=751d4fd0 vocab=113f641a
-/
theorem inj_bounded (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S) :
    E.Bounded (P.inj.toElementMap '' S) := by
  obtain ⟨b, hb⟩ := hS
  refine ⟨P.inj.toElementMap b, ?_⟩
  rintro _ ⟨s, hs, rfl⟩
  exact P.inj.toElementMap_mono (hb s hs)

/-- **Exercise 6.25 — `g` preserves `⊔` (not just *directed* unions).** For any
bounded set `S`,
`g(⊔S) = ⊔ {g(s) ∣ s ∈ S}`. This is the characteristic property of a lower
adjoint.

* `⊒`: `g(⊔S)` is an upper bound of `{g(s)}` since `s ⊑ ⊔S` and `g` is monotone.
* `⊑`: by the Galois connection it suffices that `⊔S ⊑ h(⊔{g(s)})`, i.e. that each
`s ⊑ h(⊔{g(s)})`;
  by the Galois connection again this is `g(s) ⊑ ⊔{g(s)}`, true by `le_sSup`.
@isnad1 id=eq.1h5v.s6.313032ff6265 from=translated src=- shape=d7c42c7c vocab=f1bf4657
-/
theorem inj_sSup (P : ProjectionPair D E) {S : Set D.Element} (hS : D.Bounded S) :
    P.inj.toElementMap (D.sSup S hS) =
      E.sSup (P.inj.toElementMap '' S) (P.inj_bounded hS) := by
  apply le_antisymm
  · refine (P.galois _ _).mpr (D.sSup_le S hS fun s hs => ?_)
    refine (P.galois s _).mp ?_
    exact E.le_sSup _ (P.inj_bounded hS) ⟨s, hs, rfl⟩
  · refine E.sSup_le _ (P.inj_bounded hS) ?_
    rintro _ ⟨s, hs, rfl⟩
    exact P.inj.toElementMap_mono (D.le_sSup S hS hs)

end Subsystem.ProjectionPair

end Domain.Neighborhood
