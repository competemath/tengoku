/-
Copyright (c) 2026 Catskills Research Company. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Catskills Research Company
-/
module

public import Tengoku.LeanPool.LeanPool.DomainTheory.Neighborhood.FunctionSpace
public import Tengoku

/-!
# Exercise 3.28 (Scott 1981, PRG-19, §3) — the elementwise formula for the least
map

In `(𝒟₀ → 𝒟₁)`, let `⋂ {[Xᵢ, Yᵢ] ∣ i < n}` be a non-empty neighbourhood.
Proposition 3.9
characterizes its minimal element `f₀` as a *relation* (`leastMap`, `X f₀ Y ↔ ⋂{Yᵢ
∣ X ⊆ Xᵢ} ⊆ Y`).
Exercise 3.28 asks for the **elementwise** description:

`f₀(x) = ⊔ { ↑Yᵢ ∣ x ∈ [Xᵢ] }`  for `x ∈ |𝒟₀|`,

where `x ∈ [Xᵢ]` means `Xᵢ ∈ x` (the input is at least as defined as `Xᵢ`). We
formalize this as
`toElementMap_leastMap_eq_sSup`: `f₀(x)` is the least upper bound (Exercise 1.27's
`sSup`) of the
principal filters `↑Yᵢ` over the active indices.

The proof shows `f₀(x)` is *the* least upper bound of that set: it is an upper
bound
(`val_le_leastMap_toElementMap`, from `Yᵢ ∈ f₀(x)`), and it is least
(`leastMap_toElementMap_le_of_ub`, because any upper bound contains every relevant
`Yᵢ`, hence the
finite intersection `⋂{Yᵢ ∣ X ⊆ Xᵢ}`); the equality with `⊔` then follows by
antisymmetry.

Everything is **choice-free** (`#print axioms ⊆ {propext, Quot.sound}`).
-/

@[expose] public section

namespace Domain.Neighborhood

open NeighborhoodSystem ApproximableMap

variable {α β : Type*} {V₀ : NeighborhoodSystem α} {V₁ : NeighborhoodSystem β}

/-- A filter `z` contains the finite intersection `⋂{Yᵢ ∣ X ⊆ Xᵢ}` (inside `Δ₁`)
as soon as it
contains each `Yᵢ` whose input `Xᵢ ⊇ X`. (The element-side analogue of
`rel_interYs`.)
@isnad1 id=mem.1h6v.s6.658aa9320dfb from=translated src=- shape=39a7cdf5 vocab=8712c064
-/
theorem Element.mem_interYs_of (z : V₁.Element) {L : List (Set α × Set β)} {X : Set α}
    (hall : ∀ p ∈ L, X ⊆ p.1 → z.mem p.2) : z.mem (interYs V₁.master L X) := by
  induction L with
  | nil => exact z.master_mem
  | cons p L ih =>
    have htail : ∀ q ∈ L, X ⊆ q.1 → z.mem q.2 :=
      fun q hq => hall q (List.mem_cons.mpr (Or.inr hq))
    by_cases hXp : X ⊆ p.1
    · have heq : interYs V₁.master (p :: L) X = p.2 ∩ interYs V₁.master L X := by
        rw [interYs_cons]; simp_all
      rw [heq]
      exact z.inter_mem (hall p (List.mem_cons.mpr (Or.inl rfl)) hXp) (ih htail)
    · have heq : interYs V₁.master (p :: L) X = interYs V₁.master L X := by
        rw [interYs_cons]; simp_all
      simp_all

/-- **Exercise 3.28 — the active values.** The set `{ ↑Yᵢ ∣ x ∈ [Xᵢ] }` of
principal filters whose
input `Xᵢ` is a member of `x`. -/
def leastMapVals (L : List (Set α × Set β)) (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (x : V₀.Element) : Set V₁.Element :=
  {z | ∃ (p : Set α × Set β) (hp : p ∈ L), x.mem p.1 ∧ z = V₁.principal (hL p hp).2}

/-- Each active value `↑Yᵢ` (with `Xᵢ ∈ x`) approximates `f₀(x)`, because `Yᵢ ∈
f₀(x)`.
@isnad1 id=le.4h7v.s7.853266ec36bc from=translated src=- shape=ba4cfada vocab=d67aeacc
-/
theorem val_le_leastMap_toElementMap {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {x : V₀.Element}
    {p : Set α × Set β} (hp : p ∈ L) (hp1x : x.mem p.1) :
    V₁.principal (hL p hp).2 ≤ (leastMap L hcons).toElementMap x := by
  have hmem : ((leastMap L hcons).toElementMap x).mem p.2 :=
    ⟨p.1, hp1x, leastMap_mem_stepFun hL hcons p hp⟩
  intro Z hZ
  exact ((leastMap L hcons).toElementMap x).up_mem hmem hZ.1 hZ.2

/-- The active values are bounded (by `f₀(x)`).
@isnad1 id=bounded.2h6v.s6.42984fe52bc9 from=translated src=- shape=b9f81adb vocab=ffe9e227
-/
theorem leastMapVals_bounded {L : List (Set α × Set β)} (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) (x : V₀.Element) :
    V₁.Bounded (leastMapVals L hL x) := by
  refine ⟨(leastMap L hcons).toElementMap x, ?_⟩
  rintro w ⟨p, hp, hp1x, rfl⟩
  exact val_le_leastMap_toElementMap hL hcons hp hp1x

/-- `f₀(x)` is a *lower* bound of the upper bounds: any upper bound `z` of the
active values
dominates `f₀(x)`. (Uses that `z` then contains `⋂{Yᵢ ∣ X ⊆ Xᵢ}`.)
@isnad1 id=le.3h7v.s7.0b810a9fbb4c from=translated src=- shape=276b6980 vocab=1c1dfdce
-/
theorem leastMap_toElementMap_le_of_ub {L : List (Set α × Set β)}
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) {x : V₀.Element} {z : V₁.Element}
    (hz : ∀ w ∈ leastMapVals L hL x, w ≤ z) :
    (leastMap L hcons).toElementMap x ≤ z := by
  rintro Y' ⟨X', hX'x, hX'mem, hY'mem, hsub⟩
  have hzint : z.mem (interYs V₁.master L X') := by
    apply Element.mem_interYs_of
    intro p hp hX'p
    have hp1x : x.mem p.1 := x.up_mem hX'x (hL p hp).1 hX'p
    have hle : V₁.principal (hL p hp).2 ≤ z := hz _ ⟨p, hp, hp1x, rfl⟩
    exact hle p.2 ⟨(hL p hp).2, subset_rfl⟩
  exact z.up_mem hzint hY'mem hsub

/-- **Exercise 3.28 (Scott 1981, PRG-19).** The least map's elementwise action is
the least upper
bound of the active principal filters: `f₀(x) = ⊔ { ↑Yᵢ ∣ x ∈ [Xᵢ] }`.
@isnad1 id=eq.2h6v.s6.705d901d9eb0 from=translated src=- shape=2bf527a3 vocab=ca8bd84c
-/
theorem toElementMap_leastMap_eq_sSup (L : List (Set α × Set β))
    (hL : ∀ p ∈ L, V₀.mem p.1 ∧ V₁.mem p.2)
    (hcons : ∀ {X}, V₀.mem X → V₁.mem (interYs V₁.master L X)) (x : V₀.Element) :
    (leastMap L hcons).toElementMap x
      = V₁.sSup (leastMapVals L hL x) (leastMapVals_bounded hL hcons x) := by
  apply le_antisymm
  · apply leastMap_toElementMap_le_of_ub hL hcons
    intro w hw
    exact V₁.le_sSup _ (leastMapVals_bounded hL hcons x) hw
  · apply V₁.sSup_le
    rintro w ⟨p, hp, hp1x, rfl⟩
    exact val_le_leastMap_toElementMap hL hcons hp hp1x

end Domain.Neighborhood
