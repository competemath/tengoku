/-
Copyright (c) 2026 Hara Seihun. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hara Seihun
-/
module

public import Tengoku.Seed.GroupTheory.GroupAction.Defs
public import Tengoku.Seed.GroupTheory.Perm.Subgroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Two-closures of permutation groups

The two-closure of a permutation group consists of the permutations that agree with an element of
the group on each ordered pair. This file defines the two-closure as a subgroup and proves its basic
closure-operator properties.
-/

public section

namespace Subgroup

variable {α : Type*}

/-- The two-closure of a permutation group. A permutation belongs to `twoClosure G` when, on every
ordered pair, it agrees with some element of `G`.-/
def twoClosure (G : Subgroup (Equiv.Perm α)) : Subgroup (Equiv.Perm α) where
  carrier := {q | ∀ x y, ∃ g ∈ G, g x = q x ∧ g y = q y}
  one_mem' := fun x y ↦ ⟨1, G.one_mem, by simp, by simp⟩
  mul_mem' := by
    intro q r hq hr x y
    obtain ⟨g, hg, hgx, hgy⟩ := hr x y
    obtain ⟨h, hh, hhx, hhy⟩ := hq (r x) (r y)
    refine ⟨h * g, G.mul_mem hh hg, ?_, ?_⟩
    · simpa [Equiv.Perm.mul_apply, hgx] using hhx
    · simpa [Equiv.Perm.mul_apply, hgy] using hhy
  inv_mem' := by
    intro q hq x y
    obtain ⟨g, hg, hgx, hgy⟩ := hq (q⁻¹ x) (q⁻¹ y)
    refine ⟨g⁻¹, G.inv_mem hg, ?_, ?_⟩
    · apply g.injective
      simpa using hgx.symm
    · apply g.injective
      simpa using hgy.symm

/-- Taking two-closures is monotone.-/
theorem twoClosure_mono : Monotone (twoClosure : Subgroup (Equiv.Perm α) →
    Subgroup (Equiv.Perm α)) := by
  intro G H hGH q hq x y
  obtain ⟨g, hg, hgx, hgy⟩ := hq x y
  exact ⟨g, hGH hg, hgx, hgy⟩

/-- Taking the two-closure twice has no further effect.-/
@[simp]
theorem twoClosure_twoClosure (G : Subgroup (Equiv.Perm α)) :
    G.twoClosure.twoClosure = G.twoClosure := by
  apply le_antisymm
  · intro q hq x y
    obtain ⟨h, hh, hhx, hhy⟩ := hq x y
    obtain ⟨g, hg, hgx, hgy⟩ := hh x y
    exact ⟨g, hg, hgx.trans hhx, hgy.trans hhy⟩
  · intro q hq x y
    exact ⟨q, hq, rfl, rfl⟩

/-- Membership in the two-closure is equivalent to preserving every binary relation that is
invariant under the original permutation group.-/
theorem mem_twoClosure_iff_preserves_invariant_binary_relations
    (G : Subgroup (Equiv.Perm α)) (q : Equiv.Perm α) :
    q ∈ G.twoClosure ↔
      ∀ R : Set (α × α),
        (∀ g ∈ G, ∀ x y, ((x, y) ∈ R ↔ (g x, g y) ∈ R)) →
          ∀ x y, ((x, y) ∈ R ↔ (q x, q y) ∈ R) := by
  constructor
  · intro hq R hR x y
    obtain ⟨g, hg, hgx, hgy⟩ := hq x y
    simpa [hgx, hgy] using hR g hg x y
  · intro hpres x y
    let R : Set (α × α) :=
      {z | ∃ g ∈ G, g x = z.1 ∧ g y = z.2}
    have hR : ∀ g ∈ G, ∀ u v,
        ((u, v) ∈ R ↔ (g u, g v) ∈ R) := by
      intro g hg u v
      constructor
      · rintro ⟨a, ha, hax, hay⟩
        refine ⟨g * a, G.mul_mem hg ha, ?_, ?_⟩
        · simp [Equiv.Perm.mul_apply, hax]
        · simp [Equiv.Perm.mul_apply, hay]
      · rintro ⟨a, ha, hax, hay⟩
        refine ⟨g⁻¹ * a, G.mul_mem (G.inv_mem hg) ha, ?_, ?_⟩
        · simpa [Equiv.Perm.mul_apply] using congrArg g.symm hax
        · simpa [Equiv.Perm.mul_apply] using congrArg g.symm hay
    have hxy : (x, y) ∈ R := ⟨1, G.one_mem, by simp, by simp⟩
    exact (hpres R hR x y).mp hxy

/-- The orbit of `x` under the stabilizer of `o` in a permutation group.-/
def pointStabilizerOrbit (G : Subgroup (Equiv.Perm α)) (o x : α) : Set α :=
  MulAction.orbit (MulAction.stabilizer G o) x

end Subgroup
