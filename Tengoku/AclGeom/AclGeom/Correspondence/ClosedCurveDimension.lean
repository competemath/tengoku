/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Codex
-/
import Tengoku.Seed.Topology.KrullDimension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A closed subspace of full finite dimension in an irreducible space

Named consumer: the equality of nested translated curves in the general-group proof of
blueprint `lem:curve-coset`. A closed embedding into an irreducible finite-dimensional space
is surjective when its source has at least the target's dimension. No Noetherian or sober
hypothesis is needed: append the whole target to a chain in a hypothetical proper closed image.

**Status:** proved. The general source consumer is `curveCoset_of_genericProduct`.
-/

namespace AclGeom

open Set TopologicalSpace Topology

/-- A closed embedding of full finite dimension into an irreducible space is surjective.
The named source consumer is the equality of the translated curves in `lem:curve-coset`.
@isnad1 id=surjecti.3h4v.s6.75f14aeaf350 from=translated src=- shape=50836866 vocab=3c579a4d
-/
theorem surjective_of_isClosedEmbedding_of_finite_topologicalKrullDim
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] [IrreducibleSpace X]
    {f : Y → X} (hf : IsClosedEmbedding f) (n : ℕ)
    (hY : (n : WithBot ℕ∞) ≤ topologicalKrullDim Y)
    (hX : topologicalKrullDim X ≤ n) : Function.Surjective f := by
  classical
  by_contra hnot
  let F : IrreducibleCloseds Y → IrreducibleCloseds X :=
    IrreducibleCloseds.map f hf.continuous
  have hF : StrictMono F :=
    IrreducibleCloseds.map_strictMono_of_isInducing hf.isEmbedding.isInducing
  let T : IrreducibleCloseds X := ⟨univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hsub (S : IrreducibleCloseds Y) : (F S : Set X) ⊆ range f := by
    change closure (f '' (S : Set Y)) ⊆ range f
    exact closure_minimal (image_subset_range _ _) hf.isClosed_range
  have hlt (S : IrreducibleCloseds Y) : F S < T := by
    refine lt_of_le_of_ne (fun x _ ↦ mem_univ x) ?_
    intro heq
    apply hnot
    intro x
    have hx : x ∈ (F S : Set X) := by
      rw [heq]
      exact mem_univ x
    exact hsub S hx
  obtain ⟨p, hp⟩ := (Order.le_krullDim_iff (α := IrreducibleCloseds Y) (n := n)).1 hY
  let q : LTSeries (IrreducibleCloseds X) := (p.map F hF).snoc T (hlt _)
  have hlen : q.length = n + 1 := by
    change p.length + 1 = n + 1
    rw [hp]
  have hbad : ((n + 1 : ℕ) : WithBot ℕ∞) ≤ n := by
    calc
      _ = (q.length : WithBot ℕ∞) := congrArg (fun m : ℕ ↦ (m : WithBot ℕ∞)) hlen.symm
      _ ≤ topologicalKrullDim X := Order.LTSeries.length_le_krullDim q
      _ ≤ n := hX
  exact (not_le_of_gt (show (n : WithBot ℕ∞) < ((n + 1 : ℕ) : WithBot ℕ∞) by
    exact_mod_cast Nat.lt_succ_self n)) hbad

/-- Nested closed subspaces of equal finite dimension agree when the larger is irreducible.
The translated curves in the general curve-coset argument are the named consumer.-/
theorem eq_of_subset_of_finite_topologicalKrullDim
    {X : Type*} [TopologicalSpace X] {A D : Set X}
    (hA : IsClosed A) (hDi : IsIrreducible D) (hAD : A ⊆ D) (n : ℕ)
    (hD : topologicalKrullDim D = n) (hAn : topologicalKrullDim A = n) : A = D := by
  have : IrreducibleSpace D := Subtype.irreducibleSpace hDi
  have hf : IsClosedEmbedding (Set.inclusion hAD) :=
    IsClosedEmbedding.inclusion hAD (hA.preimage continuous_subtype_val)
  have hs := surjective_of_isClosedEmbedding_of_finite_topologicalKrullDim hf n
    hAn.symm.le hD.le
  refine Set.Subset.antisymm hAD ?_
  intro x hx
  obtain ⟨a, ha⟩ := hs ⟨x, hx⟩
  have he : (a : X) = x := congrArg Subtype.val ha
  rw [← he]
  exact a.property

end AclGeom
