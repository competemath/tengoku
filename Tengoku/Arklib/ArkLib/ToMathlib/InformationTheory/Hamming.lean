/-
Copyright (c) 2026 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alexander Hicks
-/
module

public import Tengoku.Seed.InformationTheory.Hamming

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hamming distance under coordinate reindexing

`hammingDist_comp` transports the *alphabet* along an injection `α → β`. This file adds the
transport of the *coordinate index*: precomposition with an index equivalence is a Hamming
isometry.

Intended as a candidate for upstreaming to `Mathlib.InformationTheory.Hamming`, next to
`hammingDist_comp`.
-/

@[expose] public section
namespace Tengoku.Arklib end Tengoku.Arklib open Tengoku.Arklib 
/-- Reindexing the coordinates by an equivalence preserves Hamming distance.
@isnad1 id=eq.0h6v.s6.e71c375e950e from=translated src=- shape=dc66c231 vocab=f7b016dd
-/
theorem _root_.Tengoku.Arklib.hammingDist_comp_equiv {ι ι' α : Type*} [Fintype ι] [Fintype ι'] [DecidableEq α]
    (e : ι' ≃ ι) (x y : ι → α) :
    hammingDist (x ∘ e) (y ∘ e) = hammingDist x y := by
  unfold hammingDist
  apply Finset.card_nbij' (fun i' => e i') (fun i => e.symm i)
  · intro i' hi'; simpa using hi'
  · intro i hi; simpa using hi
  · intro i' hi'; simp
  · intro i hi; simp
-- Tengoku: root names of this library moved to Tengoku.Arklib so they do not collide with other libraries (generated)
