/-
Copyright (c) 2026 Álvaro Begué. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Álvaro Begué
-/
module

public import Tengoku.LeanPool.LeanPool.Schoenflies.Square

/-!
# Catching a bounded set inside a square

The outer face of a plane graph is found by catching the whole drawing — finitely many points
and finitely many compact arcs — inside one axis-parallel square, and then observing that the
outside of that square is connected (`isConnected_beyondSquare`) and therefore lies in a single
face. This module is the "catching" half.

The key identity is `beyondSquare_eq_compl`: the outside of a square, as defined by a
coordinate inequality, *is* the complement of the closed square. It is what lets the
connectedness theorem be applied to a complement.

## Blueprint

* `beyondSquare_eq_compl` — the outside of a square is the complement of the closed square.
* `exists_closedSquare_of_isBounded`, `IsCompact.exists_closedSquare` — a bounded set is caught
  inside a square about the origin.
* `isOpen_compl_of_finite_isCompact` — the complement of a finite union of compact sets is
  open; the exterior of a plane graph is open for this reason.
-/

@[expose] public section

open Metric Set

namespace Schoenflies

namespace Plane

/--
@isnad1 id=eq.0h1v.s6.e70c76ae451b from=translated src=- shape=959a34e3 vocab=694b4f25
-/
@[simp] theorem supDist_zero (x : Plane) : supDist x 0 = supNorm x := by
  simp [supDist, supNorm]

/-- The outside of a square is exactly the complement of the closed square.
@isnad1 id=eq.0h1v.s6.27872a8e57db from=translated src=- shape=7d785e8e vocab=be26111c
-/
theorem beyondSquare_eq_compl (r : ℝ) : beyondSquare r = (closedSquare 0 r)ᶜ := by
  ext x
  simp only [beyondSquare, closedSquare, Set.mem_ofPred_eq, mem_compl_iff, supDist_zero, supNorm,
    max_le_iff, not_and_or, not_le]

/-- A bounded set sits inside a closed square about the origin, of nonnegative radius.
@isnad1 id=ex.1h1v.s7.5727722f74af from=translated src=- shape=1b62dab7 vocab=0b465be6
-/
theorem exists_closedSquare_of_isBounded {s : Set Plane} (hs : Bornology.IsBounded s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r := by
  obtain ⟨R, hR⟩ := hs.subset_closedBall 0
  refine ⟨max R 0, le_max_right _ _, fun x hx => ?_⟩
  have hnorm : ‖x‖ ≤ R := by simpa using hR hx
  have : supNorm x ≤ R := le_trans (supNorm_le_norm x) hnorm
  simpa [closedSquare, supDist_zero] using le_trans this (le_max_left _ _)

/--
@isnad1 id=ex.1h1v.s7.d48d4bfc1cd6 from=translated src=- shape=1b62dab7 vocab=2f75deba
-/
theorem IsCompact.exists_closedSquare {s : Set Plane} (hs : IsCompact s) :
    ∃ r : ℝ, 0 ≤ r ∧ s ⊆ closedSquare 0 r :=
  exists_closedSquare_of_isBounded hs.isBounded

/-- Two squares about the origin merge by taking the larger radius; kept nonnegative so that
callers never split on which is larger.
@isnad1 id=le.1h2v.s7.35a44876f2f1 from=translated src=- shape=4997f19d vocab=6ab4eff8
-/
theorem closedSquare_mono {r s : ℝ} (h : r ≤ s) : closedSquare 0 r ⊆ closedSquare 0 s :=
  fun _ hx => le_trans hx h

/-- A finite family of bounded sets is caught inside one square.
@isnad1 id=ex.2h3v.s7.82212472ebb3 from=translated src=- shape=f347b57d vocab=25c9f392
-/
theorem exists_closedSquare_of_finite {ι : Type*} {S : ι → Set Plane} {t : Set ι}
    (ht : t.Finite) (hS : ∀ i ∈ t, Bornology.IsBounded (S i)) :
    ∃ r : ℝ, 0 ≤ r ∧ (⋃ i ∈ t, S i) ⊆ closedSquare 0 r :=
  exists_closedSquare_of_isBounded ((Bornology.isBounded_biUnion ht).2 hS)

/-- The complement of a finite union of compact sets is open. The exterior of a plane graph —
finitely many vertices and finitely many compact edge arcs — is open for this reason.
@isnad1 id=isopen.2h3v.s7.493d15cd3ae0 from=translated src=- shape=320f4ee0 vocab=c7177a5d
-/
theorem isOpen_compl_of_finite_isCompact {ι : Type*} {S : ι → Set Plane} {t : Set ι}
    (ht : t.Finite) (hS : ∀ i ∈ t, IsCompact (S i)) : IsOpen (⋃ i ∈ t, S i)ᶜ :=
  (ht.isClosed_biUnion fun i hi => (hS i hi).isClosed).isOpen_compl

end Plane

end Schoenflies
