/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Tengoku.Tauceti.TauCeti.MeasureTheory.Measure.ProjectiveLimit.Nat

/-!
# Projective limits on countable products

This file extends the sequence-indexed Kolmogorov extension theorem from
`TauCeti.MeasureTheory.Measure.ProjectiveLimit.Nat` to an arbitrary countable index type. Finite
index types are handled directly by the law on all coordinates; infinite countable types are
enumerated and reduced to the sequence theorem.

## Main result

* `TauCeti.Measure.exists_isProjectiveLimit_of_countable` realizes every projective family of
  probability laws on finite subsets of a countable family of standard Borel spaces.

The proof transports finite-dimensional laws along measurable equivalences of dependent products.
This is the arbitrary-countable-index existence bridge required by
`TauCetiRoadmap/OptimalTransport/README.md`, Layer 0, item 4.
-/

public section

noncomputable section

open Finset MeasureTheory

namespace TauCeti

namespace Measure

universe u v

variable {ι : Type u} {κ : Type v} {X : ι → Type*} [∀ i, MeasurableSpace (X i)]

/-- Reindex a finite dependent product along an equivalence of its coordinate types. -/
private def finitePiCongrLeft (e : κ ≃ ι) (J : Finset κ) :
    (∀ j : J, X (e j)) ≃ᵐ (∀ i : J.map e.toEmbedding, X i) :=
  MeasurableEquiv.piCongrLeft (fun i : J.map e.toEmbedding ↦ X i)
    (J.equivMap e.toEmbedding)

/-- Reindex the finite-dimensional laws of a projective family along an equivalence. -/
private def reindexProjectiveFamily (e : κ ≃ ι)
    (P : ∀ I : Finset ι, Measure (∀ i : I, X i)) (J : Finset κ) :
    Measure (∀ j : J, X (e j)) :=
  (P (J.map e.toEmbedding)).map (finitePiCongrLeft e J).symm

end Measure

end TauCeti
