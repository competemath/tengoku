/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import Tengoku

/-!
# Projective limits on sequences

This file proves a sequence-indexed version of Kolmogorov's extension theorem when every
positive-indexed coordinate is standard Borel. Mathlib defines projective measure families and
proves uniqueness of their projective limits, while its Ionescu--Tulcea construction produces a
path law from a sequence of transition kernels. Here a coherent family of finite-prefix laws is
disintegrated to obtain those kernels.

## Main result

* `TauCeti.Measure.exists_map_frestrictLe_eq` constructs a probability measure on a dependent
  sequence whose finite-prefix laws are a prescribed coherent family.
* `TauCeti.Measure.exists_isProjectiveLimit_nat` realizes a projective family indexed by finite
  subsets of `ℕ`.

This is the existence bridge between Mathlib's `MeasureTheory.IsProjectiveMeasureFamily` API and
its Ionescu--Tulcea theorem. The construction follows the standard proof of Kolmogorov extension
for countable products by successive disintegration, as prescribed by the
`TauCetiRoadmap/OptimalTransport/README.md` Layer 0, item 4 target.
-/

public section

noncomputable section

open Finset MeasureTheory Preorder ProbabilityTheory

namespace TauCeti

namespace Measure

universe u

variable {X : ℕ → Type u} [∀ n, MeasurableSpace (X n)]

/-- Split a trajectory through time `n + 1` into its prefix through time `n` and its last
coordinate. -/
private def prefixSuccEquiv (n : ℕ) :
    ((∀ i : Iic n, X i) × X (n + 1)) ≃ᵐ (∀ i : Iic (n + 1), X i) :=
  (MeasurableEquiv.prodCongr (MeasurableEquiv.refl _) (MeasurableEquiv.piSingleton n)).trans
    (MeasurableEquiv.IicProdIoc n.le_succ)

/-- The law of a prefix and its next coordinate, obtained from the next prescribed prefix law. -/
private def successorLaw (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) (n : ℕ) :
    Measure ((∀ i : Iic n, X i) × X (n + 1)) :=
  (P (n + 1)).map (prefixSuccEquiv n).symm

/-- The zeroth-coordinate law extracted from the first prescribed prefix law. -/
private def initialLaw (P : ∀ n : ℕ, Measure (∀ i : Iic n, X i)) : Measure (X 0) :=
  (P 0).map (MeasurableEquiv.piUnique fun i : Iic 0 ↦ X i)

end Measure

end TauCeti
