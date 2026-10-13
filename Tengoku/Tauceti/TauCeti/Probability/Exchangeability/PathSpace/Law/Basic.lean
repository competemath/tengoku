/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.Basic
public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.PermutationExtension
public import Tengoku

/-!
# Exchangeable laws on path space

This file adds the path-law formulation of full exchangeability for measures on `ℕ → α`.
The process-level definitions in `TauCeti.Probability.Exchangeability.Basic` remain the main
user-facing API for stochastic processes; `ExchangeableLaw` names the equivalent path-space
viewpoint needed by π-system, invariant-σ-algebra, and shift arguments.

Everything here is pure path space: it depends only on the coordinate-reindexing and prefix
machinery of `Basic` and the finite permutation extension of `PermutationExtension`. The
process-level ↔ path-law bridges live in
`TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge`, which imports both this file and
`FullyExchangeable`. No measure-theoretic infrastructure is vendored.

The closure theorem `exchangeableLaw_map_prod_coding` records that applying one jointly measurable
coding function coordinatewise to independent parameter and exchangeable-noise laws preserves
exchangeability.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- A measure on one-sided path space is exchangeable if it is invariant under every
permutation of the time coordinate. -/
def ExchangeableLaw (ρ : Measure (ℕ → α)) : Prop :=
  ∀ π : Equiv.Perm ℕ, ρ.map (permReindex (α := α) π) = ρ

/-- Constructor for `ExchangeableLaw` from the defining map invariance. -/
theorem ExchangeableLaw.intro {ρ : Measure (ℕ → α)}
    (h : ∀ π : Equiv.Perm ℕ, ρ.map (permReindex (α := α) π) = ρ) :
    ExchangeableLaw ρ :=
  h

/-- Simp normal form for `ExchangeableLaw`. -/
@[simp]
theorem exchangeableLaw_iff {ρ : Measure (ℕ → α)} :
    ExchangeableLaw ρ ↔ ∀ π : Equiv.Perm ℕ, ρ.map (permReindex (α := α) π) = ρ :=
  Iff.rfl

/-- The defining invariance of an exchangeable path law. -/
theorem ExchangeableLaw.map_permReindex {ρ : Measure (ℕ → α)} (hρ : ExchangeableLaw ρ)
    (π : Equiv.Perm ℕ) :
    ρ.map (permReindex (α := α) π) = ρ :=
  hρ π

/-- **An i.i.d. product law is exchangeable.** Reindexing a constant product law by a
permutation leaves every factor unchanged. -/
theorem exchangeableLaw_infinitePi_const (P : ProbabilityMeasure α) :
    ExchangeableLaw (Measure.infinitePi fun _ : ℕ => (P : Measure α)) := by
  intro π
  have hperm : permReindex (α := α) π = fun x i => x (π i) := by
    funext x i
    rw [permReindex_apply]
  rw [hperm]
  simpa only using
    Measure.map_infinitePi_infinitePi_of_inj
      (P := fun _ : ℕ => (P : Measure α)) π.injective

end Probability

end TauCeti
