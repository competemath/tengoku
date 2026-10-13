/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.FiniteMarginals
public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.PathSpace.Law.Basic

/-!
# Contractable laws on path space

This file adds the path-law formulation of contractability, also called spreadability:
a measure on `ℕ → α` is invariant under every strictly increasing reindexing of time.
The process-level predicate `Contractable μ X` remains the main stochastic-process API;
`ContractableLaw` names the equivalent path-space viewpoint needed by the de Finetti
factorization and path-space dynamics.

This is the contractability analogue of `ExchangeableLaw`. It realizes the Exchangeability
roadmap's Layer 0 request for the characterization of contractability by strictly increasing
maps `ℕ → ℕ`, with finite-dimensional marginal consequences. The process-level ↔ path-law
bridges live in `TauCeti.Probability.Exchangeability.PathSpace.Law.Bridge`, which imports this
file and `Contractability`; no Mathlib infrastructure is vendored.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A measure on one-sided path space is contractable, or spreadable, if it is invariant under
every strictly increasing reindexing of the time coordinate. -/
def ContractableLaw (ρ : Measure (ℕ → α)) : Prop :=
  ∀ φ : ℕ → ℕ, StrictMono φ → ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ

/-- Constructor for `ContractableLaw` from the defining map invariance. -/
theorem ContractableLaw.intro {ρ : Measure (ℕ → α)}
    (h : ∀ φ : ℕ → ℕ, StrictMono φ →
      ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ) :
    ContractableLaw ρ :=
  h

/-- Simp normal form for `ContractableLaw`. -/
@[simp]
theorem contractableLaw_iff {ρ : Measure (ℕ → α)} :
    ContractableLaw ρ ↔
      ∀ φ : ℕ → ℕ, StrictMono φ →
        ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ :=
  Iff.rfl

/-- The defining invariance of a contractable path law. -/
theorem ContractableLaw.map_reindex {ρ : Measure (ℕ → α)}
    (hρ : ContractableLaw ρ)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    ρ.map (fun x : ℕ → α => fun k => x (φ k)) = ρ :=
  hρ φ hφ

end Probability

end TauCeti
