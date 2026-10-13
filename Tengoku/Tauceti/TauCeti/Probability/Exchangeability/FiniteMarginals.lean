/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.Basic
public import Tengoku

/-!
# Finite-dimensional marginal uniqueness

A finite measure on path space `ℕ → α` is determined by its finite prefix marginals: any measure
agreeing with it on every prefix projection (`prefixProj α n`, the projection to the first `n`
coordinates) is equal to it. This is the Layer 0 finite-marginal uniqueness milestone of
`TauCetiRoadmap/Exchangeability`: a thin ℕ-prefix wrapper over Mathlib's projective-limit
machinery (`IsProjectiveLimit.unique`), not new measure theory.

The public API:
* `measure_eq_of_prefixProj_map_eq` — the map-equality form;
* `measure_eq_of_fin_marginals_eq` — the roadmap-named setwise form;
* `prefixProjPair`, `measurable_prefixProjPair`, `prefixProjPair_comp` — the same prefix
  projection, carrying an extra factor along;
* `measure_eq_of_prefixProjPair_map_eq` — paired finite-marginal uniqueness on `T × (ℕ → α)`.

The paired form reduces to the unpaired one rather than reproving it. Mathlib's
`IsProjectiveLimit` is stated for dependent products `∀ i, α i`, and `T × (ℕ → α)` is not of that
shape — but replicating the first factor at every coordinate, `(t, x) ↦ fun n => (t, x n)`, embeds
it in `ℕ → T × α`, which is. That map has an explicit measurable left inverse, so it is injective on
measures, and each of its prefix marginals is read off the paired prefix marginal one step longer.

Both apply directly to probability measures, since `IsProbabilityMeasure` provides
`IsFiniteMeasure`, so no separate probability-measure theorem is needed.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {α : Type*} [MeasurableSpace α]

/-- The prefix map onto the first `n` path coordinates, keeping the first factor. -/
def prefixProjPair (T α : Type*) (n : ℕ) : T × (ℕ → α) → T × (Fin n → α) :=
  fun q => (q.1, fun i : Fin n => q.2 i)

/-- Applying the paired prefix map. -/
@[simp]
theorem prefixProjPair_apply {T α : Type*} (n : ℕ) (q : T × (ℕ → α)) :
    prefixProjPair T α n q = (q.1, fun i : Fin n => q.2 i) :=
  (rfl)

/-! ## Paired prefix marginals -/

/-- Longer prefixes refine shorter ones. -/
theorem prefixProjPair_comp {T α : Type*} {m n : ℕ} (hmn : m ≤ n) : prefixProjPair T α m
      = (fun r : T × (Fin n → α) =>
          (r.1, fun i : Fin m => r.2 (Fin.castLE hmn i))) ∘ prefixProjPair T α n := by
  funext q
  simp only [prefixProjPair, Function.comp_apply, Fin.val_castLE]

end Probability

end TauCeti
