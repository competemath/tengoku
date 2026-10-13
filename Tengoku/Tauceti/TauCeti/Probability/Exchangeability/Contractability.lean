/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.Basic
public import Tengoku
import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.PermutationExtension
import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.ExchangeableAtMonotone
import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.FiniteMarginals

/-!
# Contractability API

This file records basic lemmas for `Contractable` processes. The definitions live in
`TauCeti.Probability.Exchangeability.Basic`.

The main result is `Exchangeable.contractable`: every exchangeable sequence with a.e. measurable
coordinates is contractable. The file also provides
`Exchangeable.blockLaw_eq_prefixLaw_of_injective` (the injective-selection analogue) and
`Contractable.measurePreserving_reindex` / `Contractable.measurePreserving_shift` (a contractable
path law is invariant under strictly monotone time-reindexing, in particular the shift), plus the
converse characterization `contractable_iff_forall_map_reindex_pathLaw`.

These declarations are adapted from the `cameronfreer/exchangeability` Layer 0 sources pinned
at `e0532e59ceff23edab44dda9ab0655debbc9cc22`, with Tau Ceti API names and hypotheses; the
combinatorial core now lives in `PermutationExtension.lean`. `Contractable.pairLaw_eq` is adapted
from `DeFinetti/ViaMartingale/FutureRectangles.lean` (`contractable_dist_eq`) in the same repo,
reproved via the reindexing route below rather than the reference's rectangle π-system.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory

open scoped ENNReal

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]

/-- A contractable process has the same finite-dimensional block law as the corresponding
prefix law along any strictly increasing finite index map. -/
theorem Contractable.map {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {m : ℕ} {k : Fin m → ℕ} (hk : StrictMono k) :
    blockLaw μ X k = prefixLaw μ X m :=
  h m k hk

/-- The one-coordinate specialization of contractability. -/
theorem Contractable.map_single {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    (k : Fin 1 → ℕ) :
    blockLaw μ X k = prefixLaw μ X 1 :=
  h.map (Subsingleton.strictMono k)

/-- The two-coordinate specialization of contractability. -/
theorem Contractable.map_pair {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {i j : ℕ} (hij : i < j) :
    blockLaw μ X ![i, j] = prefixLaw μ X 2 :=
  h.map (strictMono_vecEmpty.vecCons hij)

/-- Contractability is preserved by passing to a strictly increasing subsequence. -/
theorem Contractable.comp {μ : Measure Ω} {X : ℕ → Ω → α} (h : Contractable μ X)
    {φ : ℕ → ℕ} (hφ : StrictMono φ) :
    Contractable μ (fun n ω ↦ X (φ n) ω) := by
  intro m k hk
  calc
    blockLaw μ (fun n ω ↦ X (φ n) ω) k =
        blockLaw μ X (φ ∘ k) := by
      simp only [blockLaw_def, Function.comp_apply]
    _ = prefixLaw μ X m := h.map (hφ.comp hk)
    _ = blockLaw μ (fun n ω ↦ X (φ n) ω) (fun i : Fin m ↦ i.val) := by
      have := (h.map (hφ.comp (Fin.val_strictMono : StrictMono (fun i : Fin m ↦ i.val)))).symm
      simpa only [blockLaw_def, Function.comp_apply] using this
    _ = prefixLaw μ (fun n ω ↦ X (φ n) ω) m := by
      simp only [prefixLaw_def]

end Probability

end TauCeti
