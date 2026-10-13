/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Strong.Weighted.Conditional.Internal

/-!
# Conditioning finite sources without discarding zero-mass rows

Every row is normalized, with a uniform completion at null events. Exact
factorization recovers the original joint law. Total variation from a fresh
uniform output equals the average conditional distance, retaining the actual
first marginal. These identities support finite leakage and independence
merging without a pointwise conditional entropy assumption.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Multiplying a conditional row by its marginal recovers each original point mass.
@isnad1 id=eq.1h5v.s5.5baefb5399cd from=translated src=- shape=dbe6eddc vocab=23cb4ea4
-/
theorem conditionalWeight_factor {α β : Type*} [Fintype β]
    (p : α × β → ℝ) (nonnegative : ∀ ab, 0 ≤ p ab) (a : α) (b : β) :
    firstWeight p a * conditionalWeight p a b = p (a, b) :=
  Internal.conditionalWeight_factor p nonnegative a b

/-- Every conditional row of a probability law is normalized, including null rows.
@isnad1 id=isprobab.1h4v.s5.54555717becb from=translated src=- shape=7ad098ee vocab=57827805
-/
theorem IsProbabilityWeight.conditionalWeight {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β]
    {p : α × β → ℝ} (probability : IsProbabilityWeight p) (a : α) :
    IsProbabilityWeight (conditionalWeight p a) :=
  Internal.probabilityWeight_conditional probability a

/-- Appending an independent uniform coordinate preserves normalization.
@isnad1 id=isprobab.1h3v.s5.1f5a903a6131 from=translated src=- shape=52a4669f vocab=599be090
-/
theorem IsProbabilityWeight.uniformExtension {α : Type*} [Fintype α]
    {w : α → ℝ} (probability : IsProbabilityWeight w) (β : Type*) [Fintype β] [Nonempty β] :
    IsProbabilityWeight (uniformExtensionWeight β w) :=
  Internal.probabilityWeight_uniformExtension probability β

/-- Uniform extension preserves its supplied first-coordinate weighting exactly.
@isnad1 id=eq.0h3v.s4.f0e8feadec6a from=translated src=- shape=daf40484 vocab=af40ac2c
-/
theorem firstWeight_uniformExtension {α β : Type*} [Fintype β] [Nonempty β]
    (w : α → ℝ) : firstWeight (uniformExtensionWeight β w) = w :=
  Internal.firstWeight_uniformExtension w

/-- Replacing the second coordinate by fresh uniform randomness preserves probability.
@isnad1 id=isprobab.1h3v.s5.dcd8d767507b from=translated src=- shape=6631d688 vocab=b6ab11f6
-/
theorem IsProbabilityWeight.uniformSecond {α β : Type*}
    [Fintype α] [Fintype β] [Nonempty β]
    {p : α × β → ℝ} (probability : IsProbabilityWeight p) :
    IsProbabilityWeight (uniformSecondWeight p) :=
  Internal.probabilityWeight_uniformSecond probability

/-- Distance from a conditionally uniform output averages the exact row distances.
@isnad1 id=eq.1h3v.s6.acd59e4861cf from=translated src=- shape=ea0a8767 vocab=acfe4cc9
-/
theorem weightDist_uniformSecond_eq {α β : Type*}
    [Fintype α] [Fintype β]
    {p : α × β → ℝ} (probability : IsProbabilityWeight p) :
    weightDist p (uniformSecondWeight p) =
      ∑ a, firstWeight p a * weightDist (conditionalWeight p a) (uniformWeight β) :=
  Internal.weightDist_uniformSecond_eq probability

/-- Processing the second coordinate separately on each row preserves the first marginal.
@isnad1 id=eq.0h5v.s6.29177cbd66b5 from=translated src=- shape=9012fae7 vocab=41ca1a01
-/
theorem firstWeight_map_fiber {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → β → γ) :
    firstWeight (mapWeight (fun ab => (ab.1, f ab.1 ab.2)) p) = firstWeight p :=
  Internal.firstWeight_map_fiber p f

/-- Retaining a nonnegative mixture tag averages distance from conditionally uniform output.
@isnad1 id=eq.1h5v.s7.965be6c62ede from=translated src=- shape=85af505c vocab=b72774d5
-/
theorem weightDist_uniformSecond_tagged {ι α β : Type*}
    [Fintype ι] [Fintype α] [Fintype β]
    (w : ι → ℝ) (p : ι → α × β → ℝ) (nonnegative : ∀ i, 0 ≤ w i) :
    weightDist (fun iab : (ι × α) × β => w iab.1.1 * p iab.1.1 (iab.1.2, iab.2))
      (uniformSecondWeight (fun iab => w iab.1.1 * p iab.1.1 (iab.1.2, iab.2))) =
        ∑ i, w i * weightDist (p i) (uniformSecondWeight (p i)) :=
  Internal.weightDist_uniformSecond_tagged w p nonnegative

/-- A deterministic observation of the first coordinate pushes forward its marginal.
@isnad1 id=eq.0h5v.s6.9edb40fb2fcb from=translated src=- shape=b8a970ba vocab=41ca1a01
-/
theorem firstWeight_map_first {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → γ) :
    firstWeight (mapWeight (fun ab => (f ab.1, ab.2)) p) =
      mapWeight f (firstWeight p) :=
  Internal.firstWeight_map_first p f

/-- Observing the first coordinate commutes with adding independent uniform randomness.
@isnad1 id=eq.0h5v.s6.c55791e67b3b from=translated src=- shape=2e6e8630 vocab=68f406c7
-/
theorem mapWeight_uniformExtension {α β γ : Type*}
    [Fintype α] [Fintype β] (w : α → ℝ) (f : α → γ) :
    mapWeight (fun ab : α × β => (f ab.1, ab.2)) (uniformExtensionWeight β w) =
      uniformExtensionWeight β (mapWeight f w) :=
  Internal.mapWeight_uniformExtension w f

/-- Uniformizing an output commutes with every deterministic observation of its side information.
@isnad1 id=eq.0h5v.s6.2b360f38190c from=translated src=- shape=ccdf048d vocab=dc2c7400
-/
theorem uniformSecondWeight_map_first {α β γ : Type*}
    [Fintype α] [Fintype β] [Fintype γ]
    (p : α × β → ℝ) (f : α → γ) :
    mapWeight (fun ab => (f ab.1, ab.2)) (uniformSecondWeight p) =
      uniformSecondWeight (mapWeight (fun ab => (f ab.1, ab.2)) p) :=
  Internal.uniformSecondWeight_map_first p f

end Algebraic.Cutwidth.Extractor
