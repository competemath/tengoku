/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Defs
import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Extractor.Moments.Internal

/-!
# Low-order sign-sum moments from parity bias

The bounds hold for finite weighted averages. Nonnegative weights of mass one
specialize them to finite probability distributions. `SourceReduction.Tests`
derives the parity-bias hypothesis for the actual source reduction.
-/

public section

namespace Algebraic.Cutwidth.Extractor

/-- Singleton parity bias bounds the first moment of the sum of `m` signs.
@isnad1 id=le.1h6v.s5.3faa53fb9ce1 from=translated src=- shape=8a9ce779 vocab=0fb498ae
-/
theorem signSum_first_moment {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (h : ParityBiasBound s w σ δ) :
    |weightedMean s w (signSum σ)| ≤ m * δ :=
  Internal.signSum_first_moment h

/-- Pair parity bias bounds the deviation of the second moment from `m`.
@isnad1 id=le.4h6v.s7.59ca247a0bc8 from=translated src=- shape=7a05d0d0 vocab=c267b687
-/
theorem signSum_second_moment {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) :
    |weightedMean s w (fun a => signSum σ a ^ 2) - m| ≤ (m : ℝ) ^ 2 * δ :=
  Internal.signSum_second_moment hδ hmass hσ h

/-- Every odd triple reduces to a nonempty parity of at most three signs.
@isnad1 id=le.2h6v.s7.d4d039bfa8ec from=translated src=- shape=5eb9e873 vocab=c6bcdc5b
-/
theorem signSum_third_moment {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ}
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) :
    |weightedMean s w (fun a => signSum σ a ^ 3)| ≤ (m : ℝ) ^ 3 * δ :=
  Internal.signSum_third_moment hσ h

/-- The three possible pairings account for at most `3m²` unbiased terms;
each remaining fourth-degree term is controlled by its parity bias.
@isnad1 id=le.4h6v.s7.e32ae7b794d4 from=translated src=- shape=64e975b0 vocab=f30b9c93
-/
theorem signSum_fourth_moment {α : Type*} {m : Nat} {s : Finset α} {w : α → ℝ}
    {σ : α → Fin m → ℝ} {δ : ℝ} (hδ : 0 ≤ δ) (hmass : ∑ a ∈ s, w a = 1)
    (hσ : ∀ a ∈ s, ∀ i, σ a i = 1 ∨ σ a i = -1)
    (h : ParityBiasBound s w σ δ) :
    weightedMean s w (fun a => signSum σ a ^ 4) ≤
      3 * (m : ℝ) ^ 2 + (m : ℝ) ^ 4 * δ :=
  Internal.signSum_fourth_moment hδ hmass hσ h

end Algebraic.Cutwidth.Extractor
