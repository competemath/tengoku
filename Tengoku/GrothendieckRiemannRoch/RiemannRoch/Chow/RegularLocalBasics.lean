/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.CohenMacaulay
import Tengoku.Seed.RingTheory.RegularLocalRing.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic interface for regular local rings

This file packages the minimal generators of the maximal ideal as a regular system of
parameters and aligns Mathlib's `WithBot ℕ∞` dimension with the local dimension used by the
depth/Cohen--Macaulay layer.
-/

noncomputable section

universe u

open IsLocalRing

variable (R : Type u) [CommRing R] [IsRegularLocalRing R]

namespace IsRegularLocalRing

/-- The embedding dimension, i.e. the minimal number of generators of the maximal ideal.-/
def embeddingDimension : ℕ :=
  (maximalIdeal R).spanFinrank

/-- In a regular local ring the embedding dimension, coerced to the dimension value type,
is the Krull dimension.-/
theorem coe_embeddingDimension_eq_ringKrullDim :
    ((embeddingDimension R : ℕ∞) : WithBot ℕ∞) = ringKrullDim R :=
  IsRegularLocalRing.spanFinrank_maximalIdeal

/-- The bottom-free local Krull dimension is the finite embedding dimension.-/
theorem localKrullDim_eq_embeddingDimension :
    ModuleCat.localKrullDim R = (embeddingDimension R : ℕ∞) := by
  apply WithBot.coe_injective
  rw [ModuleCat.coe_localKrullDim]
  exact coe_embeddingDimension_eq_ringKrullDim R |>.symm

/-- A regular system of parameters, at the basic interface level needed downstream: a
minimal finite generating set of the maximal ideal.  Regular-sequence properties are supplied
later by the Cohen--Macaulay plate.-/
structure SystemOfParameters where
  elements : Finset R
  card_eq : elements.card = embeddingDimension R
  span_eq : Submodule.span R (elements : Set R) = maximalIdeal R

namespace SystemOfParameters

/-- Every member of a regular system of parameters lies in the maximal ideal.-/
theorem mem_maximalIdeal (s : SystemOfParameters R) {r : R} (hr : r ∈ s.elements) :
    r ∈ maximalIdeal R := by
  rw [← s.span_eq]
  exact Submodule.subset_span hr

/-- The parameters generate the maximal ideal as an ideal.-/
theorem ideal_span_eq (s : SystemOfParameters R) :
    Ideal.span (s.elements : Set R) = maximalIdeal R := by
  exact s.span_eq

end SystemOfParameters

/-- A regular local ring admits a regular system of parameters of cardinality equal to its
embedding (hence Krull) dimension.-/
theorem exists_systemOfParameters : Nonempty (SystemOfParameters R) := by
  let m : Submodule R R := maximalIdeal R
  have hfg : m.FG := IsNoetherian.noetherian m
  obtain ⟨s, hcard, hspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank hfg
  exact ⟨⟨s, by simpa [embeddingDimension, m] using hcard, by simpa [m] using hspan⟩⟩

end IsRegularLocalRing
