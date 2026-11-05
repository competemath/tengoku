/-
Copyright (c) 2025 Christian Merten. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Merten
-/
module

public import Tengoku.Seed.RingTheory.TotallySplit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

open TensorProduct

universe u

namespace RingHom

lemma Smooth.ofLocalizationSpan : OfLocalizationSpan Smooth := by
  apply ofLocalizationSpanTarget.ofLocalizationSpan
  exact (stableUnderComposition.stableUnderCompositionWithLocalizationAway
    holdsForLocalizationAway).left

end RingHom

lemma Algebra.FormallySmooth.of_bijective_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (h : Function.Bijective (algebraMap R S)) :
    Algebra.FormallySmooth R S :=
  Algebra.FormallySmooth.of_equiv
    { __ := RingEquiv.ofBijective (algebraMap R S) h, commutes' := by simp }

namespace Algebra

end Algebra
