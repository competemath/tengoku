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

/--
@isnad1 id=oflocali.0h0v.s4.fde6ab27412f from=translated src=- shape=96d721b5 vocab=148b8dd3
-/
lemma Smooth.ofLocalizationSpan : OfLocalizationSpan Smooth := by
  apply ofLocalizationSpanTarget.ofLocalizationSpan
  exact (stableUnderComposition.stableUnderCompositionWithLocalizationAway
    holdsForLocalizationAway).left

end RingHom

/--
@isnad1 id=formally.1h2v.s6.1a68a7e7b964 from=translated src=- shape=d2bc4cd6 vocab=1194ff77
-/
lemma Algebra.FormallySmooth.of_bijective_algebraMap {R S : Type u} [CommRing R] [CommRing S]
    [Algebra R S] (h : Function.Bijective (algebraMap R S)) :
    Algebra.FormallySmooth R S :=
  Algebra.FormallySmooth.of_equiv
    { __ := RingEquiv.ofBijective (algebraMap R S) h, commutes' := by simp }

namespace Algebra

end Algebra
