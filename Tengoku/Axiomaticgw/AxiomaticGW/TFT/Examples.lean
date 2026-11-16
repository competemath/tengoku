/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Frobenius.Examples
public import Tengoku.Axiomaticgw.AxiomaticGW.TFT.Frobenius

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Examples of Frobenius-algebra correlators

This file computes the correlators associated to the base ring and the
rank-two product Frobenius algebra.
-/

@[expose] public section

namespace AxiomaticGW

namespace CommFrobeniusAlgebra

/-- The correlators of the base-ring Frobenius algebra are ordinary finite
products, independently of the genus.
@isnad1 id=eq.0h4v.s7.37b6da18d186 from=translated src=- shape=910a53ed vocab=c1d2ffb2
-/
theorem baseRing_correlator_apply (R : Type*) [CommRing R] (g : ℕ)
    {S : Type*} [Fintype S] (a : S → R) :
    (baseRing R).correlator g S a = ∏ s, a s := by
  simp only [correlator_apply, baseRing_handleElement, one_pow, mul_one,
    baseRing_counit_apply]

/-- The product-algebra correlator is the sum of the products of the two
coordinate families.
@isnad1 id=eq.0h4v.s8.4b009b13af51 from=translated src=- shape=50759c57 vocab=4488a3a1
-/
theorem productAlgebra_correlator_apply (R : Type*) [CommRing R] (g : ℕ)
    {S : Type*} [Fintype S] (a : S → R × R) :
    (productAlgebra R).correlator g S a =
      (∏ s, (a s).1) + ∏ s, (a s).2 := by
  rw [correlator_apply, productAlgebra_handleElement]
  simp only [one_pow, mul_one]
  change (∏ s, a s).1 + (∏ s, a s).2 = _
  have hfst : (∏ s, a s).1 = ∏ s, (a s).1 := by
    simpa only using (Prod.fst_prod (s := Finset.univ) (f := a))
  have hsnd : (∏ s, a s).2 = ∏ s, (a s).2 := by
    simpa only using (Prod.snd_prod (s := Finset.univ) (f := a))
  rw [hfst, hsnd]

end CommFrobeniusAlgebra

end AxiomaticGW
