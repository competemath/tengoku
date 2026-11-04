/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.RingTheory.UniqueFactorizationDomain.Multiplicity
import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic
import Tengoku.Seed.RingTheory.DiscreteValuationRing.Basic
import Tengoku.Seed.RingTheory.OrderOfVanishing.Noetherian
import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.StalkGenerization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Order of vanishing as prime content in the stalk at a closed point

The second step of P2.5c's piece c4.  `Chow/FactorialFractionUnit.lean` reduces "the Laurent
cofactor is a genuine unit of `𝒪_{X,pt}`" to "numerator and denominator are divisible by exactly
the same prime powers".  This file converts that divisibility condition into the order of vanishing
that the relation cycle actually records.

`IsLocalization.pow_dvd_iff_map_pow_dvd_map` is the saturation step: for a prime element `π` of a
domain `A`, `π ^ n ∣ a` can be tested after localizing at `(π)`.  The nontrivial direction clears
denominators — `s · a = π ^ n · b` with `s ∉ (π)` — and uses primality of `π` to cancel `s`.

`AlgebraicGeometry.Scheme.pow_dvd_iff_natCast_le_ord` is the geometric form.  For `w ⤳ pt` with
`𝒪_{X,w}` a discrete valuation ring and `π` generating the prime `stalkPrimeOfSpecializes h`
attached to `w` by P2.5a (principal by P2.5b on a regular surface):

```lean
π ^ n ∣ a ↔ (n : ℕ∞) ≤ Ring.ord (X.presheaf.stalk w) (algebraMap _ _ a)
```

P2.5a's `isLocalization_stalkSpecializes` is what makes `𝒪_{X,w}` the localization of `𝒪_{X,pt}`
at `(π)`, so the image of `π` is a uniformizer and `Ring.ord_eq_addVal` turns the order into the
discrete valuation, where `IsDiscreteValuationRing.addVal_le_iff_dvd` is exactly divisibility.
`Chow/PrincipalOrderLength.lean`'s `Scheme.ord_algebraMap_eq_length_toNat` connects `Ring.ord` to
`Scheme.ord` on the other side.

Together with `FactorialFractionUnit` this gives the criterion c4 needs: a rational function whose
order vanishes at every codimension-one generization of `pt` is a unit of `𝒪_{X,pt}`.  What is left
of c4 is the geometric assembly — a `zpow` form of `restrictFunctionToPointClosure_mul`, the
relation components that miss `pt`, and matching `X.ord f w` against `compactCycleFinsupp g.cycle`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry

universe u

namespace IsLocalization

/-- Divisibility by a power of a prime element is detected after localizing at the prime it
generates.
@isnad1 id=iff.2h6v.s8.07687fb941a3 from=translated src=- shape=983be5de vocab=d4c18ef4
-/
theorem pow_dvd_iff_map_pow_dvd_map {A : Type u} [CommRing A] [IsDomain A]
    {P : Ideal A} [P.IsPrime] {π : A} (hπ : Prime π) (hgen : P = Ideal.span {π})
    (S : Type u) [CommRing S] [Algebra A S] [IsLocalization.AtPrime S P]
    (a : A) (n : ℕ) :
    π ^ n ∣ a ↔ (algebraMap A S π) ^ n ∣ algebraMap A S a := by
  subst hgen
  refine ⟨fun h => by simpa using map_dvd (algebraMap A S) h, ?_⟩
  rintro ⟨t, ht⟩
  obtain ⟨⟨b, s⟩, hbs⟩ := IsLocalization.surj (M := (Ideal.span {π} : Ideal A).primeCompl) t
  have hmap : algebraMap A S (s * a) = algebraMap A S (π ^ n * b) := by
    rw [map_mul, map_mul, mul_comm ((algebraMap A S) s), ht, mul_assoc, hbs, map_pow]
  obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists (Ideal.span {π} : Ideal A).primeCompl S).mp hmap
  have hmem : ∀ d : (Ideal.span {π} : Ideal A).primeCompl, ¬ π ∣ (d : A) :=
    fun d hd => d.2 (Ideal.mem_span_singleton.mpr hd)
  have hdvd : π ^ n ∣ ((c : A) * s) * a := by
    refine ⟨(c : A) * b, ?_⟩
    calc ((c : A) * s) * a = (c : A) * (s * a) := by ring
      _ = (c : A) * (π ^ n * b) := by rw [hc]
      _ = π ^ n * ((c : A) * b) := by ring
  have hns : ¬ π ∣ ((c : A) * s) := by
    intro hd
    rcases hπ.dvd_mul.mp hd with hd' | hd'
    · exact hmem c hd'
    · exact hmem s hd'
  exact hπ.pow_dvd_of_dvd_mul_left n hns hdvd

end IsLocalization

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} [IsIntegral X]

/-- **The `Scheme.ord` bridge.**  For a codimension-one generization `w` of `pt` whose stalk is a
discrete valuation ring, divisibility in `𝒪_{X,pt}` by a power of a generator of the prime attached
to `w` is exactly a lower bound on the order of vanishing at `w`.
@isnad1 id=iff.3h6v.s10.b86580ee8a2c from=translated src=- shape=4a7c00e2 vocab=03ede8e2
-/
theorem pow_dvd_iff_natCast_le_ord {w pt : X} (h : w ⤳ pt)
    [IsDiscreteValuationRing (X.presheaf.stalk w)]
    {π : X.presheaf.stalk pt} (hπ : Prime π)
    (hgen : stalkPrimeOfSpecializes h = Ideal.span {π}) (a : X.presheaf.stalk pt) (n : ℕ) :
    letI := stalkSpecializesAlgebra h
    π ^ n ∣ a ↔ (n : ℕ∞) ≤ Ring.ord (X.presheaf.stalk w)
      (algebraMap (X.presheaf.stalk pt) (X.presheaf.stalk w) a) := by
  letI := stalkSpecializesAlgebra h
  haveI := isLocalization_stalkSpecializes h
  -- the image of `π` is a uniformizer of the discrete valuation ring `𝒪_{X,w}`
  have hunif : Irreducible (algebraMap (X.presheaf.stalk pt) (X.presheaf.stalk w) π) := by
    rw [IsDiscreteValuationRing.irreducible_iff_uniformizer]
    rw [← IsLocalization.AtPrime.map_eq_maximalIdeal (stalkPrimeOfSpecializes h)
      (X.presheaf.stalk w), hgen, Ideal.map_span, Set.image_singleton]
  rw [IsLocalization.pow_dvd_iff_map_pow_dvd_map hπ hgen (X.presheaf.stalk w) a n,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, hunif.addVal_pow, Ring.ord_eq_addVal]

end AlgebraicGeometry.Scheme
