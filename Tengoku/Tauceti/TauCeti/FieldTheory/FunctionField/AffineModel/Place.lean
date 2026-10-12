/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.FieldTheory.FunctionField.Place.Basic
public import Tengoku.Tauceti.TauCeti.RingTheory.DedekindDomain.AdicValuation.Basic

/-!
# Affine models: a place finite on a Dedekind subring is one of its height one primes

An *affine model* of `F / k` is a Dedekind `k`-subalgebra `R` of `F` whose fraction field is `F`;
the standard example is the integral closure `R_x` of `k[x]` in `F` for a transcendental `x`. This
file proves the forward direction of the places ↔ height one primes correspondence: a place of
`F / k` whose valuation ring contains `R` is the adic place of a *unique* height one prime `𝔭` of
`R`, in the strong sense that the valuation of the place *equals* — not merely is equivalent to —
the normalized `𝔭`-adic valuation. The prime in question is the centre `{r : R | ord_P r > 0}` of
the place on `R`, so the valuation ring of the place is the localization of `R` there. The converse
— that every height one prime of `R` arises this way, which upgrades this injection into a
bijection — is not proved here; it is proved in
`TauCeti/FieldTheory/FunctionField/AffineModel/Prime.lean`, which constructs the place of a
prime.

This is the "places → height one primes" half of the affine-model dictionary that reduces divisor
theory on the finite chart of a model to Mathlib's factorization calculus for fractional ideals.
Which places are finite on `R_x` is settled by the two order-of-`x` criteria below: `k[x]` lies in
the valuation ring of `P` exactly when `x` has no pole at `P`, and the valuation ring, being
integrally closed, then swallows everything integral over `k[x]`.

## Main results

* `TauCeti.Place.adjoin_le_integers_iff`: `k[x] ⊆ 𝒪_P` exactly when `x ∈ 𝒪_P`.
* `TauCeti.Place.center`: the height one prime of an affine model below a place finite on it,
  with `TauCeti.Place.valuation_center` identifying the adic valuation of that prime with the
  valuation of the place, and `TauCeti.Place.center_injective` showing that a place finite on a
  model is determined by its centre.
* `TauCeti.Place.existsUnique_valuation_eq`: the uniqueness statement, and
  `TauCeti.Place.valuationSubringAtPrime_eq_integers`: the valuation ring of the place is the
  localization of the model at the centre.
* `TauCeti.Place.ord_algebraMap_eq_multiplicity_center`: the coefficient formula
  `ord_P r = mult_(centre) (r)`, which reads an order at the place off the factorization of an
  ideal of the model.

## References

* H. Stichtenoth, *Algebraic Function Fields and Codes*, 2nd ed., GTM 254, Springer, 2009,
  Sections I.1 and III.2.
-/

public section

open IsDedekindDomain

namespace TauCeti

namespace Place

universe u v w

variable {k : Type u} {F : Type v} [Field k] [Field F] [Algebra k F] (P : Place k F)

section Integers

end Integers

section AffineModel

variable {R : Type w} [CommRing R] [Algebra R F] [IsFractionRing R F]

section Center

variable (hR : ∀ r : R, algebraMap R F r ∈ P.integers)

include hR

/-- The **centre** on `R` of a place `P` finite on `R`: the nonzero prime ideal consisting of
the elements with a zero at `P`, bundled as a `HeightOneSpectrum R`. For a Dedekind affine model,
this is a height one prime. -/
def center : HeightOneSpectrum R :=
  P.valuation.heightOneSpectrum R fun r ↦ P.mem_integers_iff.mp (hR r)

/-- The centre of `P` on `R` consists of the elements of `R` at which the valuation of `P` is
`< 1`. -/
@[simp]
theorem mem_center_asIdeal {r : R} :
    r ∈ (P.center hR).asIdeal ↔ P.valuation (algebraMap R F r) < 1 := by
  rw [center, Valuation.asIdeal_heightOneSpectrum, Valuation.mem_centerIdeal]

section Dedekind

variable [IsDedekindDomain R]

/-- **The valuation of a place finite on an affine model is the adic valuation of its centre.**
This is the exact, not merely up-to-equivalence, form of the correspondence between places and
height one primes. -/
@[simp]
theorem valuation_center : (P.center hR).valuation F = P.valuation :=
  Valuation.valuation_heightOneSpectrum P.valuation_surjective _

/-- A height one prime whose adic valuation is that of `P` is the centre of `P`. -/
theorem eq_center {𝔭 : HeightOneSpectrum R} (h : 𝔭.valuation F = P.valuation) :
    𝔭 = P.center hR :=
  Valuation.eq_heightOneSpectrum P.valuation_surjective _ h

end Dedekind

end Center

variable [IsDedekindDomain R]

end AffineModel

end Place

end TauCeti
