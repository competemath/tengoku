/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.RingTheory.DedekindDomain.AdicValuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport of the height-one spectrum and adic valuation under a ring isomorphism

Let `e : R ≃+* S` be an isomorphism of Dedekind domains. This file builds the transport of the
**height-one spectrum** and the **adic (int)valuation** along `e`:

* `RingEquiv.idealMulEquiv e : Ideal R ≃* Ideal S` — the multiplicative isomorphism of ideal
  monoids induced by `e` (the `Ideal.map`/`Ideal.map e.symm` pair).
* `IsDedekindDomain.HeightOneSpectrum.mapEquiv e : HeightOneSpectrum R ≃ HeightOneSpectrum S` —
  the induced bijection of closed points, `v ↦ Ideal.map e v.asIdeal`.
* `IsDedekindDomain.HeightOneSpectrum.intValuation_mapEquiv` — the valuation is preserved:
  `(mapEquiv e v).intValuation (e r) = v.intValuation r`.

These are the general Dedekind-domain infrastructure underlying the pullback of divisors and orders
of vanishing along a ring automorphism (e.g. the translation-by-a-point automorphism of the
function field of an elliptic curve).

## Main statements

* `RingEquiv.idealMulEquiv_apply`, `RingEquiv.idealMulEquiv_symm_apply`.
* `IsDedekindDomain.HeightOneSpectrum.mapEquiv_asIdeal`, `_symm`.
* `IsDedekindDomain.HeightOneSpectrum.intValuation_mapEquiv`.
-/

open IsDedekindDomain

variable {R S : Type*} [CommRing R] [CommRing S]

/-- A ring isomorphism `e : R ≃+* S` induces a multiplicative isomorphism `Ideal R ≃* Ideal S` of
the ideal monoids, given by `Ideal.map e` (with inverse `Ideal.map e.symm`). -/
def RingEquiv.idealMulEquiv (e : R ≃+* S) : Ideal R ≃* Ideal S :=
  { e.idealComapOrderIso.symm.toEquiv with
    map_mul' := fun I J => Ideal.map_mul e I J }

@[simp]
lemma RingEquiv.idealMulEquiv_apply (e : R ≃+* S) (I : Ideal R) :
    e.idealMulEquiv I = I.map e := rfl

namespace IsDedekindDomain.HeightOneSpectrum

variable [IsDedekindDomain R] [IsDedekindDomain S]

/-- The image of a height-one prime `v` of `R` under a ring isomorphism `e : R ≃+* S`, as a
height-one prime of `S`: its underlying ideal is `Ideal.map e v.asIdeal`. -/
def map (e : R ≃+* S) (v : HeightOneSpectrum R) : HeightOneSpectrum S where
  asIdeal := Ideal.map e v.asIdeal
  isPrime := inferInstance
  ne_bot := by
    rw [ne_eq, Ideal.map_eq_bot_iff_of_injective e.injective]
    exact v.ne_bot

omit [IsDedekindDomain R] [IsDedekindDomain S] in
@[simp]
lemma asIdeal_map (e : R ≃+* S) (v : HeightOneSpectrum R) :
    (v.map e).asIdeal = Ideal.map e v.asIdeal := rfl

/-- The bijection of closed points (height-one primes) induced by a ring isomorphism
`e : R ≃+* S`. -/
def mapEquiv (e : R ≃+* S) : HeightOneSpectrum R ≃ HeightOneSpectrum S where
  toFun := map e
  invFun := map e.symm
  left_inv v := by
    apply HeightOneSpectrum.ext
    rw [asIdeal_map, asIdeal_map, Ideal.map_symm, Ideal.comap_map_of_bijective _ e.bijective]
  right_inv v := by
    apply HeightOneSpectrum.ext
    rw [asIdeal_map, asIdeal_map, ← Ideal.comap_symm e,
      Ideal.comap_map_of_bijective _ e.symm.bijective]

omit [IsDedekindDomain R] [IsDedekindDomain S] in
@[simp]
lemma mapEquiv_asIdeal (e : R ≃+* S) (v : HeightOneSpectrum R) :
    (mapEquiv e v).asIdeal = Ideal.map e v.asIdeal := rfl

omit [IsDedekindDomain R] [IsDedekindDomain S] in
@[simp]
lemma mapEquiv_symm (e : R ≃+* S) : (mapEquiv e).symm = mapEquiv e.symm := rfl

/-- The adic valuation is transported by `mapEquiv`: the `mapEquiv e v`-adic valuation of `e r`
equals the `v`-adic valuation of `r`. -/
theorem intValuation_mapEquiv (e : R ≃+* S) (v : HeightOneSpectrum R) (r : R) :
    (mapEquiv e v).intValuation (e r) = v.intValuation r := by
  obtain rfl | hr := eq_or_ne r 0
  · simp
  · have her : e r ≠ 0 := by simpa [EmbeddingLike.map_eq_zero_iff] using hr
    rw [(mapEquiv e v).intValuation_eq_exp_neg_multiplicity her,
      v.intValuation_eq_exp_neg_multiplicity hr]
    congr 1
    rw [mapEquiv_asIdeal]
    have hspan : (Ideal.span {e r} : Ideal S) = Ideal.map e (Ideal.span {r}) := by
      rw [Ideal.map_span, Set.image_singleton]
    rw [hspan, ← e.idealMulEquiv_apply v.asIdeal, ← e.idealMulEquiv_apply (Ideal.span {r}),
      multiplicity_map_eq]

end IsDedekindDomain.HeightOneSpectrum
