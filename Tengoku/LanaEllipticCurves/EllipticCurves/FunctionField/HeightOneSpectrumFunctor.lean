/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.LanaEllipticCurves.EllipticCurves.FunctionField.HeightOneSpectrumMap

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Functoriality of the transport of closed points along ring isomorphisms

`EllipticCurves.FunctionField.HeightOneSpectrumMap` transports a height-one prime along a *single*
ring isomorphism `e : R ≃+* S` of Dedekind domains, as `HeightOneSpectrum.map e` and its packaging
`HeightOneSpectrum.mapEquiv e`. This file records that the transport is **functorial in `e`**:
it takes the identity to the identity and a composite to the composite.

The point of doing so is that a *group* of ring automorphisms then acts on the set of closed
points. Without these two lemmas, `mapEquiv e` is a bijection of closed points for each `e`
separately, with nothing relating the bijections attached to different `e` — one cannot even state
"the Galois group acts on the closed points of a curve", let alone compose two such transports.
`mapAut` packages exactly that action, as a `MonoidHom` from `RingAut R` to `Equiv.Perm`.

## Main statements

* `IsDedekindDomain.HeightOneSpectrum.map_refl` / `map_trans` — functoriality of `map`;
* `IsDedekindDomain.HeightOneSpectrum.mapEquiv_refl` / `mapEquiv_trans` — the same for `mapEquiv`;
* `IsDedekindDomain.HeightOneSpectrum.mapAut` — the induced group homomorphism
  `RingAut R →* Equiv.Perm (HeightOneSpectrum R)`.

## Implementation notes

`Ideal.map` takes an argument in a `RingHomClass`, so `Ideal.map (e : R ≃+* S) I` is *not*
syntactically `Ideal.map (e : R →+* S) I`, and `rw [Ideal.map_id]` / `rw [Ideal.map_map]` fail to
find their patterns. The two coercions are definitionally equal, so `exact` closes both goals where
`rw` cannot; that is why the proofs below are `exact`s with explicit `→+*` ascriptions.

Both `Equiv.Perm` and `RingAut` multiply by `g * h = h.trans g` — composition, not `trans` order —
which is why `mapAut`'s `map_mul'` field applies `mapEquiv_trans` with its arguments swapped.

This file mentions no curve and is general Dedekind-domain algebra; it is an upstream candidate
alongside `HeightOneSpectrumMap`.
-/

open IsDedekindDomain

namespace IsDedekindDomain.HeightOneSpectrum

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [IsDedekindDomain R] [IsDedekindDomain S] [IsDedekindDomain T]

omit [IsDedekindDomain R] in
/-- Transport along the identity isomorphism fixes every closed point. -/
@[simp]
lemma map_refl (v : HeightOneSpectrum R) : v.map (RingEquiv.refl R) = v := by
  apply HeightOneSpectrum.ext
  exact Ideal.map_id v.asIdeal

omit [IsDedekindDomain R] [IsDedekindDomain S] [IsDedekindDomain T] in
/-- Transport along a composite isomorphism is the composite of the transports. -/
lemma map_trans (e : R ≃+* S) (e' : S ≃+* T) (v : HeightOneSpectrum R) :
    v.map (e.trans e') = (v.map e).map e' := by
  apply HeightOneSpectrum.ext
  exact (Ideal.map_map (e : R →+* S) (e' : S →+* T)).symm

omit [IsDedekindDomain R] in
@[simp]
lemma mapEquiv_refl : mapEquiv (RingEquiv.refl R) = Equiv.refl (HeightOneSpectrum R) :=
  Equiv.ext map_refl

omit [IsDedekindDomain R] [IsDedekindDomain S] [IsDedekindDomain T] in
lemma mapEquiv_trans (e : R ≃+* S) (e' : S ≃+* T) :
    mapEquiv (e.trans e') = (mapEquiv e).trans (mapEquiv e') :=
  Equiv.ext (map_trans e e')

/-- **Ring automorphisms act on closed points.** The permutation of the height-one spectrum
attached to a ring automorphism, as a group homomorphism `RingAut R →* Equiv.Perm _`.

The two functoriality lemmas above are exactly the two `MonoidHom` fields; note that both groups
multiply by composition (`g * h = h.trans g`), whence the swap in `map_mul'`. -/
def mapAut : RingAut R →* Equiv.Perm (HeightOneSpectrum R) where
  toFun e := mapEquiv e
  map_one' := mapEquiv_refl
  map_mul' e e' := mapEquiv_trans e' e

omit [IsDedekindDomain R] in
@[simp]
lemma mapAut_apply (e : RingAut R) (v : HeightOneSpectrum R) : mapAut e v = v.map e := rfl

end IsDedekindDomain.HeightOneSpectrum
