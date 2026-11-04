/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.AlgebraicGeometry.Stalk
import Tengoku.Seed.AlgebraicGeometry.AffineScheme
import Tengoku.Seed.AlgebraicGeometry.FunctionField
import Tengoku.Seed.AlgebraicGeometry.Properties
import Tengoku.Seed.RingTheory.Ideal.Height
import Tengoku.Seed.RingTheory.Localization.LocalizationLocalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The generization dictionary for stalks

P2.5a.  For a specialization `x ⤳ y` in a scheme `X`, mathlib supplies the ring map
`X.presheaf.stalkSpecializes h : 𝒪_{X,y} ⟶ 𝒪_{X,x}` but says nothing about what kind of map it
is.  This file proves that it is a localization at a prime, and assembles the resulting dictionary
between the points of `X` specializing to `y` and the primes of the local ring `𝒪_{X,y}`.

* `stalkSpecializesAlgebra h` is the `𝒪_{X,y}`-algebra structure on `𝒪_{X,x}` given by the
  generization map.
* `stalkPrimeOfSpecializes h` is the prime of `𝒪_{X,y}` attached to the generization `x`: the
  contraction of the maximal ideal of `𝒪_{X,x}`.
* `isLocalization_stalkSpecializes` is the missing lemma: `𝒪_{X,x}` *is* the localization of
  `𝒪_{X,y}` at that prime.  Everything else in this file follows from it or from
  `Scheme.range_fromSpecStalk`.
* `fromSpecStalk_stalkPrimeOfSpecializes`, `stalkPrimeOfSpecializes_injective` and
  `exists_specializes_stalkPrimeOfSpecializes_eq` say that `x ↦ stalkPrimeOfSpecializes` is a
  bijection from the generizations of `y` onto the primes of `𝒪_{X,y}`.
* `height_stalkPrimeOfSpecializes` says that bijection matches height with codimension, so the
  height-one primes of `𝒪_{X,y}` are exactly the codimension-one points specializing to `y`.
* `isScalarTower_functionField` says the generization maps commute with the embeddings into the
  function field, so `Scheme.ord` at `x` is the valuation of the localized `𝒪_{X,y}`.

The proof of `isLocalization_stalkSpecializes` is chart-local: on an affine open `U ∋ y` (which
then also contains the generization `x`) both stalks are localizations of `Γ(X, U)`, at primes
`p_x ≤ p_y` because `hU.isoSpec` is continuous and specialization in `Spec` is inclusion of primes.
`IsLocalization.isLocalization_of_submonoid_le` turns that into a localization of `𝒪_{X,y}` at the
image of `p_x.primeCompl`, and `IsLocalization.isLocalization_of_is_exists_mul_mem` saturates that
submonoid to the full prime complement.

This is the input consumed by `Chow/SurfaceRestrictionLocalFactorization.lean`: at a closed point
`pt` of a regular surface the stalk is a two-dimensional regular local ring, factorial by
`IsRegularLocalRing.uniqueFactorizationMonoid_of_ringKrullDim_eq_two`, and this file is what
converts the global coefficients of a relation cycle into local exponents at `pt`.
-/

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Order

universe u

namespace AlgebraicGeometry.Scheme

variable {X : Scheme.{u}} {x y : X}

/-- The `𝒪_{X,y}`-algebra structure on the stalk at a generization `x` of `y`.-/
@[reducible] def stalkSpecializesAlgebra (h : x ⤳ y) :
    Algebra (X.presheaf.stalk y) (X.presheaf.stalk x) :=
  (X.presheaf.stalkSpecializes h).hom.toAlgebra

/-- The prime ideal of `𝒪_{X,y}` cut out by a generization `x` of `y`.-/
def stalkPrimeOfSpecializes (h : x ⤳ y) : Ideal (X.presheaf.stalk y) :=
  (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).comap (X.presheaf.stalkSpecializes h).hom

/--
@isnad1 id=isprime.1h3v.s7.b2f995381c3b from=translated src=- shape=7a500ebf vocab=b3ae315b
-/
instance stalkPrimeOfSpecializes_isPrime (h : x ⤳ y) : (stalkPrimeOfSpecializes h).IsPrime := by
  unfold stalkPrimeOfSpecializes
  infer_instance

/-- **The generization dictionary, localization half.**  If `x` is a generization of `y`, then
`𝒪_{X,x}` is the localization of `𝒪_{X,y}` at the prime `stalkPrimeOfSpecializes h`.
@isnad1 id=atprime.1h3v.s7.ca8c78d3c77a from=translated src=- shape=c8924309 vocab=1f91d37a
-/
theorem isLocalization_stalkSpecializes (h : x ⤳ y) :
    letI := stalkSpecializesAlgebra h
    IsLocalization.AtPrime (X.presheaf.stalk x) (stalkPrimeOfSpecializes h) := by
  letI := stalkSpecializesAlgebra h
  -- an affine chart around `y`; the generization `x` lies in it too
  set U : X.Opens := (X.affineCover.f (X.affineCover.idx y)).opensRange with hUdef
  have hU : IsAffineOpen U := isAffineOpen_opensRange _
  have hyU : y ∈ U := X.affineCover.covers y
  have hxU : x ∈ U := h.mem_open U.2 hyU
  letI algy : Algebra Γ(X, U) (X.presheaf.stalk y) :=
    X.presheaf.algebra_section_stalk ⟨y, hyU⟩
  letI algx : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk ⟨x, hxU⟩
  haveI hlx := hU.isLocalization_stalk ⟨x, hxU⟩
  haveI hly := hU.isLocalization_stalk ⟨y, hyU⟩
  set px : Ideal Γ(X, U) := (hU.primeIdealOf ⟨x, hxU⟩).asIdeal with hpxdef
  set py : Ideal Γ(X, U) := (hU.primeIdealOf ⟨y, hyU⟩).asIdeal with hpydef
  -- specialization in `X` becomes inclusion of primes in the chart
  have hle : px ≤ py := by
    have hsub : (⟨x, hxU⟩ : U) ⤳ (⟨y, hyU⟩ : U) := (subtype_specializes_iff _ _).mpr h
    exact (PrimeSpectrum.le_iff_specializes _ _).mpr
      (hsub.map (Scheme.Hom.continuous hU.isoSpec.hom))
  have hcompl : py.primeCompl ≤ px.primeCompl := fun a ha ha' => ha (hle ha')
  -- the germ maps form a scalar tower along the generization map
  haveI htower : IsScalarTower Γ(X, U) (X.presheaf.stalk y) (X.presheaf.stalk x) := by
    refine IsScalarTower.of_algebraMap_eq' ?_
    have hgerm := X.presheaf.germ_stalkSpecializes (U := U) hyU h
    have hgerm' := congrArg CommRingCat.Hom.hom hgerm
    simp only [CommRingCat.hom_comp] at hgerm'
    simpa [RingHom.algebraMap_toAlgebra] using hgerm'.symm
  -- transport of germs along the generization map
  have hmap : ∀ a : Γ(X, U), (X.presheaf.stalkSpecializes h).hom
      (algebraMap Γ(X, U) (X.presheaf.stalk y) a) = algebraMap Γ(X, U) (X.presheaf.stalk x) a := by
    intro a
    rw [IsScalarTower.algebraMap_apply Γ(X, U) (X.presheaf.stalk y) (X.presheaf.stalk x) a]
    simp [RingHom.algebraMap_toAlgebra]
  -- the stalk at `x` is a localization of the stalk at `y`, first at the image submonoid
  haveI key : IsLocalization (px.primeCompl.map (algebraMap Γ(X, U) (X.presheaf.stalk y)))
      (X.presheaf.stalk x) :=
    IsLocalization.isLocalization_of_submonoid_le (X.presheaf.stalk y) (X.presheaf.stalk x)
      py.primeCompl px.primeCompl hcompl
  -- and then at the saturation of that submonoid, which is the prime complement we want
  refine IsLocalization.isLocalization_of_is_exists_mul_mem (X.presheaf.stalk x)
    (px.primeCompl.map (algebraMap Γ(X, U) (X.presheaf.stalk y)))
    (stalkPrimeOfSpecializes h).primeCompl ?_ ?_
  · rintro _ ⟨a, ha, rfl⟩
    show _ ∉ stalkPrimeOfSpecializes h
    rw [stalkPrimeOfSpecializes, Ideal.mem_comap, hmap a, IsLocalRing.notMem_maximalIdeal]
    exact IsLocalization.map_units (X.presheaf.stalk x) ⟨a, ha⟩
  · rintro ⟨u, hu⟩
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (M := py.primeCompl) u
    have hfu : IsUnit ((X.presheaf.stalkSpecializes h).hom u) := by
      rw [← IsLocalRing.notMem_maximalIdeal]
      exact hu
    have hfs : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) (s : Γ(X, U))) :=
      IsLocalization.map_units (X.presheaf.stalk x) ⟨(s : Γ(X, U)), hcompl s.2⟩
    have hfa : IsUnit (algebraMap Γ(X, U) (X.presheaf.stalk x) a) := by
      have := congrArg (X.presheaf.stalkSpecializes h).hom e
      rw [map_mul, hmap, hmap] at this
      rw [← this]
      exact hfu.mul hfs
    have ha : a ∈ px.primeCompl :=
      (IsLocalization.AtPrime.isUnit_to_map_iff (X.presheaf.stalk x) px a).mp hfa
    refine ⟨algebraMap Γ(X, U) (X.presheaf.stalk y) (s : Γ(X, U)), ?_⟩
    rw [mul_comm, e]
    exact Submonoid.mem_map_of_mem _ ha

/-- `𝒪_{X,x}` is, as an `𝒪_{X,y}`-algebra, the localization of `𝒪_{X,y}` at the prime attached to
the generization `x`.-/
def stalkSpecializesAlgEquiv (h : x ⤳ y) :
    letI := stalkSpecializesAlgebra h
    Localization.AtPrime (stalkPrimeOfSpecializes h) ≃ₐ[X.presheaf.stalk y]
      X.presheaf.stalk x :=
  letI := stalkSpecializesAlgebra h
  haveI := isLocalization_stalkSpecializes h
  IsLocalization.algEquiv (stalkPrimeOfSpecializes h).primeCompl _ _

/-- The generization map `𝒪_{X,y} ⟶ 𝒪_{X,x}` is compatible with the two embeddings into the
function field.  Together with `isLocalization_stalkSpecializes` this says that the order of
vanishing at `x` is the valuation of the localization of `𝒪_{X,y}` at
`stalkPrimeOfSpecializes h`.
@isnad1 id=isscalar.1h3v.s8.002434fef0bd from=translated src=- shape=17bcf193 vocab=61bb6283
-/
theorem isScalarTower_functionField [IrreducibleSpace X] (h : x ⤳ y) :
    letI := stalkSpecializesAlgebra h
    IsScalarTower (X.presheaf.stalk y) (X.presheaf.stalk x) X.functionField := by
  letI := stalkSpecializesAlgebra h
  apply IsScalarTower.of_algebraMap_eq'
  simp_rw [RingHom.algebraMap_toAlgebra]
  change _ = (X.presheaf.stalkSpecializes h ≫ _).hom
  rw [X.presheaf.stalkSpecializes_comp]

/-- **The generization dictionary, height half.**  The prime attached to a generization `x` of `y`
has height equal to the codimension of `x`.  In particular the height-one primes of `𝒪_{X,y}`
correspond exactly to the codimension-one points of `X` specializing to `y`.
@isnad1 id=eq.1h3v.s6.e01ec7a4684d from=translated src=- shape=9156c883 vocab=9b45decc
-/
theorem height_stalkPrimeOfSpecializes (h : x ⤳ y) :
    (stalkPrimeOfSpecializes h).height = Order.coheight x := by
  letI := stalkSpecializesAlgebra h
  haveI := isLocalization_stalkSpecializes h
  have h1 : ringKrullDim (X.presheaf.stalk x) = (stalkPrimeOfSpecializes h).height :=
    IsLocalization.AtPrime.ringKrullDim_eq_height _ _
  have h2 : ringKrullDim (X.presheaf.stalk x) = Order.coheight x :=
    ringKrullDim_stalk_eq_coheight x
  exact_mod_cast h1.symm.trans h2

end AlgebraicGeometry.Scheme
