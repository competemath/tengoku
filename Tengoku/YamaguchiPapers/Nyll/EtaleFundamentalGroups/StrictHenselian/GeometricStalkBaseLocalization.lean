/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkLocalizedGerm
import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic
import Tengoku.Seed.RingTheory.Localization.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ordinary local ring mapping to the actual geometric stalk

For any geometric point of an affine scheme, the structure map factors
through the localization at its actual kernel prime. This factorization
is local, and for a domain base it is injective. No comparison with a
separately postulated strict henselization is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [Field Ω] (φ : R →+* Ω)

/-- The actual prime of the affine base selected by the geometric point.-/
def geometricBasePrime : PrimeSpectrum R :=
  ⟨RingHom.ker φ, RingHom.ker_isPrime φ⟩

private theorem geometricBaseDenominatorUnit
    (r : (geometricBasePrime φ).asIdeal.primeCompl) :
    IsUnit (geometricStalkStructureMap φ r) := by
  apply geometricStalk_isUnit_of_evaluation_ne_zero
    (Spec.map (CommRingCat.ofHom φ))
  rw [geometricStalkStructureMap_evaluation_apply]
  exact r.property

/-- The actual structure map extended from the affine base to its ordinary local ring.-/
def geometricStalkBaseLocalizationMap :
    Localization.AtPrime (geometricBasePrime φ).asIdeal →+*
      geometricStalk (Spec.map (CommRingCat.ofHom φ)) :=
  IsLocalization.lift (S := Localization.AtPrime (geometricBasePrime φ).asIdeal)
    (g := geometricStalkStructureMap φ) (geometricBaseDenominatorUnit φ)

/-- The prime selected on an actual neighborhood lies over the actual kernel
prime on the affine base.
@isnad1 id=eq.0h5v.s16.ca772948ef80 from=translated src=- shape=dc6197a4 vocab=6c0d2ff3
-/
theorem geometricNeighborhoodPrime_comap_structure
    (V : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj V) :
    (geometricNeighborhoodPrime (Spec.map (CommRingCat.ofHom φ)) V v).asIdeal.comap
      (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom) =
        (geometricBasePrime φ).asIdeal := by
  let s := Spec.map (CommRingCat.ofHom φ)
  let β := ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom
  ext r
  change (v.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom) (β r) = 0 ↔
    φ r = 0
  have h₁ :
      geometricStalkEvaluation s (geometricStalkGerm s V v (β r)) =
        (v.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom) (β r) :=
    ConcreteCategory.congr_hom (geometricStalkGerm_evaluation s V v) (β r)
  have h₂ : geometricStalkGerm s V v (β r) = geometricStalkStructureMap φ r :=
    RingHom.congr_fun (geometricStalkGerm_comp_structure φ V v) r
  rw [← h₁, h₂, geometricStalkStructureMap_evaluation_apply]

/-- The actual map between ordinary local rings selected by a pointed
étale neighborhood, constructed by Mathlib's localization functor.-/
def geometricNeighborhoodBaseLocalizationMap
    (V : (Spec (CommRingCat.of R)).Etale)
    (v : (Scheme.pointEtaleNeighborhoods (Spec.map (CommRingCat.ofHom φ))).fiber.obj V) :
    Localization.AtPrime (geometricBasePrime φ).asIdeal →+*
      Localization.AtPrime
        (geometricNeighborhoodPrime (Spec.map (CommRingCat.ofHom φ)) V v).asIdeal :=
  Localization.localRingHom (geometricBasePrime φ).asIdeal
    (geometricNeighborhoodPrime (Spec.map (CommRingCat.ofHom φ)) V v).asIdeal
    (((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ V.hom.appTop).hom)
    (geometricNeighborhoodPrime_comap_structure φ V v).symm

end EtaleFundamentalGroups.StrictHenselian
