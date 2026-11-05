/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Tengoku.Seed.RingTheory.Ideal.Maps
import Tengoku.Seed.RingTheory.Localization.AtPrime.Basic
import Tengoku.Seed.RingTheory.LocalRing.RingHom.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Localized neighborhood rings mapping to the geometric étale stalk

On an actual pointed étale neighborhood, take the prime ideal given by the
kernel of evaluation in the geometric field. Every section outside this ideal
has an invertible germ. The universal property of localization therefore
constructs a map from the actual local ring of sections at this prime to the
geometric stalk. This map is local, as follows from the criterion for a fraction
to be a unit in a localization at a prime.

This supplies the local-stage maps needed to transfer local algebra from
affine étale neighborhoods. No local-stage map or comparison is postulated.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω]
  (s : Spec (.of Ω) ⟶ S) (W : S.Etale)
  (t : (Scheme.pointEtaleNeighborhoods s).fiber.obj W)

/-- The actual prime of the neighborhood's ring of sections selected by its
given geometric point.-/
def geometricNeighborhoodPrime : PrimeSpectrum Γ(W.left, ⊤) :=
  ⟨RingHom.ker (t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom,
    RingHom.ker_isPrime _⟩

/-- A denominator outside the selected prime has an invertible germ.-/
theorem geometricStalkGerm_isUnit_of_mem_primeCompl
    (a : (geometricNeighborhoodPrime s W t).asIdeal.primeCompl) :
    IsUnit (geometricStalkGerm s W t a) := by
  apply geometricStalk_isUnit_of_evaluation_ne_zero s
  have ha := a.property
  change (t.left.appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of Ω)).hom).hom (a : Γ(W.left, ⊤)) ≠ 0 at ha
  intro hzero
  apply ha
  exact (ConcreteCategory.congr_hom (geometricStalkGerm_evaluation s W t) a).symm.trans hzero

/-- The actual local ring of sections at the chosen point maps to the geometric
stalk by localization of the germ map.-/
def geometricStalkLocalizedGerm :
    Localization.AtPrime (geometricNeighborhoodPrime s W t).asIdeal →+* geometricStalk s :=
  IsLocalization.lift (S := Localization.AtPrime (geometricNeighborhoodPrime s W t).asIdeal)
    (g := (geometricStalkGerm s W t).hom)
    (geometricStalkGerm_isUnit_of_mem_primeCompl s W t)

end EtaleFundamentalGroups.StrictHenselian
