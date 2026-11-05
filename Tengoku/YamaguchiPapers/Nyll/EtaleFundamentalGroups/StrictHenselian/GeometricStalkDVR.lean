/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkDVRAtPrime
import Tengoku.Seed.Algebra.Group.Irreducible.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual geometric étale stalk of a DVR is a DVR

These are the local-base corollaries of the ordinary-local-ring result.
The factorization and maximal-ideal proofs are shared with arbitrary
affine bases rather than repeated here.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω) [IsLocalHom φ]

private def geometricBaseLocalizationEquivOfLocal :
    R ≃ₐ[R] Localization.AtPrime (geometricBasePrime φ).asIdeal :=
  IsLocalization.atUnits R (geometricBasePrime φ).asIdeal.primeCompl
    (S := Localization.AtPrime (geometricBasePrime φ).asIdeal) (by
      intro r hr
      change IsUnit r
      have hrφ : φ r ≠ 0 := hr
      exact IsLocalHom.map_nonunit (f := φ) r (isUnit_iff_ne_zero.mpr hrφ))

end EtaleFundamentalGroups.StrictHenselian
