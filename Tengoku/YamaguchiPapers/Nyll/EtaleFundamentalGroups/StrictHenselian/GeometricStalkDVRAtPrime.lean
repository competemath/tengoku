/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkBaseLocalization
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.LocalEtaleDVR
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Etale
import Tengoku.Seed.AlgebraicGeometry.Morphisms.RingHomProperties
import Tengoku.Seed.RingTheory.Etale.Basic
import Tengoku.Seed.RingTheory.EssentialFiniteness
import Tengoku.Seed.RingTheory.Localization.Algebra
import Tengoku.Seed.RingTheory.RingHom.Etale
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# DVR geometric stalks from the ordinary local ring

The affine base need not be local. If its ordinary local ring at the
chosen point is a DVR, pointed affine neighborhoods have local rings
unramified over that actual DVR. Their unit-power factorizations pass to
the actual geometric stalk through the compatible localized germ maps.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory IsLocalRing

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field Ω] [IsSepClosed Ω] (φ : R →+* Ω)
  [IsDiscreteValuationRing (Localization.AtPrime (geometricBasePrime φ).asIdeal)]

end EtaleFundamentalGroups.StrictHenselian
