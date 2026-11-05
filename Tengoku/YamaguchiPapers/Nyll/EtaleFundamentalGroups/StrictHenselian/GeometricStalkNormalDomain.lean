/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkLocalizedGerm
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Descent.EtaleAtPrimeNormality
import Tengoku.Seed.AlgebraicGeometry.Morphisms.Etale
import Tengoku.Seed.AlgebraicGeometry.Morphisms.RingHomProperties
import Tengoku.Seed.Data.Fin.VecNotation
import Tengoku.Seed.RingTheory.RingHom.Etale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual geometric étale stalk over a normal domain is a domain

A zero-product relation between two germs descends to an actual pointed étale
neighborhood, then to an affine refinement. Localizing its sections at the
prime selected by the geometric point gives a domain, by normality of prime
localizations of étale algebras over a normal domain. Its localized germ map
carries one of the two zero factors back to the geometric stalk.

No discrete valuation, Noetherianity, or localness of the base ring is needed.
This supplies the domain needed to use the actual fraction field of a strict
henselization over a normal local ring. Integral closedness of this stalk and
the generic tensor comparison are separate results.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field Ω] (φ : R →+* Ω)

end EtaleFundamentalGroups.StrictHenselian
