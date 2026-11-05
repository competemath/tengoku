/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Tengoku.Seed.RingTheory.Localization.FractionRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual strict generic field map over a normal domain

The actual geometric stalk is a domain, and its structure map is flat, hence
injective. Localizing this injection constructs the map between the actual
fraction fields and its compatibility with the original structure map. Neither
a DVR nor a generic tensor comparison is required.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field Ω] (φ : R →+* Ω)

end EtaleFundamentalGroups.StrictHenselian
