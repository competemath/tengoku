/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkNormalDomain
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFlat
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkGenericIntegral
import Tengoku.Seed.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Tengoku.Seed.RingTheory.Localization.BaseChange
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.RingTheory.TensorProduct.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual fraction field of the geometric étale stalk

For a normal domain, the generic tensor of its actual geometric stalk
is a localization of a domain at nonzero elements. It is integral over the
original fraction field, so every nonzero element is a unit. Thus it is the
fraction ring of the actual stalk, with its canonical scalar map.

The resulting comparison uses the existing tensor and localization algebra
structures. No field structure is installed on the tensor product, and no
uniformizer or finite presentation of the original fraction field is used.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped TensorProduct nonZeroDivisors

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field Ω] (φ : R →+* Ω)

end EtaleFundamentalGroups.StrictHenselian
