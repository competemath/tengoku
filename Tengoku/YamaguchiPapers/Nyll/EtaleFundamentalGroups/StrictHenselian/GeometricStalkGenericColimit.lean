/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalk
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkStructure
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkAlgebraColimit
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionTensor
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.StrictHenselian.GeometricStalkFractionFieldMap
import Tengoku.YamaguchiPapers.Nyll.EtaleFundamentalGroups.GenericTensor.FilteredColimit.CoconeLeg
import Tengoku.Seed.Algebra.Category.Ring.Under.Basic
import Tengoku.Seed.CategoryTheory.Limits.Cones
import Tengoku.Seed.CategoryTheory.Limits.Constructions.Over.Connected
import Tengoku.Seed.CategoryTheory.Limits.IsLimit
import Tengoku.Seed.CategoryTheory.Limits.Preserves.Basic
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.RingTheory.TensorProduct.Maps

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual strict generic field as a filtered colimit

Base-change the already constructed small pointed-neighborhood diagram from
R to its actual fraction field K. Its colimit is K ⊗[R] A, where A is the actual
geometric stalk. The existing fraction-tensor comparison identifies this ring
with Frac(A). Its K-scalar map is the existing geometricStalkFractionFieldMap:
fraction-ring extensionality reduces the comparison to the original map R → A.

Transporting the actual base-changed cocone along this K-algebra equivalence
gives a filtered colimit with vertex the actual strict generic field. The
literal cocone-leg formula retains both the fraction-field map and the actual
geometric-stalk germ maps.

This constructs the colimit required for finite-presentation descent over K,
without requiring finite presentation of K over R. It is a prerequisite for
[Stacks, Tag 0BSM](https://stacks.math.columbia.edu/tag/0BSM), not the full exact-sequence result.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped TensorProduct

namespace EtaleFundamentalGroups.StrictHenselian

universe u

variable {R Ω : Type u} [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
  [Field Ω] (φ : R →+* Ω)

variable [IsSepClosed Ω]

end EtaleFundamentalGroups.StrictHenselian
