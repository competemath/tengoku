/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.FunctionalAnalysis.BanachSteinhaus
import Tengoku.Seed.Analysis.Normed.Operator.Banach

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Banach open mapping theorem

For continuous linear maps between Banach spaces, surjectivity forces images of open sets to be
open.  `IsOpenMap` is exactly this textbook property, so it is used directly as the public carrier.
-/

namespace SandronesLibrary.FunctionalAnalysis

open Set
open SandronesLibrary.Topology.NormedSpace

variable {E F : Type*}
variable [NormedAddCommGroup E] [NormedAddCommGroup F]
variable [NormedLinearSpace ℝ E] [NormedLinearSpace ℝ F]
variable [BanachSpace E] [BanachSpace F]

/-- **Banach open mapping theorem**: a surjective continuous linear map between Banach spaces is
an open map.

> **Entry**: functional-analysis.open-mapping
@isnad1 id=isopenma.1h3v.s8.c41f8ac6ad1f from=translated src=- shape=0895d3e9 vocab=60c93c24
-/
theorem surjective_continuousLinearMap_isOpenMap (T : E →L[ℝ] F)
    (hT : Function.Surjective T) : IsOpenMap T := by
  exact T.isOpenMap hT

/-- Textbook expansion: the image of every open set under a surjective continuous linear map is
open.
@isnad1 id=isopen.2h4v.s8.cf5ffa651247 from=translated src=- shape=87a50806 vocab=2a0e5aaa
-/
theorem image_isOpen_of_surjective_continuousLinearMap (T : E →L[ℝ] F)
    (hT : Function.Surjective T) {U : Set E} (hU : IsOpen U) : IsOpen (T '' U) := by
  exact surjective_continuousLinearMap_isOpenMap T hT U hU

/-- A surjective continuous linear map between Banach spaces is also a topological quotient map.
@isnad1 id=isquotie.1h3v.s8.593ffa9e1318 from=translated src=- shape=0895d3e9 vocab=55ebe0a8
-/
theorem surjective_continuousLinearMap_isQuotientMap (T : E →L[ℝ] F)
    (hT : Function.Surjective T) : Topology.IsQuotientMap T := by
  exact T.isQuotientMap hT

end SandronesLibrary.FunctionalAnalysis
