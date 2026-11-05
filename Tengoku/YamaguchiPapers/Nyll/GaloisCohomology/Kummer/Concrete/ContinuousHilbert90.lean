/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.FieldTheory.Galois.Infinite
import Tengoku.Seed.FieldTheory.Galois.Profinite
import Tengoku.Seed.RepresentationTheory.Homological.GroupCohomology.Hilbert90
import Tengoku.Seed.Topology.LocallyConstant.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Noether Hilbert 90 for an infinite Galois extension

A locally constant multiplicative cocycle descends to a finite Galois stage.
An open normal subgroup in its identity fiber fixes every cocycle value, so the
finite-stage cocycle takes values in that actual intermediate field. Finite
Noether Hilbert 90 then produces a coboundary in the original extension.
-/

namespace KummerTheory
open scoped Topology
open groupCohomology
universe u v
variable {K : Type u} {Ω : Type v} [Field K] [Field Ω] [Algebra K Ω]
  [IsGalois K Ω]

end KummerTheory
