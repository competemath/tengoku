/-
Anthropic FLT upstream notice: Copyright 2026 Anthropic, PBC.
Released under Apache 2.0 license as described in the file LICENSE.
Anthropic FLT source material is identified by code comparison;
the exact source-file correspondence remains unresolved.
Upstream repository: https://github.com/anthropics/fermats-last-theorem
Upstream NOTICE: https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/NOTICE
Upstream per-file ATTRIBUTION (earlier FLT and Mathlib notices): https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/ATTRIBUTION.md

Local adaptation and maintenance: Naganori Yamaguchi (https://github.com/n-yamaguchi-0729).
AI assistance in local adaptation and maintenance: OpenAI Codex.
-/

import Tengoku.Seed.Algebra.Algebra.Subalgebra.Basic
import Tengoku.Seed.Algebra.Group.Action.Defs
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs
import Tengoku.Seed.RingTheory.DedekindDomain.Basic
import Tengoku.Seed.RingTheory.KrullDimension.Basic
import Tengoku.Seed.RingTheory.Localization.FractionRing
import Tengoku.Seed.RingTheory.Noetherian.Defs
import Tengoku.YamaguchiPapers.Nyll.SchemeTheory.RingTheory.Dimension.SubalgebraNoetherianDimensionLEOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Noetherian subalgebras of finite fraction-field extensions

Subalgebras of finite-dimensional fraction-field extensions of Noetherian
domains of Krull dimension at most one are Noetherian and have Krull
dimension at most one.
-/

section ProofImplementation

namespace AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
namespace IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra

universe u v w

end IsNoetherianRing_of_ringKrullDim_le_one_of_finiteDimensional_subalgebra
end AlgebraicCurves.Foundations.CommutativeAlgebra.Proofs
end ProofImplementation
