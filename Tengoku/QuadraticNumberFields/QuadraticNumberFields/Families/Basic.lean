/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.QuadraticNumberFields.QuadraticNumberFields.Qsqrtd.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Parameter Families for Quadratic Fields

This file contains lightweight shared definitions for explicit quadratic-field
families used in class-number-one and class-number-divisibility problems.
-/
namespace Tengoku.QuadraticNumberFields end Tengoku.QuadraticNumberFields open Tengoku.QuadraticNumberFields
local notation "ℚ√" d => Qsqrtd d

namespace QuadraticNumberFields
namespace Families

/-- The standard field attached to an integer parameter `d`.-/
abbrev fieldOfParam (d : ℤ) : Type :=
  Qsqrtd (d : ℚ)

/-- Predicate packaging the standard squarefree hypotheses used by this project.-/
def IsAdmissibleParam (d : ℤ) : Prop :=
  Squarefree d ∧ d ≠ 1

end Families
end QuadraticNumberFields
-- Tengoku: root names of this library moved to Tengoku.QuadraticNumberFields so they do not collide with other libraries (generated)
