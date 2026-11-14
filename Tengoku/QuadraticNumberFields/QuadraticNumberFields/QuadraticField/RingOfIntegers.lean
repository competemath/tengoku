/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/

import Tengoku.QuadraticNumberFields.QuadraticNumberFields.QuadraticField.Basic
import Tengoku.Seed.NumberTheory.NumberField.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rings of Integers of Abstract Quadratic Fields

This file collects basic structural facts about the ring of integers of an
abstract quadratic field.

## Main results

* `QuadraticField.ringOfIntegers_isQuadraticExtension`: `𝓞 K` is a quadratic
  extension of `ℤ` when `K` is a quadratic field over `ℚ`.
-/
namespace Tengoku.QuadraticNumberFields end Tengoku.QuadraticNumberFields open Tengoku.QuadraticNumberFields
local notation "ℚ√" d => Qsqrtd d

open scoped NumberField

namespace Tengoku.QuadraticNumberFields.QuadraticField

/-- The ring of integers of an abstract quadratic field is a quadratic extension
of `ℤ`.
@isnad1 id=isquadra.0h1v.s5.f3ed0915458c from=translated src=- shape=eea2e7a7 vocab=5496e926
-/
instance ringOfIntegers_isQuadraticExtension
    (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K] :
    Algebra.IsQuadraticExtension ℤ (𝓞 K) :=
  @Algebra.IsQuadraticExtension.mk ℤ _ _ _ _ _
    (inferInstance : Module.Free ℤ (𝓞 K))
    ((NumberField.RingOfIntegers.rank K).trans (by
      convert Algebra.IsQuadraticExtension.finrank_eq_two ℚ K using 1
      congr 1
      exact Subsingleton.elim _ _))

end Tengoku.QuadraticNumberFields.QuadraticField
-- Tengoku: root names of this library moved to Tengoku.QuadraticNumberFields so they do not collide with other libraries (generated)
