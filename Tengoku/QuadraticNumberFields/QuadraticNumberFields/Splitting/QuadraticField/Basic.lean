/-
Copyright (c) 2026 Frankie Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frankie Wang
-/
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.QuadraticField.Classification
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.QuadraticField.RingOfIntegers
import Tengoku.QuadraticNumberFields.QuadraticNumberFields.Splitting.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Abstract Prime-Splitting Interface for Quadratic Fields

This file gives the first abstract-field wrappers around the splitting API.
The explicit Legendre-symbol computations remain in
`QuadraticNumberFields.Splitting.Qsqrtd.Classification`; the results here expose the
same splitting conditions for an arbitrary `[QuadraticField K]`, stated directly
with mathlib's ramification API.

This module is part of the work-in-progress `Sketch` surface while the full
Legendre-symbol classification is still incomplete.
-/

local notation "ℚ√" d => Qsqrtd d

open scoped NumberField
open Ideal

-- Resolve the diamond between `DivisionRing.toRatAlgebra` and the explicit `Algebra ℚ K`.
-- NOTE: This is a file-local workaround matching the abstract quadratic-field surface.
attribute [-instance] DivisionRing.toRatAlgebra

namespace QuadraticNumberFields
namespace Splitting

section AbstractField

variable (K : Type*) [Field K] [Algebra ℚ K] [QuadraticField K]

/-- The rational prime `p` splits in the ring of integers of `K`.-/
def IsSplitAt (K : Type*) [Field K] (p : ℕ) : Prop :=
  IsSplitIn (𝔭(p)) (𝓞 K)

/-- The rational prime `p` is inert in the ring of integers of `K`.-/
def IsInertAt (K : Type*) [Field K] (p : ℕ) : Prop :=
  IsInertIn (𝔭(p)) (𝓞 K)

/-- The rational prime `p` ramifies in the ring of integers of `K`.-/
def IsRamifiedAt (K : Type*) [Field K] (p : ℕ) : Prop :=
  IsRamifiedIn (𝔭(p)) (𝓞 K)

end AbstractField

end Splitting
end QuadraticNumberFields
