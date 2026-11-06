/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.RingTheory.Norm.Transitivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Field norms on unit groups

This file provides the common algebraic norm map on unit groups.  It is
independent of any valuation or local-field structure, so valued-field and
discrete-valuation APIs can share the same definition.
-/

namespace LocalFieldTheory

noncomputable section

universe u v w

variable (K : Type u) (L : Type v)
variable [Field K] [Field L] [Algebra K L]

/-- Negation contributes one sign for each basis vector in the field norm.
@isnad1 id=eq.0h3v.s8.e29cbe154476 from=translated src=- shape=93dbf839 vocab=6d9b70d1
-/
theorem algebraNorm_neg (x : L) :
    Algebra.norm K (-x) = (-1) ^ Module.finrank K L * Algebra.norm K x := by
  rw [show -x = algebraMap K L (-1) * x by rw [map_neg, map_one, neg_one_mul],
    map_mul, Algebra.norm_algebraMap]

/-- The algebra norm, restricted to unit groups.-/
def normUnits : Lˣ →* Kˣ :=
  Units.map (Algebra.norm K)

/-- The underlying field element of a unit norm is the algebra norm.
@isnad1 id=eq.0h3v.s8.6e67f508fa7a from=translated src=- shape=46e43cb5 vocab=d42ef629
-/
@[simp]
theorem normUnits_apply_coe (x : Lˣ) :
    ((normUnits K L x : Kˣ) : K) = Algebra.norm K (x : L) :=
  rfl

end

end LocalFieldTheory
