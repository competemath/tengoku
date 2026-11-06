/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Algebra.Basic
import Tengoku
import Tengoku.Seed.Topology.UniformSpace.AbsoluteValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Extensions of absolute values

A reusable predicate for exact extension along an algebra map.
-/

namespace AbsoluteValue
/-- The target absolute value agrees with the base absolute value along the algebra map.-/
def Extends {K L : Type*} [Field K] [Field L] [Algebra K L]
    (v : AbsoluteValue K ℝ) (w : AbsoluteValue L ℝ) : Prop :=
  ∀ x : K, w (algebraMap K L x) = v x

end AbsoluteValue
