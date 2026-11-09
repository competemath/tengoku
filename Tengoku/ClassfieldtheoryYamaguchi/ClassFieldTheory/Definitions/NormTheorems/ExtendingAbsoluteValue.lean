/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Algebra.Basic
import Tengoku
import Tengoku.Seed.Topology.UniformSpace.AbsoluteValue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Absolute values above a fixed absolute value

This index type uses only Mathlib's absolute values and algebra map.  Its
elements are precisely the absolute values on `L` extending `v` on `K`.
-/

namespace ClassFieldTheory

universe u v

/-- An absolute value on `L` whose restriction along `K → L` is `v`.-/
abbrev ExtendingAbsoluteValue
    {K : Type u} [Field K] (v : AbsoluteValue K ℝ)
    (L : Type v) [Field L] [Algebra K L] :=
  { w : AbsoluteValue L ℝ // ∀ a : K, w (algebraMap K L a) = v a }

end ClassFieldTheory
