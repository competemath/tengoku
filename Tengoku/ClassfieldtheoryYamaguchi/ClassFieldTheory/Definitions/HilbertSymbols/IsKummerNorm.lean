/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.HilbertSymbols.KummerAlgebra
import Tengoku.Seed.RingTheory.Norm.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Norms from Kummer algebras
-/

namespace ClassFieldTheory

universe u

/-- A nonzero element `b` is a norm from the Kummer algebra
`K[X] / (X^n - a)`.-/
def IsKummerNorm
    (K : Type u) [Field K] (n : ℕ+) (a b : Kˣ) : Prop :=
  ∃ y : (KummerAlgebra K n a)ˣ,
    Algebra.norm K (y : KummerAlgebra K n a) = (b : K)

end ClassFieldTheory
