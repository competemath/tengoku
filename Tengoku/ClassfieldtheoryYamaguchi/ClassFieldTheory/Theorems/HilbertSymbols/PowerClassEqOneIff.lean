/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.HilbertSymbols.PowerClass

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Power-class laws and representatives

For a field `K` and a positive integer `n`, `PowerClassGroup K n` is the
quotient of `Kˣ` by the subgroup of `n`-th powers. A class is the identity
exactly when its representative belongs to the power subgroup.
-/

namespace ClassFieldTheory

universe u

/-- A power class is trivial exactly when its representative is an `n`-th
power.
@isnad1 id=iff.0h3v.s8.242d932feb3a from=translated src=- shape=642b9994 vocab=5905590d
-/
@[simp]
theorem powerClass_eq_one_iff
    (K : Type u) [Field K] (n : ℕ+) (a : Kˣ) :
    powerClass K n a = 1 ↔
      a ∈ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range := by
  exact QuotientGroup.eq_one_iff a

end ClassFieldTheory
