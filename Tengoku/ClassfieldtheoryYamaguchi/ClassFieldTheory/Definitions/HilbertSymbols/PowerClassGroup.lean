/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Algebra.Field.Basic
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Multiplicative power-class groups
-/

namespace ClassFieldTheory

universe u

/-- The multiplicative group of a field modulo its `n`-th powers.-/
def PowerClassGroup (K : Type u) [Field K] (n : ℕ+) : Type u :=
  Kˣ ⧸ (powMonoidHom (n : ℕ) : Kˣ →* Kˣ).range

instance instCommGroupPowerClassGroup
    (K : Type u) [Field K] (n : ℕ+) : CommGroup (PowerClassGroup K n) := by
  unfold PowerClassGroup
  infer_instance

end ClassFieldTheory
