/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# The field-norm quotient
-/

noncomputable section

namespace ClassFieldTheory

universe u v

/-- The norm quotient `Kˣ / N_{L/K}(Lˣ)`.-/
abbrev FieldNormQuotient
    (K : Type u) (L : Type v)
    [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :=
  Kˣ ⧸ fieldNormSubgroup K L

end ClassFieldTheory
