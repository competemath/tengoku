/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import Tengoku.Seed.RingTheory.Norm.Transitivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Norm subgroups in a tower

The norm from a larger field factors through the norm from every intermediate
field. Thus enlarging a finite extension can only shrink its subgroup of
norms in the base field. No local-field or Galois assumption is needed.
-/

noncomputable section

namespace ClassFieldTheory

universe u v w

/-- In a finite tower `K ⊆ M ⊆ L`, every norm from `L` to `K` is a norm
from `M` to `K`.
@isnad1 id=le.0h3v.s8.c4c8c99ea5c4 from=translated src=- shape=e57e095f vocab=ebff22d9
-/
theorem fieldNormSubgroup_le_of_tower
    (K : Type u) (M : Type v) (L : Type w)
    [Field K] [Field M] [Field L]
    [Algebra K M] [Algebra M L] [Algebra K L]
    [IsScalarTower K M L]
    [FiniteDimensional K M] [FiniteDimensional M L] [FiniteDimensional K L] :
    fieldNormSubgroup K L ≤ fieldNormSubgroup K M := by
  rintro x ⟨y, rfl⟩
  refine ⟨fieldNormHom M L y, ?_⟩
  apply Units.ext
  exact Algebra.norm_norm

end ClassFieldTheory
