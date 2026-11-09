/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import Tengoku.Seed.FieldTheory.Galois.Abelian
import Tengoku.Seed.FieldTheory.IsSepClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Finite abelian local extensions
-/

noncomputable section

namespace ClassFieldTheory

universe u

/-- A finite abelian extension of `K` inside Mathlib's chosen separable
closure.  The inherited order is field inclusion.-/
abbrev FiniteAbelianLocalExtension
    (K : Type u) [Field K] :=
  { E : IntermediateField K (SeparableClosure K) //
      FiniteDimensional K E ∧ IsAbelianGalois K E }

namespace FiniteAbelianLocalExtension

variable {K : Type u} [Field K]

/-- The packaged intermediate field is finite-dimensional over the base.
@isnad1 id=finitedi.0h2v.s14.32bcfce161e8 from=translated src=- shape=19d111fd vocab=a6b137cc
-/
instance finiteDimensional (E : FiniteAbelianLocalExtension K) :
    FiniteDimensional K E.1 :=
  E.2.1

/-- The packaged intermediate field is abelian Galois over the base.
@isnad1 id=isabelia.0h2v.s13.0d9fa9be5a85 from=translated src=- shape=c1dba889 vocab=a6b137cc
-/
instance isAbelianGalois (E : FiniteAbelianLocalExtension K) :
    IsAbelianGalois K E.1 :=
  E.2.2

/-- The norm subgroup belonging to a packaged finite abelian extension.-/
def normSubgroup (E : FiniteAbelianLocalExtension K) : Subgroup Kˣ :=
  fieldNormSubgroup K E.1

end FiniteAbelianLocalExtension

end ClassFieldTheory
