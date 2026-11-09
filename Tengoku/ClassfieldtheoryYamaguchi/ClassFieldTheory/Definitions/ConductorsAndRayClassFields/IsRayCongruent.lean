/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayClassModulus
import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.ConductorsAndRayClassFields.RayLocalHigherUnitGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Ray congruences
-/

open scoped NumberField
open NumberField IsDedekindDomain

noncomputable section

namespace ClassFieldTheory

universe u

/-- The diagonal embedding of field units into a finite completion.-/
def finitePlaceUnitEmbedding
    {K : Type u} [Field K] [NumberField K]
    (v : HeightOneSpectrum (𝓞 K)) :
    Kˣ →* (v.adicCompletion K)ˣ :=
  Units.map (algebraMap K (v.adicCompletion K)).toMonoidHom

/-- A field unit satisfies the finite congruences and real positivity
conditions specified by a ray modulus.-/
def IsRayCongruent
    {K : Type u} [Field K] [NumberField K]
    (m : RayClassModulus K) (x : Kˣ) : Prop :=
  (∀ v, v ∈ m.finitePart.support →
      finitePlaceUnitEmbedding v x ∈
        rayLocalHigherUnitGroup v (m.finitePart v)) ∧
    (∀ v, v ∈ m.infinitePart →
      0 < v.1.embedding_of_isReal v.2 (x : K))

namespace IsRayCongruent

end IsRayCongruent

end ClassFieldTheory
