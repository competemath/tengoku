/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.ClassfieldtheoryYamaguchi.ClassFieldTheory.Definitions.LocalClassFieldTheory.FieldNormSubgroup
import Tengoku.Seed.RingTheory.Norm.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Transport of finite-extension norm subgroups

Compatible field equivalences carry the actual group of field norms to the
actual group of field norms.  This is the norm comparison needed when finite
local class-field theory is transported to a small representative.
-/

noncomputable section

namespace ClassFieldTheory

universe u v w x

variable {F : Type u} {M : Type v} {F' : Type w} {M' : Type x}
  [Field F] [Field M] [Field F'] [Field M']
  [Algebra F M] [Algebra F' M']
  [FiniteDimensional F M] [FiniteDimensional F' M']

/-- The field-norm homomorphisms commute with compatible field equivalences.
@isnad1 id=eq.1h7v.s10.219d20e1d2d0 from=translated src=- shape=d5030ab2 vocab=54ae80ef
-/
theorem fieldNormHom_map_ringEquiv
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he : (algebraMap F' M').comp eF.toRingHom =
      eM.toRingHom.comp (algebraMap F M))
    (y : Mˣ) :
    (Units.mapEquiv eF.toMulEquiv) (fieldNormHom F M y) =
      fieldNormHom F' M' (Units.mapEquiv eM.toMulEquiv y) := by
  apply Units.ext
  change eF (Algebra.norm F (y : M)) =
    Algebra.norm F' (eM (y : M))
  rw [Algebra.norm_eq_of_equiv_equiv eF eM he]
  exact eF.apply_symm_apply _

/-- The image of a field-norm subgroup under a base-field equivalence is
exactly the norm subgroup of the transported extension.
@isnad1 id=eq.1h6v.s9.0eb1f2f6a610 from=translated src=- shape=225725fb vocab=668e1e8b
-/
theorem fieldNormSubgroup_map_ringEquiv
    (eF : F ≃+* F') (eM : M ≃+* M')
    (he : (algebraMap F' M').comp eF.toRingHom =
      eM.toRingHom.comp (algebraMap F M)) :
    (fieldNormSubgroup F M).map
        (Units.mapEquiv eF.toMulEquiv).toMonoidHom =
      fieldNormSubgroup F' M' := by
  ext z
  constructor
  · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨Units.mapEquiv eM.toMulEquiv x,
      (fieldNormHom_map_ringEquiv eF eM he x).symm⟩
  · rintro ⟨x, rfl⟩
    let y := (Units.mapEquiv eM.toMulEquiv).symm x
    refine ⟨fieldNormHom F M y, ⟨y, rfl⟩, ?_⟩
    change (Units.mapEquiv eF.toMulEquiv) (fieldNormHom F M y) =
      fieldNormHom F' M' x
    simpa only [y, MulEquiv.apply_symm_apply] using
      fieldNormHom_map_ringEquiv eF eM he y

end ClassFieldTheory
