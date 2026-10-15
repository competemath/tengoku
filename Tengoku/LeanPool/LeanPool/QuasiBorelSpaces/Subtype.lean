/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.OmegaQuasiBorelSpace
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic

/-!
# LeanPool.QuasiBorelSpaces.Subtype

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Subtype`.
-/

@[expose] public section

namespace QuasiBorelSpace.Subtype

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {P : A → Prop}

instance [QuasiBorelSpace A] : QuasiBorelSpace (Subtype P) := lift Subtype.val

/--
@isnad1 id=iff.0h6v.s5.9b06d2db43e0 from=translated src=- shape=39753427 vocab=fd426cc3
-/
@[simp]
lemma isHom_def {P : B → Prop} (f : A → Subtype P) : IsHom f ↔ IsHom fun x ↦ (f x).val := by
  rw [isHom_to_lift]

/--
@isnad1 id=ishom.1h7v.s5.e9a4c6883cf5 from=translated src=- shape=134bc2bc vocab=44d3fbc4
-/
@[fun_prop]
lemma isHom_mk {P : B → Prop}
    {f : A → B} (hf₁ : IsHom f) (hf₂ : (x : A) → P (f x))
    : IsHom (fun x ↦ Subtype.mk (f x) (hf₂ x)) := by
  simp_all

/--
@isnad1 id=ishom.1h6v.s5.d6e476e4e790 from=translated src=- shape=dd1468ec vocab=fd426cc3
-/
@[fun_prop]
lemma isHom_val {P : B → Prop} {f : A → Subtype P} (hf : IsHom f) : IsHom (fun x ↦ (f x).val) := by
  rwa [← isHom_def]

end QuasiBorelSpace.Subtype

namespace OmegaQuasiBorelSpace.Subtype

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable
  {I : Type*} {P : I → Prop} [OmegaQuasiBorelSpace I]
  (hP : ∀ (c : OmegaCompletePartialOrder.Chain I),
    (∀ i ∈ c, P i) → P (OmegaCompletePartialOrder.ωSup c))

/-- Constructs an `OmegaQuasiBorelSpace` instance for a `Subtype`. -/
@[reducible] def subtype : OmegaQuasiBorelSpace (Subtype P) where
  toOmegaCompletePartialOrder := OmegaCompletePartialOrder.subtype P hP
  isHom_ωSup := by
    simp only [ωSup, Subtype.isHom_def]
    apply isHom_comp
    · fun_prop
    · simp only [Chain.isHom_iff, Chain.coe_map, OrderHom.Subtype.val_coe, Function.comp_apply]
      fun_prop

end OmegaQuasiBorelSpace.Subtype
