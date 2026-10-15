/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.OmegaHom
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic

/-!
# LeanPool.QuasiBorelSpaces.Cont

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Cont`.
-/

@[expose] public section

open QuasiBorelSpace
open OmegaCompletePartialOrder

namespace OmegaQuasiBorelSpace

/-- The continuation monad in the category of `OmegaQuasiBorelSpace`s. -/
structure Cont (R A : Type*) [OmegaQuasiBorelSpace R] [OmegaQuasiBorelSpace A] where
  /-- The underlying morphism. -/
  apply : (A →ω𝒒 R) →ω𝒒 R

namespace Cont

variable {R A B : Type*} [OmegaQuasiBorelSpace R] [OmegaQuasiBorelSpace A]

/--
@isnad1 id=eq.1h4v.s5.9064f9f58a09 from=translated src=- shape=b28f9e64 vocab=5470313d
-/
@[ext]
lemma ext {x y : Cont R A} (h : x.apply = y.apply) : x = y := by
  cases x
  simp_all

instance : PartialOrder (Cont R A) :=
  PartialOrder.lift apply (by
    rintro ⟨x⟩ ⟨y⟩
    simp only [mk.injEq, imp_self])

/-- The underlying continuation as an order homomorphism. -/
def applyOrderHom : Cont R A →o ((A →ω𝒒 R) →ω𝒒 R) where
  toFun := apply
  monotone' _ _ h := h

instance : OmegaCompletePartialOrder (Cont R A) := by
  refine OmegaCompletePartialOrder.lift applyOrderHom
    (fun c ↦ ⟨ωSup (c.map applyOrderHom)⟩) ?_ ?_
  · intro ⟨x⟩ ⟨y⟩
    exact id
  · intro c
    rfl

instance : QuasiBorelSpace (Cont R A) :=
  QuasiBorelSpace.lift apply

/--
@isnad1 id=ishom.0h2v.s5.730551c579f0 from=translated src=- shape=d1c0322c vocab=243dd151
-/
@[local fun_prop]
lemma isHom_val : IsHom (apply (R := R) (A := A)) := by
  rw [← isHom_to_lift]
  simp only [isHom_id']

/--
@isnad1 id=ishom.1h4v.s6.7444e0944dda from=translated src=- shape=c62f77a0 vocab=1582c845
-/
@[fun_prop]
lemma isHom_val'
    [QuasiBorelSpace B] {f : B → Cont R A} (hf : IsHom f)
    : IsHom (fun x ↦ (f x).apply) := by
  fun_prop

/--
@isnad1 id=ishom.0h2v.s5.17b43a4da911 from=translated src=- shape=2e088bf8 vocab=7b3c844c
-/
@[simp, local fun_prop]
lemma isHom_mk : IsHom (mk (R := R) (A := A)) := by
  apply isHom_of_lift

/--
@isnad1 id=ishom.1h4v.s6.0a23cbd28313 from=translated src=- shape=2f498ad6 vocab=622889cf
-/
@[fun_prop]
lemma isHom_mk'
    [QuasiBorelSpace B] {f : B → (A →ω𝒒 R) →ω𝒒 R} (hf : IsHom f)
    : IsHom (fun x ↦ mk (f x)) := by
  fun_prop

/--
@isnad1 id=scottcon.0h2v.s5.74332c6b8611 from=translated src=- shape=2e088bf8 vocab=644e4e1b
-/
@[simp, local fun_prop]
lemma ωScottContinuous_mk : ωScottContinuous (mk (R := R) (A := A)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y h k ↦ ?_, fun c ↦ ?_⟩
  · apply h
  · rfl

/--
@isnad1 id=scottcon.1h4v.s6.647cb3378352 from=translated src=- shape=2f498ad6 vocab=d44c3824
-/
@[fun_prop]
lemma ωScottContinuous_mk'
     [OmegaCompletePartialOrder B] {f : B → (A →ω𝒒 R) →ω𝒒 R} (hf : ωScottContinuous f)
     : ωScottContinuous (fun x ↦ mk (f x)) := by
  fun_prop

/--
@isnad1 id=scottcon.0h2v.s5.647c6af21106 from=translated src=- shape=d1c0322c vocab=0be7ecc2
-/
@[simp, local fun_prop]
lemma ωScottContinuous_val : ωScottContinuous (apply (R := R) (A := A)) := by
  rw [ωScottContinuous_iff_monotone_map_ωSup]
  refine ⟨fun x y h k ↦ ?_, fun c ↦ ?_⟩
  · apply h
  · rfl

/--
@isnad1 id=scottcon.1h4v.s6.0e534d768cb1 from=translated src=- shape=c62f77a0 vocab=9232b771
-/
@[fun_prop]
lemma ωScottContinuous_val'
    [OmegaCompletePartialOrder B] {f : B → Cont R A} (hf : ωScottContinuous f)
    : ωScottContinuous (fun x ↦ (f x).apply) := by
  fun_prop

instance : OmegaQuasiBorelSpace (Cont R A) where
  isHom_ωSup := by
    change IsHom fun x ↦ mk _
    apply isHom_comp' isHom_mk
    apply isHom_ωSup'
    simp only [
      Chain.isHom_iff, Chain.coe_map, Function.comp_apply, OmegaQuasiBorelHom.isHom_iff]
    intro i
    apply isHom_comp'
        (f := fun x : Cont R A × _ ↦ x.1.apply x.2)
        (g := fun x : Chain (Cont R A) × _ ↦ (x.1 i, x.2))
        (by fun_prop)
    apply Prod.isHom_mk
    · apply isHom_comp' (Chain.isHom_apply i) Prod.isHom_fst
    · apply Prod.isHom_snd

/-- The `unit` operator (i.e., pure values) for the continuation monad. -/
@[simps]
def unit : A →ω𝒒 Cont R A where
  toFun x := ⟨{ toFun k := k x }⟩

/-- The `bind` operator (i.e., sequential composition) for the continuation monad. -/
@[simps]
def bind [OmegaQuasiBorelSpace B] : (A →ω𝒒 Cont R B) →ω𝒒 (Cont R A →ω𝒒 Cont R B) where
  toFun f := { toFun x := ⟨{ toFun k := x.apply { toFun y := (f y).apply k } }⟩ }

/--
@isnad1 id=eq.0h5v.s8.34e266263232 from=translated src=- shape=d2497c19 vocab=c6c82ef5
-/
@[simp]
lemma bind_unit [OmegaQuasiBorelSpace B] (f : A →ω𝒒 Cont R B) (x : A) : bind f (unit x) = f x := rfl

/--
@isnad1 id=eq.0h2v.s7.e0ce24eb0a05 from=translated src=- shape=46f9ef29 vocab=0b8b8e82
-/
@[simp]
lemma unit_bind : bind (unit (R := R) (A := A)) = .id := rfl

/--
@isnad1 id=eq.0h6v.s9.13523ebbf2cf from=translated src=- shape=5d8dd11b vocab=cf456de9
-/
@[simp]
lemma bind_bind {C : Type*}
    [OmegaQuasiBorelSpace B] [OmegaQuasiBorelSpace C]
    (f : B →ω𝒒 Cont R C) (g : A →ω𝒒 Cont R B)
    : (bind f).comp (bind g) = bind ((bind f).comp g) :=
  rfl

end Cont

end OmegaQuasiBorelSpace
