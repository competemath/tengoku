/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.IsHomDiagonal
public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Option
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Nat
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Prop

/-!
# LeanPool.QuasiBorelSpaces.Option

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Option`.
-/

@[expose] public section

namespace QuasiBorelSpace.Option

variable {A B C : Type*} [QuasiBorelSpace A] [QuasiBorelSpace B] [QuasiBorelSpace C]

/--
We derive the `QuasiBorelSpace` instance for `Option A`s from their encoding as
`Unit ⊕ A`.
-/
abbrev Encoding (A : Type*) := Unit ⊕ A

namespace Encoding

/-- The encoded version of `Option.none`. -/
def none : Encoding A := .inl ()

/-- The encoded version of `Option.some`. -/
def some (x : A) : Encoding A := .inr x

/-- The encoded version of `Option.elim`. -/
def elim (x : B) (f : A → B) : Encoding A → B :=
  Sum.elim (fun _ ↦ x) f

/--
@isnad1 id=ishom.0h1v.s4.b63d47d40250 from=translated src=- shape=a638af76 vocab=53128768
-/
@[fun_prop, simp]
lemma isHom_some : IsHom (some (A := A)) := by
  unfold some
  fun_prop

/--
@isnad1 id=ishom.3h6v.s6.5b5e6bd3355a from=translated src=- shape=902a8033 vocab=4e9266ab
-/
@[fun_prop]
lemma isHom_elim
    {f : A → C} (hf : IsHom f)
    {g : A → B → C} (hg : IsHom fun (x, y) ↦ g x y)
    {h : A → Encoding B} (hh : IsHom h)
    : IsHom (fun x ↦ elim (f x) (g x) (h x)) := by
  unfold elim
  fun_prop

end Encoding

/-- Encodes an `Option A` as an `Encoding A`. -/
def encode (x : Option A) : Unit ⊕ A :=
  Option.elim x Encoding.none Encoding.some

instance : QuasiBorelSpace (Option A) := lift encode

/--
@isnad1 id=ishom.0h1v.s4.8312844111a8 from=translated src=- shape=133a3ae8 vocab=90414285
-/
@[fun_prop, simp]
lemma isHom_encode : IsHom (encode (A := A)) := by
  apply isHom_of_lift

/--
@isnad1 id=ishom.1h3v.s5.491cfe9b7d2c from=translated src=- shape=3ee43307 vocab=0e5cd967
-/
@[fun_prop]
lemma isHom_some {f : A → B} (hf : IsHom f) : IsHom (fun x ↦ some (f x)) := by
  simp only [isHom_to_lift (A := Option _), encode, Option.elim_some]
  fun_prop

/--
@isnad1 id=ishom.3h6v.s6.01afdbfea2a3 from=translated src=- shape=b81edfa7 vocab=0f3d1945
-/
@[fun_prop]
lemma isHom_elim
    {f : A → Option B} (hf : IsHom f)
    {g : A → C} (hg : IsHom g)
    {h : A → B → C} (hh : IsHom fun (x, y) ↦ h x y)
    : IsHom (fun x ↦ Option.elim (f x) (g x) (h x)) := by
  have {x}
      : Option.elim (f x) (g x) (h x)
      = Encoding.elim (g x) (h x) (encode (f x)) := by
    cases f x <;> rfl
  simp only [this]
  fun_prop

/--
@isnad1 id=ishom.2h5v.s6.cd7734fbebbf from=translated src=- shape=ffdda966 vocab=dda1f21a
-/
@[fun_prop]
lemma isHom_map
    {f : A → B → C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : IsHom g)
    : IsHom (fun x ↦ Option.map (f x) (g x)) := by
  have {x} : Option.map (f x) (g x) = Option.elim (g x) .none (.some ∘ f x) := by
    cases g x <;> rfl
  simp only [this]
  fun_prop

/--
@isnad1 id=ishom.2h5v.s6.68e67b819946 from=translated src=- shape=cc26decf vocab=d83fec1e
-/
@[fun_prop]
lemma isHom_bind
    {f : A → B → Option C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : IsHom g)
    : IsHom (fun x ↦ Option.bind (g x) (f x)) := by
  have {x} : Option.bind (g x) (f x) = Option.elim (g x) .none (f x) := by
    cases g x <;> rfl
  simp only [this]
  fun_prop

/--
@isnad1 id=ishom.2h5v.s6.5af2a51a6801 from=translated src=- shape=b4b80235 vocab=5614b510
-/
@[fun_prop]
lemma isHom_bind'
    {C : Type _} [QuasiBorelSpace C]
    {f : A → B → Option C} (hf : IsHom fun (x, y) ↦ f x y)
    {g : A → Option B} (hg : IsHom g)
    : IsHom (fun x ↦ g x >>= f x) := by
  simp only [Option.bind_eq_bind]
  fun_prop

/--
@isnad1 id=ishom.2h4v.s5.8c3d0edc7b8c from=translated src=- shape=e9639cd7 vocab=0e42fb79
-/
@[fun_prop]
lemma isHom_getD
    {f : A → Option B} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (fun x ↦ (f x).getD (g x)) := by
  have {x} : Option.getD (f x) (g x) = Option.elim (f x) (g x) id := by
    cases f x <;> rfl
  simp only [this]
  fun_prop

/--
@isnad1 id=ishom.0h1v.s4.938016b9a5ba from=translated src=- shape=fcf3b915 vocab=d71a79e2
-/
@[simp, fun_prop]
lemma isHom_isSome : IsHom (fun x : Option A ↦ x.isSome) := by
  have (x : Option A) : x.isSome = x.elim false (fun _ ↦ true) := by
    cases x <;> rfl
  simp only [this]
  fun_prop

/--
@isnad1 id=ishom.0h1v.s4.725980520150 from=translated src=- shape=fcf3b915 vocab=d4e85aaf
-/
@[simp, fun_prop]
lemma isHom_isNone : IsHom (fun x : Option A ↦ x.isNone) := by
  have (x : Option A) : x.isNone = x.elim true (fun _ ↦ false) := by
    cases x <;> rfl
  simp only [this]
  fun_prop

end QuasiBorelSpace.Option

namespace OmegaQuasiBorelSpace.Option

open QuasiBorelSpace
open OmegaCompletePartialOrder

variable {A B : Type*}

/--
@isnad1 id=ishom.2h3v.s6.637aec66754b from=translated src=- shape=341a1154 vocab=65a9b022
-/
@[fun_prop]
lemma isHom_project
    [QuasiBorelSpace A] [QuasiBorelSpace B] [Preorder B]
    {f : A → Chain (Option B)} (hf : IsHom f)
    (g : ∀ x, ∃ n, (f x n).isSome)
    : IsHom (fun x ↦ Chain.Option.project (f x) (g x)) := by
  simp only [Chain.isHom_iff, Chain.Option.project_coe]
  intro i
  apply Option.isHom_getD
  · apply isHom_cases (f := fun n x ↦ f x n)
    · apply Nat.isHom_add'
      · apply Nat.isHom_find fun n ↦ ?_
        apply isHom_eq'
        · exact isHom_comp' Option.isHom_isSome (isHom_comp' (Chain.isHom_apply n) hf)
        · fun_prop
      · fun_prop
    · simp_all
  · fun_prop

/--
@isnad1 id=ishom.0h1v.s5.779fb7dfab18 from=translated src=- shape=0bfaef8a vocab=2dc607f7
-/
@[fun_prop]
lemma isHom_distrib [QuasiBorelSpace A] [Preorder A] : IsHom (Chain.Option.distrib (A := A)) := by
  classical
  rw [isHom_def]
  intro φ hφ
  simp only [Chain.Option.distrib]
  apply Prop.isHom_dite
  · apply Prop.isHom_exists fun i ↦ ?_
    apply isHom_eq'
    · exact isHom_comp' Option.isHom_isSome (isHom_comp' (Chain.isHom_apply i) hφ)
    · fun_prop
  · fun_prop
  · fun_prop

noncomputable instance [OmegaQuasiBorelSpace A] : OmegaQuasiBorelSpace (Option A) where
  isHom_ωSup := by
    change IsHom fun r ↦ ωSup _
    simp only [ωSup]
    fun_prop

end OmegaQuasiBorelSpace.Option
