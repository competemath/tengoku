/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Subtype
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Basic
import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Prod

/-!
# LeanPool.QuasiBorelSpaces.Prop

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Prop`.
-/

@[expose] public section

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {I : Sort*} [Countable I]

namespace QuasiBorelSpace.Prop

/--
@isnad1 id=ishom.3h7v.s6.4360e546646d from=translated src=- shape=807058b4 vocab=88d4a471
-/
@[fun_prop]
lemma isHom_ite
    {p : A → Prop} (hp : IsHom p) [inst : DecidablePred p]
    {f : A → B} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (fun x ↦ if p x then f x else g x) := by
  classical
  have (x : A) : inst x = Classical.dec _ := by subsingleton
  conv => enter [1, x]; rw [this]
  apply isHom_cases (f := fun b x ↦ if b then f x else g x) hp
  intro
  split_ifs <;> assumption

/--
@isnad1 id=ishom.1h3v.s4.47f1ff128182 from=translated src=- shape=5cdf6ada vocab=3fa53d2d
-/
@[fun_prop]
lemma isHom_not
    {f : A → Prop} (hf : IsHom f)
    : IsHom (fun x ↦ ¬f x) := by
  fun_prop

/--
@isnad1 id=ishom.2h4v.s5.73ae2822e2b5 from=translated src=- shape=091efe82 vocab=3fa53d2d
-/
@[fun_prop]
lemma isHom_and
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ∧ g x) := by
  fun_prop

/--
@isnad1 id=ishom.2h4v.s5.9815a87f379e from=translated src=- shape=091efe82 vocab=3fa53d2d
-/
@[fun_prop]
lemma isHom_or
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ∨ g x) := by
  fun_prop

/--
@isnad1 id=ishom.2h4v.s5.ecee1b52e28d from=translated src=- shape=5c323d91 vocab=3fa53d2d
-/
lemma isHom_imp
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x → g x) := by
  exact isHom_comp' (f := fun x ↦ x.1 → x.2) (g := fun x ↦ (f x, g x))
    (by simp only [isHom_of_discrete_countable]) (by fun_prop)

/--
@isnad1 id=ishom.2h4v.s5.72bb979d43cd from=translated src=- shape=091efe82 vocab=3fa53d2d
-/
@[fun_prop]
lemma isHom_iff
    {f g : A → Prop} (hf : IsHom f) (hg : IsHom g)
    : IsHom (fun x ↦ f x ↔ g x) := by
  fun_prop

/--
@isnad1 id=ishom.1h4v.s5.270d23d69bc8 from=translated src=- shape=fdbe6055 vocab=4c4abed3
-/
lemma isHom_forall
    {f : I → A → Prop} (hf : ∀ i, IsHom (f i))
    : IsHom (fun x ↦ ∀i, f i x) := by
  rw [isHom_def]
  intro φ hφ
  simp only [isHom_ofMeasurableSpace]
  apply Measurable.forall
  intro i
  rw [←isHom_iff_measurable]
  fun_prop

/--
@isnad1 id=ishom.1h4v.s5.3fe064c756f6 from=translated src=- shape=c8106cd7 vocab=4c4abed3
-/
@[fun_prop]
lemma isHom_exists
    {f : I → A → Prop} (hf : ∀ i, IsHom (f i))
    : IsHom (fun x ↦ ∃i, f i x) := by
  rw [isHom_def]
  intro φ hφ
  simp only [isHom_ofMeasurableSpace]
  apply Measurable.exists
  intro i
  rw [←isHom_iff_measurable]
  fun_prop

/--
@isnad1 id=ishom.3h7v.s7.c9851cdd601e from=translated src=- shape=4400b416 vocab=5c9f76f1
-/
@[fun_prop]
lemma isHom_dite
    {p : A → Prop} (hp : IsHom p) [inst : DecidablePred p]
    {f : (x : A) → p x → B} (hf : IsHom fun x : Subtype p ↦ f x.val x.property)
    {g : (x : A) → ¬p x → B} (hg : IsHom fun x : Subtype (fun x ↦ ¬p x) ↦ g x.val x.property)
    : IsHom (fun x ↦ if h : p x then f x h else g x h) := by
  classical
  have : inst = fun x ↦ Classical.dec _ := by subsingleton
  subst this
  wlog hp : Nonempty (Subtype p)
  · simp only [nonempty_subtype, not_exists] at hp
    simp only [hp, ↓reduceDIte]
    have : IsHom fun x : A ↦ (⟨x, hp x⟩ : Subtype fun x ↦ ¬p x) := by fun_prop
    apply isHom_comp' hg this
  wlog hnp : Nonempty (Subtype fun x ↦ ¬p x)
  · simp only [nonempty_subtype, not_exists, Decidable.not_not] at hnp
    simp only [hnp, ↓reduceDIte]
    have : IsHom fun x : A ↦ (⟨x, hnp x⟩ : Subtype p) := by fun_prop
    apply isHom_comp' hf this
  let f' := fun x : Subtype p ↦ f x.val x.property
  let g' := fun x : Subtype (fun x ↦ ¬p x) ↦ g x.val x.property
  let k q x :=
      if q
      then f' (if h : p x then ⟨x, h⟩ else Classical.arbitrary _)
      else g' (if h : ¬p x then ⟨x, h⟩ else Classical.arbitrary _)
  have {x}
      : (if h : p x then f x h else g x h)
      = if p x
        then f' (if h :  p x then ⟨x, h⟩ else Classical.arbitrary _)
        else g' (if h : ¬p x then ⟨x, h⟩ else Classical.arbitrary _) := by
    grind
  simp only [this]
  apply isHom_ite
  · fun_prop
  · apply isHom_comp' hf
    simp only [Subtype.isHom_def, apply_dite, dite_eq_ite]
    apply isHom_ite <;> fun_prop
  · apply isHom_comp' hg
    simp only [Subtype.isHom_def, apply_dite, dite_eq_ite]
    apply isHom_ite <;> fun_prop

/--
@isnad1 id=ishom.1h3v.s5.497d96f45795 from=translated src=- shape=cf454921 vocab=6f4f9a61
-/
@[fun_prop]
lemma isHom_decide
    {p : A → Prop} [inst : DecidablePred p] (hp : IsHom p)
    : IsHom (fun x ↦ decide (p x)) := by
  classical
  have : inst = fun x ↦ Classical.dec (p x) := by subsingleton
  subst this
  apply isHom_cases (f := fun p _ ↦ decide p) <;> fun_prop

end QuasiBorelSpace.Prop
