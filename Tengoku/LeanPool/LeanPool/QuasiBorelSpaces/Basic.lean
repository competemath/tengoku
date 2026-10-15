/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.Defs
public import Tengoku.LeanPool.LeanPool.QuasiBorelSpaces.MeasureTheory.Pack

/-!
# LeanPool.QuasiBorelSpaces.Basic

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.Basic`.
-/

@[expose] public section

open scoped MeasureTheory

namespace QuasiBorelSpace

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {C : Type*} {_ : QuasiBorelSpace C}
  {I : Type*} [Countable I]

/--
@isnad1 id=isvar.2h5v.s6.9ca63fa0c4d9 from=translated src=- shape=4ef6dadf vocab=25be844a
-/
lemma isVar_cases
    {ix : ℝ → I} {φ : I → ℝ → A}
    (hix : Measurable[_, ⊤] ix) (hφ : ∀ n, IsVar (φ n))
    : IsVar (fun r ↦ φ (ix r) r) := by
  have hI : Nonempty I := ⟨ix 0⟩
  have ⟨k, hk⟩ := Countable.exists_injective_nat I
  have hk' : ∀i, k.invFun (k i) = i := Function.leftInverse_invFun hk
  have hix' : Measurable (fun x ↦ k (ix x)) := Measurable.fun_comp measurable_from_top hix
  have hφk (n) : IsVar (φ (Function.invFun k n)) := by
    simp only [hφ]
  have := isVar_cases' hix' hφk
  simp_all

/--
@isnad1 id=iff.0h3v.s4.08555bb16e51 from=translated src=- shape=e0d9b943 vocab=8c10e303
-/
@[simp]
lemma isVar_iff_isHom {A : Type*} {_ : QuasiBorelSpace A} (f : ℝ → A) : IsVar f ↔ IsHom f := by
  apply Iff.intro
  · intro hf
    constructor
    intro φ hφ
    apply isVar_comp hφ hf
  · rintro ⟨hf⟩
    exact hf measurable_id

/--
@isnad1 id=iff.0h3v.s4.c8c41a21e18d from=translated src=- shape=2a7585ea vocab=cd559071
-/
@[simp]
lemma isHom_ofMeasurableSpace
    {A : Type*} {_ : MeasurableSpace A} (φ : ℝ → A)
    : IsHom[_, ofMeasurableSpace] φ ↔ Measurable φ := by
  rw [←isVar_iff_isHom]
  rfl

instance {A : Type*} {_ : MeasurableSpace A} : @MeasurableQuasiBorelSpace A ofMeasurableSpace _ :=
  @MeasurableQuasiBorelSpace.mk A ofMeasurableSpace _ fun _ ↦ by
    simp only [isHom_ofMeasurableSpace]

/--
@isnad1 id=iff.0h5v.s5.141a04cb572d from=translated src=- shape=3cc45bb8 vocab=45ea852a
-/
lemma isHom_def
    {A : Type*} {_ : QuasiBorelSpace A}
    {B : Type*} {_ : QuasiBorelSpace B}
    (f : A → B)
    : IsHom f ↔ (∀⦃φ : ℝ → A⦄, IsHom φ → IsHom fun x ↦ f (φ x)) := by
  apply Iff.intro
  · rintro ⟨hf⟩
    simp_all
  · intro hf
    constructor
    simpa only [isVar_iff_isHom] using hf

namespace IsHom

instance {f : A → B}
    : CoeFun (IsHom f) (fun _ ↦ ∀⦃φ : ℝ → A⦄, IsHom φ → IsHom fun x ↦ f (φ x)) where
  coe := by
    rw [←isHom_def]
    simp only [imp_self]

end IsHom

/--
@isnad1 id=iff.0h4v.s4.a427c9b43779 from=translated src=- shape=72fbd55d vocab=d8c4c874
-/
@[simp]
lemma isHom_iff_measurable
    {_ : MeasurableSpace A} [MeasurableQuasiBorelSpace A]
    (φ : ℝ → A)
    : IsHom φ ↔ Measurable φ :=
  MeasurableQuasiBorelSpace.isHom_iff_measurable φ

/--
@isnad1 id=ishom.1h7v.s5.a45827860e0e from=translated src=- shape=8f89da8b vocab=05c8a70a
-/
@[fun_prop]
lemma isHom_of_measurable
    {_ : MeasurableSpace A} [MeasurableQuasiBorelSpace A]
    {_ : MeasurableSpace B} [MeasurableQuasiBorelSpace B]
    (f : A → B) (hf : Measurable f)
    : IsHom f := by
  rw [isHom_def]
  simp only [isHom_iff_measurable]
  fun_prop

/--
@isnad1 id=ishom.0h2v.s3.5ae94655a810 from=translated src=- shape=746c6e19 vocab=402d12e6
-/
@[simp]
lemma isHom_id : IsHom (A := A) id := by
  rw [isHom_def]
  simp only [id_eq, imp_self, implies_true]

/--
@isnad1 id=ishom.0h2v.s3.7d28f2315781 from=translated src=- shape=81c0c4c1 vocab=3fa53d2d
-/
@[fun_prop, simp]
lemma isHom_id' : IsHom (fun x : A ↦ x) :=
  isHom_id

/--
@isnad1 id=ishom.2h8v.s5.bdd9f4a9ae20 from=translated src=- shape=3b720b30 vocab=7b8ec211
-/
lemma isHom_comp
    {f : B → C} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (f ∘ g) := by
  rw [isHom_def]
  intro φ hφ
  exact hf (hg hφ)

/--
@isnad1 id=ishom.2h8v.s5.da6e114534ca from=translated src=- shape=c1dbc426 vocab=3fa53d2d
-/
@[fun_prop]
lemma isHom_comp'
    {f : B → C} (hf : IsHom f)
    {g : A → B} (hg : IsHom g)
    : IsHom (fun x ↦ f (g x)) :=
  isHom_comp hf hg

/--
@isnad1 id=ishom.0h5v.s4.f74f5987dc6f from=translated src=- shape=99059531 vocab=b648805d
-/
@[simp]
lemma isHom_const (x : B) : IsHom (Function.const A x) := by
  constructor
  simp only [isVar_const, Function.const, implies_true]

/--
@isnad1 id=ishom.0h5v.s4.1511c6b635b5 from=translated src=- shape=90eb606c vocab=3fa53d2d
-/
@[fun_prop, simp]
lemma isHom_const' (x : B) : IsHom (fun _ : A ↦ x) :=
  isHom_const x

/--
@isnad1 id=ishom.2h7v.s5.ae6a7ad30a03 from=translated src=- shape=3b839039 vocab=9d0cd2f6
-/
lemma isHom_cases
    {ix : A → I} {f : I → A → B}
    (hix : IsHom[_, default] ix) (hf : ∀ n, IsHom (f n))
    : IsHom (fun x ↦ f (ix x) x) := by
  constructor
  intro φ hφ
  simp only [isVar_iff_isHom] at hφ
  apply isVar_cases (ix := fun x ↦ ix (φ x)) (φ := fun n x ↦ f n (φ x))
  · replace hix := hix hφ
    simp_all
  · intro n
    simp only [isVar_iff_isHom]
    refine hf _ ?_
    apply hφ

/--
@isnad1 id=ishom.0h6v.s4.96340de1c2f8 from=translated src=- shape=f242e781 vocab=84ff14c4
-/
@[simp, fun_prop]
lemma isHom_of_discrete_countable
    {_ : MeasurableSpace A} [DiscreteQuasiBorelSpace A] [Countable A]
    (f : A → B) : IsHom f := by
  apply isHom_cases (ix := fun x ↦ x) (f := fun x _ ↦ f x)
  · rw [isHom_def]
    intro φ hφ
    simp only [isHom_iff_measurable, isHom_ofMeasurableSpace] at ⊢ hφ
    intro X hX
    apply hφ
    apply MeasurableSet.of_discrete
  · fun_prop

/--
@isnad1 id=ishom.0h5v.s4.3004e32111d9 from=translated src=- shape=d3a7956e vocab=a40e8b04
-/
@[simp]
lemma isHom_to_subsingleton [Subsingleton B] (f : A → B) : IsHom f := by
  rw [isHom_def]
  intro φ hφ
  have : ∀r, f (φ r) = f (φ 0) := by subsingleton
  simp only [this, isHom_const']

/--
@isnad1 id=ishom.0h5v.s4.598d140059f7 from=translated src=- shape=42137534 vocab=a40e8b04
-/
@[simp]
lemma isHom_of_subsingleton [Subsingleton A] (f : A → B) : IsHom f := by
  rw [isHom_def]
  intro φ hφ
  have : ∀r, φ r = φ 0 := by subsingleton
  simp only [this, isHom_const']

/--
@isnad1 id=ishom.0h4v.s4.f9ffce8fd080 from=translated src=- shape=cb011a27 vocab=9541b357
-/
lemma isHom_of_lift {A} (f : A → B) : IsHom[lift f, _] f := by
  apply @IsHom.intro _ _ (lift f)
  intro φ hφ
  apply hφ

/--
@isnad1 id=iff.0h7v.s5.b9374c5e6acd from=translated src=- shape=ab5a9d09 vocab=9541b357
-/
lemma isHom_to_lift
    {A} (f : A → B) (g : C → A)
    : IsHom[_, lift f] g ↔ IsHom (fun x ↦ f (g x)) := by
  apply Iff.intro
  · rintro ⟨hg⟩
    constructor
    exact hg
  · rintro ⟨hg⟩
    apply @IsHom.intro _ _ _ (lift f)
    exact hg

/--
@isnad1 id=ishom.0h3v.s4.afa7c9258ffd from=translated src=- shape=22aa1ebb vocab=430199fa
-/
@[fun_prop]
lemma isHom_unpack
    [Nonempty A] {_ : MeasurableSpace A} [MeasurableQuasiBorelSpace A] [StandardBorelSpace A]
    : IsHom (MeasureTheory.unpack (A := A)) := by
  simp only [isHom_iff_measurable, MeasureTheory.measurable_unpack]

/--
@isnad1 id=ishom.0h2v.s4.f9966fbf6a0a from=translated src=- shape=b774eefa vocab=235f72a1
-/
@[fun_prop]
lemma isHom_mem_Icc {a b : ℝ} : IsHom (· ∈ Set.Icc a b) := by
  simp only [isHom_ofMeasurableSpace, measurable_mem, measurableSet_Icc]

/--
@isnad1 id=iff.2h7v.s6.333a0a56141d from=translated src=- shape=e1d1ef2e vocab=fa8171a5
-/
lemma isHom_cast
    {B} {instB : QuasiBorelSpace B}
    {C} {instC : QuasiBorelSpace C}
    {eq : B = C} (heq : ∀ (φ : ℝ → B), IsHom φ ↔ IsHom fun x ↦ cast eq (φ x))
    (f : A → B)
    : IsHom (fun x ↦ cast eq (f x)) ↔ IsHom f := by
  subst eq
  have : instB = instC := by
    ext
    simp_all
  subst this
  rfl

/--
@isnad1 id=measurab.1h7v.s5.ebfbc173c28c from=translated src=- shape=9409950d vocab=2860ecc0
-/
@[fun_prop]
lemma measurable_of_isHom
    {_ : MeasurableSpace A} [MeasurableQuasiBorelSpace A]
    {_ : MeasurableSpace B} [MeasurableQuasiBorelSpace B] [StandardBorelSpace B]
    (f : B → A) (hf : IsHom f)
    : Measurable f := by
  wlog hB : Nonempty B
  · simp only [not_nonempty_iff] at hB
    apply measurable_of_empty
  have : f = (fun a ↦ f (MeasureTheory.unpack a)) ∘ MeasureTheory.pack := by
    ext
    simp only [Function.comp_apply, MeasureTheory.unpack_pack]
  rw [this]
  apply Measurable.comp
  · rw [← MeasurableQuasiBorelSpace.isHom_iff_measurable]
    apply isHom_comp
    · exact hf
    · rw [MeasurableQuasiBorelSpace.isHom_iff_measurable]
      fun_prop
  · simp only [MeasureTheory.measurable_pack]

namespace NonEmpty

/--
@isnad1 id=ishom.1h4v.s4.5fb7bb92b00e from=translated src=- shape=3877224b vocab=f5958b01
-/
@[fun_prop]
lemma isHom_some (f : A → Nonempty B) : IsHom fun x ↦ (f x).some := by
  rw [isHom_def]
  intro φ hφ
  change IsHom fun _ ↦ (f (φ 0)).some
  apply isHom_const

end NonEmpty

/--
@isnad1 id=ishom.2h6v.s5.9e6876fbb795 from=translated src=- shape=e3937064 vocab=8c10e303
-/
lemma isHom_mono
    {B : Type*} {f : A → B} {inst₁ inst₂ : QuasiBorelSpace B}
    (hf : IsHom[_, inst₁] f)
    (hinst : ∀ φ : ℝ → B, inst₁.IsVar φ → inst₂.IsVar φ)
    : IsHom[_, inst₂] f := by
  rw [isHom_def] at ⊢ hf
  simp_all

/--
@isnad1 id=iff.0h3v.s5.de6d64dc7ad1 from=translated src=- shape=3a077ed2 vocab=4c65d759
-/
lemma measurableSet_toMeasurableSpace
    (X : Set A)
    : MeasurableSet[toMeasurableSpace] X
    ↔ ∀{φ : ℝ → A}, IsHom φ → MeasurableSet (φ ⁻¹' X) := by
  rfl

end QuasiBorelSpace
