/-
Copyright (c) 2026 Jiazhen Xia. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiazhen Xia
-/
module

public import Tengoku

/-!
TODO: Use `Pointed` (the category of pointed types) in Mathlib.
-/

@[expose] public section

/- A pointed map from `(X, x₀)` to `(Y, y₀)` is a function `f : X → Y` such that `f x₀ = y₀`. -/
/-- `IsPointedMap` -/
class IsPointedMap {X Y : Type*} [Inhabited X] [Inhabited Y] (f : X → Y) : Prop where
  map_default : f default = default

namespace IsPointedMap

variable {X Y : Type*} [Inhabited X] [Inhabited Y] (f : X → Y) [IsPointedMap f]

/--
@isnad1 id=mem.1h4v.s5.1ad8e6369601 from=translated src=- shape=70cf501b vocab=82ebefc6
-/
lemma default_mem_image_of_default_mem {A : Set X} : default ∈ A → default ∈ f '' A :=
  fun h ↦ (Set.mem_image _ _ _).mpr ⟨default, ⟨h, IsPointedMap.map_default⟩⟩

/--
@isnad1 id=mem.0h3v.s5.c4ed08f215bc from=translated src=- shape=24166962 vocab=b38fac08
-/
lemma default_mem_preimage_default : default ∈ f ⁻¹' {default} := by
  apply Set.mem_preimage.mpr
  rw [(IsPointedMap.map_default : f _ = _)]
  exact Set.mem_singleton _

/--
@isnad1 id=le.0h3v.s5.07777954e06d from=translated src=- shape=ff715c39 vocab=e55f483b
-/
lemma default_subset_preimage_default : {default} ⊆ f ⁻¹' {default} :=
  Set.singleton_subset_iff.mpr (default_mem_preimage_default _)

/--
@isnad1 id=eq.0h3v.s5.84ce5b3bd2cc from=translated src=- shape=6ab92e4b vocab=05e8bb51
-/
lemma default_eq_image_preimage_default : {default} = f '' (f ⁻¹' {default}) := by
  refine Set.Subset.antisymm ?_ (Set.image_preimage_subset f {default})
  apply Set.singleton_subset_iff.mpr
  apply default_mem_image_of_default_mem
  exact default_mem_preimage_default f

end IsPointedMap

namespace ExactSeq

/- The sequence `X --f-> Y --g-> Z` of pointed sets is said to be exact at `Y`
if `Ker g = Im f`. -/
/-- `IsExactAt` -/
def IsExactAt {X Y Z : Type*} [Inhabited Z]
    (f : X → Y) (g : Y → Z) : Prop :=
  g ⁻¹' {default} = Set.range f

/--
@isnad1 id=isexacta.2h5v.s6.1303d0bd7b3c from=translated src=- shape=56b46381 vocab=0c5cdb05
-/
lemma isExactAt_of_ker_supset_im_of_ker_subset_im
    {X Y Z : Type*} [Inhabited Z] {f : X → Y} {g : Y → Z}
    (hsup : ∀ y, (∃ x, f x = y) → g y = default)
    (hsub : ∀ y, (g y = default) → ∃ x, f x = y) :
    IsExactAt f g := by
  apply Set.eq_of_subset_of_subset
  · intro y hy
    exact Set.mem_range.mpr <| hsub y <| Set.mem_preimage.mp hy
  · intro y hy
    exact Set.mem_preimage.mpr <| Set.mem_singleton_iff.mpr <| hsup y <| Set.mem_range.mp hy

/-!
Given an exact sequence
`A --a-> B --b-> C --c-> D --d-> E`
of five pointed sets, if `a` is surjective and `d` is injective, then `C = 0`.
*proof.*
- `Ker b = Im a = B` (since `a` is surjective)
- Hence `Im b = 0`
- `0 = Ker d = Im c` (since `d` is injective)
- Hence `Ker c = C`
- Use `Ker c = Im b` to conclude `C = 0`.
-/

variable {A B C D E : Type*}
variable [Inhabited A] [Inhabited B] [Inhabited C] [Inhabited D] [Inhabited E]

omit [Inhabited A] in
private lemma im_B_eq_zero (a : A → B) (b : B → C) (a_surj : Function.Surjective a)
    (exb : IsExactAt a b) :
    Set.range b = {default} := by
  rw [IsExactAt, Set.range_eq_univ.mpr a_surj] at exb
  simp_all

omit [Inhabited C] in
private lemma ker_c_eq_C (c : C → D) (d : D → E) (d_inj : Function.Injective d)
    [IsPointedMap d] (exd : IsExactAt c d) :
    c ⁻¹' {default} = Set.univ := by
  rw [IsExactAt] at exd
  have : d ⁻¹' {default} = {default} := by
    refine Set.Subset.antisymm ?_ (IsPointedMap.default_subset_preimage_default _)
    apply Set.subset_singleton_iff.mpr
    intro x hx
    rw [Set.mem_preimage, Set.mem_singleton_iff] at hx
    apply @d_inj x default
    rw [hx]
    exact Eq.symm IsPointedMap.map_default
  simp_all

omit [Inhabited A] in
/-- `C = {0}` if there is an exact sequence `A --a-> B --b-> C --c-> D --d-> E`
of five pointed sets such that `a` is surjective and `d` is injective.
@isnad1 id=nonempty.5h9v.s6.6cc591c65d62 from=translated src=- shape=cba04f3a vocab=88de8357
-/
theorem unique_mid_of_five (a : A → B) (b : B → C) (c : C → D) (d : D → E)
    [IsPointedMap d]
    (a_surj : Function.Surjective a) (d_inj : Function.Injective d)
    (exb : IsExactAt a b) (exc : IsExactAt b c) (exd : IsExactAt c d) :
    Nonempty (Unique C) :=
  Nonempty.intro <|
    { uniq := fun x ↦ by
        have h1 := im_B_eq_zero a b a_surj exb
        have h2 := ker_c_eq_C c d d_inj exd
        have h : @Set.univ C = {default} := h2.symm.trans exc |>.trans h1
        apply Set.eq_singleton_iff_unique_mem.mp h |>.right
        simp only [Set.mem_univ] }

end ExactSeq
