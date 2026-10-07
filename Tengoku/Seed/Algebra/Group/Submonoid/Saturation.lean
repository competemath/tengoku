/-
Copyright (c) 2025 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Divisibility.Basic
public import Tengoku.Seed.Algebra.Group.Submonoid.Basic
public import Tengoku.Seed.Order.ConditionallyCompleteLattice.Basic

/-! # Saturation of a submonoid

We define a submonoid `s` to be saturated if `x * y ∈ s → x ∈ s ∧ y ∈ s`. The type of all
saturated submonoids forms a complete lattice. For a given submonoid `s` we construct the saturation
of `s` as the smallest saturated submonoid containing `s`, which when the underlying type is a
commutative monoid, is given by the formula `{x : M | ∃ y : M, x * y ∈ s}`.

Saturated submonoids are used in the context of localisations.

We also define the type of saturated submonoids, and endow on it the structure of a complete
lattice.

## Main Definitions

* `Submonoid.MulSaturated`: the condition `x * y ∈ s ↔ x ∈ s ∧ y ∈ s`. Not to be confused with
  `Submonoid.PowSaturated`.
* `SaturatedSubmonoid`: the type of `Submonoid` satisfying `MulSaturated`. It is a complete lattice.
* `Submonoid.saturation`: the smallest saturated submonoid containing a given submonoid.

-/

@[expose] public section

namespace Submonoid

/-- Given a submonoid `s` of `M`, we say that `s` is **saturated** if it satisfies
`x * y ∈ s → x ∈ s ∧ y ∈ s`.

It is called `MulSaturated` here to be distinguished from `Submonoid.PowSaturated` or
`AddSubmonoid.NSMulSaturated`, which is also called "saturated" in the literature. -/
@[to_additive
/-- Given an additive submonoid `s` of `M`, we say that `s` is **saturated** if it satisfies
`x + y ∈ s → x ∈ s ∧ y ∈ s`.

It is called `AddSaturated` here to be distinguished from `Submonoid.PowSaturated` or
`AddSubmonoid.NSMulSaturated`, which is also called "saturated" in the literature. -/]
def MulSaturated {M : Type*} [MulOneClass M] (s : Submonoid M) : Prop :=
  ∀ ⦃x y⦄, x * y ∈ s → x ∈ s ∧ y ∈ s

namespace MulSaturated
variable {M : Type*} [MulOneClass M] {s s₁ s₂ : Submonoid M}
  (h : s.MulSaturated) (h₁ : s₁.MulSaturated) (h₂ : s₂.MulSaturated)

include h in
/--
@isnad1 id=iff.1h4v.s6.cc490663c793 from=seed src=0 shape=019b31fa vocab=f8a7c873
-/
@[to_additive]
theorem mul_mem_iff {x y : M} : x * y ∈ s ↔ x ∈ s ∧ y ∈ s :=
  ⟨@h _ _, and_imp.mpr mul_mem⟩

/--
@isnad1 id=mulsatur.0h1v.s3.3d4f560ec198 from=seed src=0 shape=b8471119 vocab=e26d7ae2
-/
@[to_additive]
theorem top : MulSaturated (⊤ : Submonoid M) := fun _ _ _ ↦ ⟨trivial, trivial⟩

include h₁ h₂ in
/--
@isnad1 id=mulsatur.2h3v.s5.2a6865f5045d from=seed src=0 shape=0540dca0 vocab=ebd64b34
-/
@[to_additive]
theorem inf : MulSaturated (s₁ ⊓ s₂) :=
  fun _ _ hxy ↦ ⟨⟨(h₁ hxy.1).1, (h₂ hxy.2).1⟩, (h₁ hxy.1).2, (h₂ hxy.2).2⟩

/--
@isnad1 id=mulsatur.1h2v.s5.053a8d4aa4c6 from=seed src=0 shape=e18d22f7 vocab=bbc77db5
-/
@[to_additive]
theorem sInf {f : Set (Submonoid M)} (hf : ∀ s ∈ f, s.MulSaturated) :
    (sInf f).MulSaturated := fun _ _ hxy ↦ by
  simp_rw [mem_sInf] at hxy ⊢
  exact ⟨fun s hs ↦ (hf s hs <| hxy s hs).1, fun s hs ↦ (hf s hs <| hxy s hs).2⟩

/--
@isnad1 id=mulsatur.1h3v.s5.4756a931f505 from=seed src=0 shape=2a9c7bfb vocab=367dbb11
-/
@[to_additive]
theorem iInf {ι : Sort*} {f : ι → Submonoid M} (hf : ∀ i, (f i).MulSaturated) :
    (iInf f).MulSaturated :=
  sInf <| Set.forall_mem_range.mpr hf

/-- If `M` is commutative, we only need to check the left condition `x ∈ s`.
@isnad1 id=mulsatur.1h2v.s6.aa2ba3d022f8 from=seed src=0 shape=55355377 vocab=ccf86ba1
-/
@[to_additive /-- If `M` is commutative, we only need to check the left condition `x ∈ s`. -/]
theorem of_left {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → x ∈ s) : s.MulSaturated :=
  fun x y hxy ↦ ⟨h hxy, h <| mul_comm x y ▸ hxy⟩

/-- If `M` is commutative, we only need to check the right condition `y ∈ s`.
@isnad1 id=mulsatur.1h2v.s6.3ce10c2da07e from=seed src=0 shape=544626e9 vocab=ccf86ba1
-/
@[to_additive /-- If `M` is commutative, we only need to check the right condition `y ∈ s`. -/]
theorem of_right {M : Type*} [CommMonoid M] {s : Submonoid M}
    (h : ∀ ⦃x y⦄, x * y ∈ s → y ∈ s) : s.MulSaturated :=
  of_left fun x y ↦ mul_comm x y ▸ @h y x

end MulSaturated

end Submonoid

-- automatic generation failed
/-- A saturated additive submonoid is a submonoid `s` that satisfies `x + y ∈ s → x ∈ s ∧ y ∈ s`. -/
structure SaturatedAddSubmonoid (M : Type*) [AddZeroClass M] extends AddSubmonoid M where
  addSaturated : toAddSubmonoid.AddSaturated

/-- A saturated submonoid is a submonoid `s` that satisfies `x * y ∈ s → x ∈ s ∧ y ∈ s`. -/
@[to_additive] structure SaturatedSubmonoid (M : Type*) [MulOneClass M] extends Submonoid M where
  mulSaturated : toSubmonoid.MulSaturated

namespace SaturatedSubmonoid
variable {M : Type*} [MulOneClass M]

attribute [simp] mulSaturated SaturatedAddSubmonoid.addSaturated

/--
@isnad1 id=injectiv.0h1v.s3.d493afb5ec10 from=seed src=0 shape=e716c754 vocab=799178e3
-/
@[to_additive]
theorem toSubmonoid_injective : (toSubmonoid (M := M)).Injective :=
  fun ⟨s₁, h₁⟩ ⟨s₂, h₂⟩ eq ↦ by congr

/--
@isnad1 id=eq.1h3v.s5.dfea97f86a38 from=seed src=0 shape=38ece54e vocab=73269447
-/
@[to_additive (attr := ext)]
lemma ext {s₁ s₂ : SaturatedSubmonoid M} (h : s₁.toSubmonoid = s₂.toSubmonoid) : s₁ = s₂ :=
  toSubmonoid_injective h

variable (M) in
@[to_additive]
instance : SetLike (SaturatedSubmonoid M) M where
  coe := (·.carrier)
  coe_injective _ _ h := toSubmonoid_injective <| SetLike.coe_injective h

@[to_additive]
instance : PartialOrder (SaturatedSubmonoid M) := .ofSetLike ..

/--
@isnad1 id=eq.1h3v.s5.7b04ca80ee70 from=seed src=0 shape=b6dfcf64 vocab=2970a2e6
-/
@[to_additive]
lemma ext' {s₁ s₂ : SaturatedSubmonoid M} (h : ∀ x, x ∈ s₁ ↔ x ∈ s₂) : s₁ = s₂ :=
  SetLike.ext h

variable (M) in
@[to_additive]
instance : SubmonoidClass (SaturatedSubmonoid M) M where
  mul_mem {s} := s.mul_mem
  one_mem {s} := s.one_mem

/--
@isnad1 id=iff.0h3v.s5.8038b69abe34 from=seed src=0 shape=51b12b4b vocab=7376b688
-/
@[to_additive (attr := simp)]
lemma mem_toSubmonoid {s : SaturatedSubmonoid M} {x : M} : x ∈ s.toSubmonoid ↔ x ∈ s :=
  Iff.rfl

@[to_additive]
instance : Top (SaturatedSubmonoid M) where
  top := { (⊤ : Submonoid M) with mulSaturated := .top }

/--
@isnad1 id=mem.0h2v.s4.ca4503bbba1c from=seed src=0 shape=c1ca4a78 vocab=f2ee9873
-/
@[to_additive (attr := simp)]
theorem mem_top {x : M} : x ∈ (⊤ : SaturatedSubmonoid M) := trivial

variable (M) in
@[to_additive]
instance : Min (SaturatedSubmonoid M) where
  min s₁ s₂ := { s₁.toSubmonoid ⊓ s₂.toSubmonoid with mulSaturated := .inf s₁.2 s₂.2 }

variable (M) in
@[to_additive]
instance : InfSet (SaturatedSubmonoid M) where
  sInf f :=
  { carrier := ⋂ s ∈ f, s
    mul_mem' hx hy := by rw [Set.mem_iInter₂] at *; exact fun s hs ↦ mul_mem (hx s hs) (hy s hs)
    one_mem' := Set.mem_iInter₂.mpr fun _ _ ↦ one_mem _
    mulSaturated := by
      convert! Submonoid.MulSaturated.sInf (f := toSubmonoid '' f) (by simp)
      ext; simp [Submonoid.mem_sInf] }

/--
@isnad1 id=iff.0h3v.s6.5ecaca069baf from=seed src=0 shape=dd21b285 vocab=7500fa43
-/
@[to_additive]
theorem mem_sInf {f : Set (SaturatedSubmonoid M)} {x : M} : x ∈ sInf f ↔ ∀ s ∈ f, x ∈ s :=
  Set.mem_iInter₂

variable (M) in
@[to_additive]
instance : CompleteSemilatticeInf (SaturatedSubmonoid M) where
  isGLB_sInf _ := .of_image SetLike.coe_subset_coe isGLB_biInf

end SaturatedSubmonoid

namespace Submonoid

/-- The saturation of a submonoid `s` is the intersection of all saturated submonoids that contain
`s`.

If `M` is a commutative monoid, then this is `{x : M | ∃ y : M, x * y ∈ s}`. -/
@[to_additive
/-- The saturation of an additive submonoid `s` is the intersection of all saturated submonoids
that contain `s`.

If `M` is a commutative additive monoid, then this is `{x : M | ∃ y : M, x + y ∈ s}`. -/]
def saturation {M : Type*} [MulOneClass M] (s : Submonoid M) : SaturatedSubmonoid M :=
  sInf {t | s ≤ t.toSubmonoid}

variable {M : Type*}

section MulOneClass
variable [MulOneClass M]

variable (M) in
/--
@isnad1 id=galoisco.0h1v.s5.5c60d8925749 from=seed src=0 shape=1e07aa1c vocab=c0338ed3
-/
@[to_additive]
theorem gc_saturation : GaloisConnection (saturation (M := M)) (·.toSubmonoid) := fun _ _ ↦
  ⟨fun ih _ hx ↦ ih <| SaturatedSubmonoid.mem_sInf.mpr fun _ ht ↦ ht hx,
  fun ih _ hx ↦ SaturatedSubmonoid.mem_sInf.mp hx _ ih⟩

variable (M) in
/-- `saturation` forms a `GaloisInsertion` with the forgetful functor
`SaturatedSubmonoid.toSubmonoid`. -/
@[to_additive
/-- `saturation` forms a `GaloisInsertion` with the forgetful functor
`SaturatedAddSubmonoid.toAddSubmonoid`. -/]
def giSaturation : GaloisInsertion (saturation (M := M)) (·.toSubmonoid) where
  choice s hs := { s with mulSaturated := le_antisymm ((gc_saturation M).le_u_l s) hs ▸ by simp }
  gc := gc_saturation M
  le_l_u s := (gc_saturation M).le_u_l s.toSubmonoid
  choice_eq s h := le_antisymm ((gc_saturation M).le_u_l s) h

variable {a : Submonoid M} {b : SaturatedSubmonoid M}

/--
@isnad1 id=iff.0h3v.s5.4019021723b7 from=seed src=0 shape=cf880aea vocab=3f9d96f9
-/
@[to_additive]
theorem saturation_le_iff_le : a.saturation ≤ b ↔ a ≤ b.toSubmonoid := gc_saturation ..

/--
@isnad1 id=le.1h3v.s5.8a17af5ccc7e from=seed src=0 shape=c7f6e821 vocab=3f9d96f9
-/
@[to_additive]
alias ⟨_, saturation_le_of_le⟩ := saturation_le_iff_le

/--
@isnad1 id=le.0h2v.s5.74b969562a63 from=seed src=0 shape=a66e7190 vocab=f4c174de
-/
@[to_additive]
theorem le_toSubmonoid_saturation : a ≤ a.saturation.toSubmonoid := (gc_saturation M).le_u_l a

/--
@isnad1 id=eq.0h2v.s4.f526a226b8fc from=seed src=0 shape=2896fe98 vocab=a561ce87
-/
@[to_additive (attr := simp)]
theorem saturation_toSubmonoid : b.saturation = b := (giSaturation M).l_u_eq b

/--
@isnad1 id=var.2h6v.s7.3af208dbb849 from=seed src=0 shape=80008454 vocab=70ba67d2
-/
@[to_additive (attr := elab_as_elim)]
theorem saturation_induction {s : Submonoid M}
    {p : (x : M) → x ∈ s.saturation → Prop}
    (mem : ∀ (x) (hx : x ∈ s), p x (le_toSubmonoid_saturation hx))
    (mul : ∀ x y hx hy, p x hx → p y hy → p (x * y) (mul_mem hx hy))
    (of_mul : ∀ (x y) (hxy : x * y ∈ s.saturation),
      p (x * y) hxy → p x (s.saturation.2 hxy).1 ∧ p y (s.saturation.2 hxy).2)
    {x : M} (hx : x ∈ s.saturation) : p x hx := by
  let s' : SaturatedSubmonoid M :=
  { carrier := { x | ∃ hx, p x hx }
    one_mem' := ⟨_ , mem 1 <| one_mem s⟩
    mul_mem' := fun ⟨_, hpx⟩ ⟨_, hpy⟩ ↦ ⟨_, mul _ _ _ _ hpx hpy⟩
    mulSaturated := fun x y ⟨_, hpxy⟩ ↦ ⟨⟨_, (of_mul _ _ _ hpxy).1⟩, ⟨_, (of_mul _ _ _ hpxy).2⟩⟩ }
  exact SaturatedSubmonoid.mem_sInf.mp hx s' (fun _ h ↦ ⟨_, mem _ h⟩) |>.2

end MulOneClass

section CommMonoid
variable [CommMonoid M]

variable {s : Submonoid M} {x : M}

/--
@isnad1 id=iff.0h3v.s6.0ae78b8c5a64 from=seed src=0 shape=9ec127d3 vocab=50101011
-/
@[to_additive]
theorem mem_saturation_iff : x ∈ s.saturation ↔ ∃ y, x * y ∈ s := by
  refine ⟨fun h ↦ ?_, fun ⟨y, hxy⟩ ↦ (s.saturation.2 <| le_toSubmonoid_saturation hxy).1⟩
  induction h using saturation_induction with
  | mem _ hx => exact ⟨1, by simpa⟩
  | mul _ _ _ _ ih₁ ih₂ =>
    exact ih₁.elim fun y₁ h₁ ↦ ih₂.elim fun y₂ h₂ ↦
      ⟨y₁ * y₂, by rw [mul_mul_mul_comm]; exact mul_mem h₁ h₂⟩
  | of_mul x₁ x₂ _ ih =>
    exact ih.elim fun y h ↦ ⟨⟨x₂ * y, by rwa [← mul_assoc]⟩,
      ⟨x₁ * y, by rwa [mul_left_comm, ← mul_assoc]⟩⟩

/--
@isnad1 id=iff.0h3v.s6.b7075d94ff96 from=seed src=0 shape=d35f8b61 vocab=50101011
-/
@[to_additive]
theorem mem_saturation_iff' : x ∈ s.saturation ↔ ∃ y, y * x ∈ s := by
  simp_rw [mem_saturation_iff, mul_comm x]

/--
@isnad1 id=iff.0h3v.s6.d89d77e814bc from=seed src=0 shape=0ed595c7 vocab=149ab6e3
-/
theorem mem_saturation_iff_exists_dvd : x ∈ s.saturation ↔ ∃ m ∈ s, x ∣ m := by
  simp_rw [dvd_def, existsAndEq, and_true, mem_saturation_iff]

end CommMonoid

end Submonoid

namespace SaturatedSubmonoid

@[to_additive]
instance (M : Type*) [MulOneClass M] :
    CompleteLattice (SaturatedSubmonoid M) :=
  { (inferInstance : PartialOrder (SaturatedSubmonoid M)),
    (inferInstance : Top (SaturatedSubmonoid M)),
    (inferInstance : Min (SaturatedSubmonoid M)),
    (inferInstance : CompleteSemilatticeInf (SaturatedSubmonoid M)),
    (Submonoid.giSaturation M).liftCompleteLattice with }

variable {M : Type*}

section MulOneClass
variable [MulOneClass M]

/--
@isnad1 id=eq.0h1v.s6.6cca76e4b553 from=seed src=0 shape=82e1e886 vocab=4c0d4c50
-/
@[to_additive]
theorem bot_def : (⊥ : SaturatedSubmonoid M) = Submonoid.saturation ⊥ := rfl

/--
@isnad1 id=eq.0h3v.s6.430c6c7f447a from=seed src=0 shape=70d9b047 vocab=cbb94e99
-/
@[to_additive]
theorem sup_def {s₁ s₂ : SaturatedSubmonoid M} :
    s₁ ⊔ s₂ = (s₁.toSubmonoid ⊔ s₂.toSubmonoid).saturation := rfl

/--
@isnad1 id=eq.0h2v.s6.32a5e6bf524d from=seed src=0 shape=f57f5a1b vocab=fbc35206
-/
@[to_additive]
theorem sSup_def {f : Set (SaturatedSubmonoid M)} :
    sSup f = (sSup (toSubmonoid '' f)).saturation := rfl

/--
@isnad1 id=eq.0h3v.s6.7187677d00ac from=seed src=0 shape=22376cc1 vocab=de0748ff
-/
@[to_additive]
theorem iSup_def {ι : Sort*} {f : ι → SaturatedSubmonoid M} :
    iSup f = (⨆ i, (f i).toSubmonoid).saturation :=
  (Submonoid.giSaturation M).l_iSup_u f |>.symm

end MulOneClass

section CommMonoid
variable [CommMonoid M]

/--
@isnad1 id=iff.0h2v.s7.574b99192548 from=seed src=0 shape=362c8caa vocab=b9965172
-/
@[to_additive]
theorem mem_bot_iff {x : M} : x ∈ (⊥ : SaturatedSubmonoid M) ↔ IsUnit x := by
  simp_rw [bot_def, Submonoid.mem_saturation_iff, Submonoid.mem_bot, isUnit_iff_exists_inv]

end CommMonoid

end SaturatedSubmonoid

namespace Submonoid
variable {M : Type*} [MulOneClass M]

/--
@isnad1 id=eq.0h1v.s6.abcf963cd4f2 from=seed src=0 shape=ffb52003 vocab=4c0d4c50
-/
@[to_additive (attr := simp)]
theorem saturation_bot : (⊥ : Submonoid M).saturation = ⊥ := (gc_saturation M).l_bot

/--
@isnad1 id=eq.0h1v.s4.4c7be3ea61a6 from=seed src=0 shape=ffb52003 vocab=b2805675
-/
@[to_additive (attr := simp)]
theorem saturation_top : (⊤ : Submonoid M).saturation = ⊤ := (giSaturation M).l_top

/--
@isnad1 id=eq.0h3v.s6.2fcbba1209b5 from=seed src=0 shape=19128959 vocab=ce341e68
-/
@[to_additive (attr := simp)]
theorem saturation_sup {s₁ s₂ : Submonoid M} :
    (s₁ ⊔ s₂).saturation = s₁.saturation ⊔ s₂.saturation := (gc_saturation M).l_sup

-- note that it does not preserve inf:
-- if s₁ = {6 ^ n | n : ℕ} and s₂ = {15 ^ n | n : ℕ} then
-- (s₁ ⊓ s₂).saturation = {1} and
-- s₁.saturation ⊓ s₂.saturation = {3 ^ n | n : ℕ}

/--
@isnad1 id=eq.0h2v.s6.0ceb2786fd22 from=seed src=0 shape=62c3850c vocab=d317358a
-/
@[to_additive (attr := simp)]
theorem saturation_sSup {f : Set (Submonoid M)} :
    (sSup f).saturation = ⨆ s ∈ f, s.saturation := (gc_saturation M).l_sSup

/--
@isnad1 id=eq.0h3v.s6.5275a0ce461f from=seed src=0 shape=d91e39ea vocab=3bd658f1
-/
@[to_additive (attr := simp)]
theorem saturation_iSup {ι : Sort*} {f : ι → Submonoid M} :
    (iSup f).saturation = ⨆ i, (f i).saturation := (gc_saturation M).l_iSup

end Submonoid
