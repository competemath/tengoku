/-
Copyright (c) 2024 Joseph Myers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joseph Myers
-/
import Tengoku.Aperiodicmonotiles.AM.Mathlib.Combinatorics.Tiling.TileSet

/-!
# Bundled functions on tilings

This file defines bundled functions on tilings in a discrete context.

## Main definitions

* `TileSetFunction ps α H`: A bundled function from `TileSet ps ιₜ` to `α` that is invariant under
change or permutation of index type `ιₜ` and under the action of group elements in `H`.

* `VarTileSetFunction Y ps α H`: A bundled function from `Y` (acted on by `G`) and `TileSet ps ιₜ`
to `α` that is invariant under change or permutation of index type `ιₜ` and under the action of
group elements in `H` on both the value from `Y` and the `TileSet`.

## References

* [Branko Grünbaum and G. C. Shephard, *Tilings and Patterns*][GrunbaumShephard1987]
-/

noncomputable section

namespace DiscreteTiling

open Function
open scoped Pointwise

variable {G X Y ιₚ : Type*} [Group G] [MulAction G X] [MulAction G Y]

universe u
variable {ps : Protoset G X ιₚ} {ιᵤ ιᵤ' : Type u} {ιₜ ιₜ' Eᵤ α β γ : Type*}
variable {H : Subgroup G}
variable [EquivLike Eᵤ ιᵤ' ιᵤ]

section

variable (Y ps α H) in
/-- A `TileSetFunction ps α H` is a function from `TileSet ps ιₜ` to `α` that is invariant under
change or permutation of index type `ιₜ` (within the same universe) and under the action of group
elements in `H`. -/
@[ext] structure TileSetFunction where
  /-- The function.  Use the coercion to a function rather than using `toFun` directly. -/
  toFun : {ιₜ : Type u} → TileSet ps ιₜ → α
  /-- The function is invariant under reindexing. -/
  reindex_eq' : ∀ {ιₜ ιₜ' : Type u} (f : ιₜ ≃ ιₜ') (t : TileSet ps ιₜ),
    toFun (t.reindex f.symm) = toFun t
  /-- The function is invariant under the group action within the subgroup `H`. -/
  smul_eq : ∀ {ιₜ : Type u} {g : G} (t : TileSet ps ιₜ), g ∈ H → toFun (g • t) = toFun t

variable (Y ps α H) in
/-- A `VarTileSetFunction Y ps α H` is a function from `Y` and `TileSet ps ιₜ` to `α` that is
invariant under change or permutation of index type `ιₜ` (within the same universe) and under the
action (on both arguments) of group elements in `H`. -/
@[ext] structure VarTileSetFunction where
  /-- The function.  Use the coercion to a function rather than using `toFun` directly. -/
  toFun : {ιₜ : Type u} → Y → TileSet ps ιₜ → α
  /-- The function is invariant under reindexing. -/
  reindex_eq' : ∀ {ιₜ ιₜ' : Type u} (f : ιₜ ≃ ιₜ') (y : Y) (t : TileSet ps ιₜ),
    toFun y (t.reindex f.symm) = toFun y t
  /-- The function is invariant under the group action within the subgroup `H`. -/
  smul_eq : ∀ {ιₜ : Type u} {g : G} (y : Y) (t : TileSet ps ιₜ), g ∈ H →
    toFun (g • y) (g • t) = toFun y t

end

namespace TileSetFunction

instance : CoeFun (TileSetFunction ps α H) (fun _ ↦ {ιₜ : Type*} → TileSet ps ιₜ → α) where
  coe := toFun

attribute [coe] toFun

attribute [simp] smul_eq

/--
@isnad1 id=eq.0h12v.s6.c1162bb2ce3f from=translated src=- shape=ef9f991a vocab=bf991bcc
-/
@[simp] lemma reindex_eq (f : TileSetFunction ps α H) (t : TileSet ps ιᵤ) (e : Eᵤ) :
    f (t.reindex e) = f t :=
  f.reindex_eq' (EquivLike.toEquiv e).symm t

/--
@isnad1 id=eq.1h11v.s6.be645832160a from=translated src=- shape=35913ab7 vocab=29f576fd
-/
@[simp] lemma reindex_eq_of_bijective (f : TileSetFunction ps α H) (t : TileSet ps ιᵤ)
    {e : ιᵤ' → ιᵤ} (h : Bijective e) : f (t.reindex e) = f t :=
  f.reindex_eq t <| Equiv.ofBijective e h

/--
@isnad1 id=eq.2h7v.s7.b8c9b5288add from=translated src=- shape=0f13cecd vocab=7ac2005b
-/
lemma coe_mk (f : {ιₜ : Type*} → TileSet ps ιₜ → α) (hr hs) :
    (⟨f, hr, hs⟩ : TileSetFunction ps α H) = @f :=
  rfl

/--
@isnad1 id=iff.0h8v.s6.e4b1554f71e7 from=translated src=- shape=03534da7 vocab=43cb1d4c
-/
@[simp, norm_cast] lemma coe_inj {f₁ f₂ : TileSetFunction ps α H} :
    (@f₁ : {ιₜ : Type*} → TileSet ps ιₜ → α) = f₂ ↔ f₁ = f₂ :=
  TileSetFunction.ext_iff.symm

/--
@isnad1 id=injectiv.0h6v.s5.a56b2747a99e from=translated src=- shape=4f11264d vocab=54df1b3b
-/
lemma coe_injective :
    Injective (TileSetFunction.toFun : TileSetFunction ps α H → {ιₜ : Type*} → TileSet ps ιₜ → α) :=
  fun _ _ ↦ coe_inj.1

/--
@isnad1 id=iff.0h11v.s6.9557532d1337 from=translated src=- shape=9736f16a vocab=bf991bcc
-/
lemma reindex_iff {f : TileSetFunction ps Prop H} {t : TileSet ps ιᵤ} (e : Eᵤ) :
    f (t.reindex e) ↔ f t :=
  by simp

/--
@isnad1 id=iff.1h10v.s6.956e704c3955 from=translated src=- shape=25dbb3e2 vocab=29f576fd
-/
lemma reindex_iff_of_bijective {f : TileSetFunction ps Prop H} {t : TileSet ps ιᵤ} {e : ιᵤ' → ιᵤ}
    (h : Bijective e) : f (t.reindex e) ↔ f t :=
  by simp [h]

/--
@isnad1 id=iff.1h9v.s7.b8d9421eee47 from=translated src=- shape=6d873828 vocab=272308b8
-/
lemma smul_iff {f : TileSetFunction ps Prop H} {g : G} {t : TileSet ps ιₜ} (hg : g ∈ H) :
    f (g • t) ↔ f t :=
  by simp [hg]

lemma eq_of_coeSet_eq_of_injective (f : TileSetFunction ps α H) {t₁ : TileSet ps ιᵤ}
    {t₂ : TileSet ps ιᵤ'} (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁)
    (h₂ : Injective t₂) : f t₁ = f t₂ := by
  rw [← TileSet.reindex_equivOfCoeSetEqOfInjective h h₁ h₂]
  exact (reindex_eq _ _ _).symm

/--
@isnad1 id=iff.3h10v.s7.05b5b1ff76e6 from=translated src=- shape=17efa4f9 vocab=9f41602d
-/
lemma iff_of_coeSet_eq_of_injective (f : TileSetFunction ps Prop H) {t₁ : TileSet ps ιᵤ}
    {t₂ : TileSet ps ιᵤ'} (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁)
    (h₂ : Injective t₂) : f t₁ ↔ f t₂ := by
  simpa using f.eq_of_coeSet_eq_of_injective h h₁ h₂

variable (ps H) in
/-- The constant `TileSetFunction`. -/
protected def const (a : α) : TileSetFunction ps α H :=
  ⟨fun {ιₜ} ↦ const (TileSet ps ιₜ) a, by simp, by simp⟩

variable (H) in
/--
@isnad1 id=eq.0h9v.s6.4ebfcad9b079 from=translated src=- shape=01fbe020 vocab=27835f70
-/
@[simp] lemma const_apply (a : α) (t : TileSet ps ιₜ) : TileSetFunction.const ps H a t = a := rfl

/-- Composing a `TileSetFunction` with a function on the result type. -/
protected def comp (f : TileSetFunction ps α H) (fab : α → β) : TileSetFunction ps β H :=
  ⟨fab ∘ f.toFun, by simp, fun _ hg ↦ by simp [hg]⟩

/--
@isnad1 id=eq.0h11v.s6.59db8c8c1570 from=translated src=- shape=a4e6452c vocab=2fdaf28c
-/
@[simp] lemma comp_apply (f : TileSetFunction ps α H) (fab : α → β) (t : TileSet ps ιₜ) :
    f.comp fab t = fab (f t) :=
  rfl

/--
@isnad1 id=eq.0h11v.s6.8469c4263868 from=translated src=- shape=2aa1544b vocab=61ed5388
-/
lemma comp_comp (f : TileSetFunction ps α H) (fab : α → β) (fbg : β → γ) :
    f.comp (fbg ∘ fab) = (f.comp fab).comp fbg :=
  rfl

/-- Combining two `TileSetFunction`s with a function on their result types. -/
protected def comp₂ (f : TileSetFunction ps α H) (f' : TileSetFunction ps β H) (fabg : α → β → γ) :
    TileSetFunction ps γ H :=
  ⟨fun {ιₜ : Type*} (t : TileSet ps ιₜ) ↦ fabg (f t) (f' t), by simp, fun _ hg ↦ by simp [hg]⟩

/--
@isnad1 id=eq.0h13v.s6.812442a83553 from=translated src=- shape=76f72a4b vocab=5e633b0e
-/
@[simp] lemma comp₂_apply (f : TileSetFunction ps α H) (f' : TileSetFunction ps β H)
    (fabg : α → β → γ) (t : TileSet ps ιₜ) : f.comp₂ f' fabg t = fabg (f t) (f' t) :=
  rfl

/-- Converting a `TileSetFunction ps α H` to one using a subgroup of `H`. -/
protected def ofLE {H' : Subgroup G} (h : H' ≤ H) :
    TileSetFunction ps α H ↪ TileSetFunction ps α H' where
  toFun f := ⟨f.toFun, by simp, fun _ hg ↦ by simp [SetLike.le_def.1 h hg]⟩
  inj' f f' h := by simpa using h

/--
@isnad1 id=eq.1h10v.s7.7ba91dc1041d from=translated src=- shape=dc130c3f vocab=58776f23
-/
@[simp] lemma ofLE_apply (f : TileSetFunction ps α H) {H' : Subgroup G} (h : H' ≤ H)
    (t : TileSet ps ιₜ) : f.ofLE h t = f t :=
  rfl

variable (ps) in
/--
@isnad1 id=eq.1h8v.s7.faaa9c79aa8e from=translated src=- shape=3217e516 vocab=9a65306e
-/
@[simp] lemma ofLE_const (a : α) {H' : Subgroup G} (h : H' ≤ H) :
    (TileSetFunction.const ps H a).ofLE h = TileSetFunction.const ps H' a :=
  rfl

/--
@isnad1 id=eq.1h10v.s8.1e26e1aa1a54 from=translated src=- shape=831adddd vocab=b4b00fa6
-/
lemma ofLE_comp (f : TileSetFunction ps α H) (fab : α → β) {H' : Subgroup G} (h : H' ≤ H) :
    (f.comp fab).ofLE h = (f.ofLE h).comp fab :=
  rfl

/--
@isnad1 id=eq.1h12v.s8.64af99c67e98 from=translated src=- shape=7d803ed8 vocab=5a0a5569
-/
lemma ofLE_comp₂ (f : TileSetFunction ps α H) (f' : TileSetFunction ps β H) (fabg : α → β → γ)
    {H' : Subgroup G} (h : H' ≤ H) : (f.comp₂ f' fabg).ofLE h = (f.ofLE h).comp₂ (f'.ofLE h) fabg :=
  rfl

end TileSetFunction

namespace VarTileSetFunction

instance : CoeFun (VarTileSetFunction Y ps α H) (fun _ ↦ {ιₜ : Type*} → Y → TileSet ps ιₜ → α) where
  coe := toFun

attribute [coe] toFun

attribute [simp] smul_eq

/--
@isnad1 id=eq.0h14v.s7.62f65ba2105a from=translated src=- shape=8e8d5952 vocab=53c523f0
-/
@[simp] lemma reindex_eq (f : VarTileSetFunction Y ps α H) (y : Y) (t : TileSet ps ιᵤ) (e : Eᵤ) :
    f y (t.reindex e) = f y t :=
  f.reindex_eq' (EquivLike.toEquiv e).symm y t

/--
@isnad1 id=eq.1h13v.s6.099ff354e35c from=translated src=- shape=ffcf193e vocab=a6c7eb7d
-/
@[simp] lemma reindex_eq_of_bijective (f : VarTileSetFunction Y ps α H) (y : Y) (t : TileSet ps ιᵤ)
    {e : ιᵤ' → ιᵤ} (h : Bijective e) : f y (t.reindex e) = f y t :=
  f.reindex_eq y t <| Equiv.ofBijective e h

/--
@isnad1 id=eq.2h8v.s8.aaf323bb2996 from=translated src=- shape=95c95dd6 vocab=f8250a85
-/
lemma coe_mk (f : {ιₜ : Type*} → Y → TileSet ps ιₜ → α) (hr hs) :
    (⟨f, hr, hs⟩ : VarTileSetFunction Y ps α H) = @f :=
  rfl

/--
@isnad1 id=iff.0h9v.s6.e84a1745023d from=translated src=- shape=6a7cb1d8 vocab=3adb5815
-/
@[simp, norm_cast] lemma coe_inj {f₁ f₂ : VarTileSetFunction Y ps α H} :
    (@f₁ : {ιₜ : Type*} → Y → TileSet ps ιₜ → α) = f₂ ↔ f₁ = f₂ :=
  VarTileSetFunction.ext_iff.symm

/--
@isnad1 id=injectiv.0h7v.s6.d604454c998b from=translated src=- shape=f7aa0244 vocab=147b2e70
-/
lemma coe_injective :
    Injective (VarTileSetFunction.toFun :
      VarTileSetFunction Y ps α H → {ιₜ : Type*} → Y → TileSet ps ιₜ → α) :=
  fun _ _ ↦ coe_inj.1

/--
@isnad1 id=iff.0h13v.s7.8af65250b372 from=translated src=- shape=60a6a189 vocab=53c523f0
-/
lemma reindex_iff {f : VarTileSetFunction Y ps Prop H} {y : Y} {t : TileSet ps ιᵤ} (e : Eᵤ) :
    f y (t.reindex e) ↔ f y t :=
  by simp

/--
@isnad1 id=iff.1h12v.s6.ad73fe4f616e from=translated src=- shape=3fdcabcb vocab=a6c7eb7d
-/
lemma reindex_iff_of_bijective {f : VarTileSetFunction Y ps Prop H} {y : Y} {t : TileSet ps ιᵤ}
    {e : ιᵤ' → ιᵤ} (h : Bijective e) : f y (t.reindex e) ↔ f y t :=
  by simp [h]

/--
@isnad1 id=iff.1h11v.s7.a5732d2e6c1e from=translated src=- shape=f3e70b56 vocab=2100c095
-/
lemma smul_iff {f : VarTileSetFunction Y ps Prop H} {g : G} {y : Y} {t : TileSet ps ιₜ}
    (hg : g ∈ H) : f (g • y) (g • t) ↔ f y t :=
  by simp [hg]

lemma eq_of_coeSet_eq_of_injective (f : VarTileSetFunction Y ps α H) (y : Y) {t₁ : TileSet ps ιᵤ}
    {t₂ : TileSet ps ιᵤ'} (h : (t₁ : Set (PlacedTile ps)) = t₂) (h₁ : Injective t₁)
    (h₂ : Injective t₂) : f y t₁ = f y t₂ := by
  rw [← TileSet.reindex_equivOfCoeSetEqOfInjective h h₁ h₂]
  exact (reindex_eq _ _ _ _).symm

/--
@isnad1 id=iff.3h12v.s7.46f401931ec9 from=translated src=- shape=4dfcbd7c vocab=5b93cfcc
-/
lemma iff_of_coeSet_eq_of_injective (f : VarTileSetFunction Y ps Prop H) {y : Y}
    {t₁ : TileSet ps ιᵤ} {t₂ : TileSet ps ιᵤ'} (h : (t₁ : Set (PlacedTile ps)) = t₂)
    (h₁ : Injective t₁) (h₂ : Injective t₂) : f y t₁ ↔ f y t₂ := by
  simpa using f.eq_of_coeSet_eq_of_injective y h h₁ h₂

variable (Y ps H) in
/-- The constant `VarTileSetFunction`. -/
protected def const (a : α) : VarTileSetFunction Y ps α H :=
  ⟨fun {ιₜ} ↦ const Y (const (TileSet ps ιₜ) a), by simp, by simp⟩

variable (H) in
/--
@isnad1 id=eq.0h11v.s6.7e43d96060a1 from=translated src=- shape=bfacaaac vocab=90460ca9
-/
@[simp] lemma const_apply (a : α) (y : Y) (t : TileSet ps ιₜ) :
    VarTileSetFunction.const Y ps H a y t = a :=
  rfl

/-- Composing a `VarTileSetFunction` with a function on the result type. -/
protected def comp (f : VarTileSetFunction Y ps α H) (fab : α → β) : VarTileSetFunction Y ps β H :=
  ⟨fun y ↦ fab ∘ (f.toFun y), by simp, fun _ _ hg ↦ by simp [hg]⟩

/--
@isnad1 id=eq.0h13v.s6.48f79fb5ca41 from=translated src=- shape=c3cc71c7 vocab=432d7210
-/
@[simp] lemma comp_apply (f : VarTileSetFunction Y ps α H) (fab : α → β) (y : Y)
    (t : TileSet ps ιₜ) : f.comp fab y t = fab (f y t) :=
  rfl

/--
@isnad1 id=eq.0h12v.s6.db3844e96781 from=translated src=- shape=b8333046 vocab=7eb74091
-/
lemma comp_comp (f : VarTileSetFunction Y ps α H) (fab : α → β) (fbg : β → γ) :
    f.comp (fbg ∘ fab) = (f.comp fab).comp fbg :=
  rfl

/-- Combining two `VarTileSetFunction`s with a function on their result types. -/
protected def comp₂ (f : VarTileSetFunction Y ps α H) (f' : VarTileSetFunction Y ps β H)
    (fabg : α → β → γ) : VarTileSetFunction Y ps γ H :=
  ⟨fun {ιₜ : Type*} (y : Y) (t : TileSet ps ιₜ) ↦ fabg (f y t) (f' y t),
   by simp,
   fun _ _ hg ↦ by simp [hg]⟩

/--
@isnad1 id=eq.0h15v.s7.0c8aaa095685 from=translated src=- shape=f6717ab0 vocab=8ee67059
-/
@[simp] lemma comp₂_apply (f : VarTileSetFunction Y ps α H) (f' : VarTileSetFunction Y ps β H)
    (fabg : α → β → γ) (y : Y) (t : TileSet ps ιₜ) : f.comp₂ f' fabg y t = fabg (f y t) (f' y t) :=
  rfl

/-- Converting a `VarTileSetFunction Y ps α H` to one using a subgroup of `H`. -/
protected def ofLE (f : VarTileSetFunction Y ps α H) {H' : Subgroup G} (h : H' ≤ H) :
    VarTileSetFunction Y ps α H' :=
  ⟨f.toFun, by simp, fun _ _ hg ↦ by simp [SetLike.le_def.1 h hg]⟩

/--
@isnad1 id=eq.1h12v.s7.37348a3a80ed from=translated src=- shape=e115e193 vocab=dd02f658
-/
@[simp] lemma ofLE_apply (f : VarTileSetFunction Y ps α H) {H' : Subgroup G} (h : H' ≤ H)
    (y : Y) (t : TileSet ps ιₜ) : f.ofLE h y t = f y t :=
  rfl

variable (Y ps) in
/--
@isnad1 id=eq.1h9v.s6.b8fa6a1cd9a9 from=translated src=- shape=ceace9ba vocab=91b74804
-/
@[simp] lemma ofLE_const (a : α) {H' : Subgroup G} (h : H' ≤ H) :
    (VarTileSetFunction.const Y ps H a).ofLE h = VarTileSetFunction.const Y ps H' a :=
  rfl

/--
@isnad1 id=eq.1h11v.s7.cd652b6ec05a from=translated src=- shape=382ad7c7 vocab=b81befd4
-/
lemma ofLE_comp (f : VarTileSetFunction Y ps α H) (fab : α → β) {H' : Subgroup G} (h : H' ≤ H) :
    (f.comp fab).ofLE h = (f.ofLE h).comp fab :=
  rfl

/--
@isnad1 id=eq.1h13v.s7.f74a7746e1bc from=translated src=- shape=15b1be99 vocab=09d5a576
-/
lemma ofLE_comp₂ (f : VarTileSetFunction Y ps α H) (f' : VarTileSetFunction Y ps β H)
    (fabg : α → β → γ) {H' : Subgroup G} (h : H' ≤ H) :
    (f.comp₂ f' fabg).ofLE h = (f.ofLE h).comp₂ (f'.ofLE h) fabg :=
  rfl

/-- Converting a `VarTileSetFunction Y ps α H`, acting at `y`, to a
`TileSetFunction ps α (H ⊓ MulAction.stabilizer G y)`. -/
def toTileSetFunction (f : VarTileSetFunction Y ps α H) (y : Y) :
    TileSetFunction ps α (H ⊓ MulAction.stabilizer G y) :=
  ⟨f.toFun y,
   by simp,
   fun {ιₜ} {g} t hg ↦ by
     nth_rewrite 1 [← MulAction.mem_stabilizer_iff.1 (Subgroup.mem_inf.1 hg).2]
     rw [smul_eq _ _ _ (Subgroup.mem_inf.1 hg).1]⟩

/--
@isnad1 id=eq.0h11v.s6.5e90a0254a80 from=translated src=- shape=c43c9df3 vocab=62815606
-/
@[simp] lemma toTileSetFunction_apply (f : VarTileSetFunction Y ps α H) (y : Y)
    (t : TileSet ps ιₜ) : f.toTileSetFunction y t = f y t :=
  rfl

variable (ps H) in
/--
@isnad1 id=eq.0h9v.s6.4d3aa3d153d4 from=translated src=- shape=bb654c80 vocab=a6fa2cb6
-/
@[simp] lemma toTileSetFunction_const (a : α) (y : Y) :
    (VarTileSetFunction.const Y ps H a).toTileSetFunction y = TileSetFunction.const ps _ a :=
  rfl

/--
@isnad1 id=eq.0h11v.s7.d751dd9b5051 from=translated src=- shape=40e021af vocab=58dc4adf
-/
lemma toTileSetFunction_comp (f : VarTileSetFunction Y ps α H) (fab : α → β) (y : Y) :
    (f.comp fab).toTileSetFunction y = (f.toTileSetFunction y).comp fab :=
  rfl

/--
@isnad1 id=eq.0h13v.s7.f06ceec0d677 from=translated src=- shape=81899201 vocab=5f4a10a6
-/
lemma toTileSetFunction_comp₂ (f : VarTileSetFunction Y ps α H) (f' : VarTileSetFunction Y ps β H)
    (fabg : α → β → γ) (y : Y) : (f.comp₂ f' fabg).toTileSetFunction y =
      (f.toTileSetFunction y).comp₂ (f'.toTileSetFunction y) fabg :=
  rfl

end VarTileSetFunction

namespace TileSetFunction

variable (Y) in
/-- Converting a `TileSetFunction ps α H` to a `VarTileSetFunction Y ps α H` that ignores its
first argument. -/
def toVarTileSetFunction (f : TileSetFunction ps α H) : VarTileSetFunction Y ps α H :=
  ⟨fun {ιₜ} ↦ const Y f.toFun, by simp, fun _ _ hg ↦ by simp [hg]⟩

/--
@isnad1 id=eq.0h11v.s6.cf36cbb0d83c from=translated src=- shape=3c7f2a9e vocab=688a89cc
-/
@[simp] lemma toVarTileSetFunction_apply (f : TileSetFunction ps α H) (y : Y) (t : TileSet ps ιₜ) :
    f.toVarTileSetFunction Y y t = f t :=
  rfl

variable (Y ps H) in
/--
@isnad1 id=eq.0h8v.s6.f7cb915f302a from=translated src=- shape=5c568ddb vocab=eacd08b7
-/
@[simp] lemma toVarTileSetFunction_const (a : α) :
    (TileSetFunction.const ps H a).toVarTileSetFunction Y = VarTileSetFunction.const Y ps H a :=
  rfl

variable (Y) in
/--
@isnad1 id=eq.0h10v.s6.e454eb66cce8 from=translated src=- shape=92fb33f4 vocab=5a29c3ca
-/
lemma toVarTileSetFunction_comp (f : TileSetFunction ps α H) (fab : α → β) :
    (f.comp fab).toVarTileSetFunction Y = (f.toVarTileSetFunction Y).comp fab :=
  rfl

variable (Y) in
/--
@isnad1 id=eq.0h12v.s7.2b53ec3028c5 from=translated src=- shape=dc686061 vocab=497e45dd
-/
lemma toVarTileSetFunction_comp₂ (f : TileSetFunction ps α H) (f' : TileSetFunction ps β H)
    (fabg : α → β → γ) : (f.comp₂ f' fabg).toVarTileSetFunction Y =
      (f.toVarTileSetFunction Y).comp₂ (f'.toVarTileSetFunction Y) fabg :=
  rfl

variable (Y) in
/--
@isnad1 id=eq.1h9v.s7.b5490fdcdbe8 from=translated src=- shape=1d88bba6 vocab=7eaf5712
-/
lemma toVarTileSetFunction_ofLE (f : TileSetFunction ps α H) {H' : Subgroup G} (h : H' ≤ H) :
    (f.ofLE h).toVarTileSetFunction Y = (f.toVarTileSetFunction Y).ofLE h :=
  rfl

/--
@isnad1 id=eq.0h9v.s8.87ed3c845a6e from=translated src=- shape=bb41e7ad vocab=afef738c
-/
@[simp] lemma toVarTileSetFunction_toTileSetFunction (f : TileSetFunction ps α H) (y : Y) :
    (f.toVarTileSetFunction Y).toTileSetFunction y = f.ofLE inf_le_left :=
  rfl

end TileSetFunction

end DiscreteTiling
