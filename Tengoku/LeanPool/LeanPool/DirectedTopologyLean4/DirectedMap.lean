/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.DirectedSpace

/-!
# LeanPool.DirectedTopologyLean4.DirectedMap
-/

@[expose] public section

/-
  # Definition of directed maps
  This file defines the directed map between two directed spaces `X` and `Y` :
  it is a continuous map from `X` to `Y` that is also `Directed`, i.e. it maps any dipath in `X` to
  a dipath in `Y`.
  We give the definitions of:
  * Constant maps
  * Identities
  * Composition of directed maps
-/

namespace DirectedMap

/-- A continuous map between two directed spaces is `Directed` if it maps dipaths to dipaths. -/
def Directed {α β : Type*} [DirectedSpace α] [DirectedSpace β] (f : C(α, β)) : Prop :=
  ∀ ⦃x y : α⦄ (γ : Path x y), IsDipath γ → IsDipath (γ.map f.continuous_toFun)

end DirectedMap

/-- Define the type of a directed map -/
structure DirectedMap (α β : Type*) [DirectedSpace α] [DirectedSpace β]
    extends ContinuousMap α β where
  protected directed_toFun : DirectedMap.Directed toContinuousMap

/-- Notation `D(X,Y)` for directed maps from `X` to `Y` -/
notation "D("α","β")" => DirectedMap α β

section

/-- Type class for the bundled directed maps from `α` to `β`. -/
class DirectedMapClass (F : Type*) (α β : outParam <| Type*) [DirectedSpace α] [DirectedSpace β]
  [FunLike F α β] : Prop extends ContinuousMapClass F α β where
  /-- Each element of the class is directed when viewed as a continuous map. -/
  map_directed (f : F) : DirectedMap.Directed (f : C(α, β))

end

export DirectedMapClass (map_directed)

section DirectedMapClass

variable {F α β : Type*} [DirectedSpace α] [DirectedSpace β] [FunLike F α β]
    [hF : DirectedMapClass F α β]
/-- Coerce a member of a `DirectedMapClass` to the bundled directed map type `D(α, β)`. -/
@[coe] def toDirectedMap (f : F) : D(α,β) := ⟨f, map_directed f⟩
instance : CoeTC F D(α,β) := ⟨toDirectedMap⟩

end DirectedMapClass

variable {α β γ δ : Type*} [DirectedSpace α] [DirectedSpace β] [DirectedSpace γ] [DirectedSpace δ]

namespace DirectedMap

instance instFunLike : FunLike D(α,β) α β where
  coe := fun f => f.toFun
  coe_injective f g h := by
    obtain ⟨⟨_, _⟩, _⟩ := f
    obtain ⟨⟨_, _⟩, _⟩ := g
    congr

/--
@isnad1 id=directed.0h2v.s4.fbfcfd7e99b3 from=translated src=- shape=7a820c7c vocab=b79ff941
-/
instance toDirectedMapClass : DirectedMapClass D(α,β) α β where
  map_continuous := fun f => f.continuous_toFun
  map_directed := fun f => f.directed_toFun

/-- Helper instance for when there's too many metavariables to apply `FunLike.hasCoeToFun` directly.
-/
instance : CoeFun (D(α,β)) fun _ => α → β := DFunLike.toCoeFun

/-- A directed map can be coerced into a continuous map -/
instance : Coe D(α,β) C(α, β) := ⟨fun f => f.toContinuousMap⟩

/--
@isnad1 id=eq.0h3v.s5.bbab49df6a0d from=translated src=- shape=c9ede0ca vocab=165fb5c6
-/
@[simp] lemma toFun_eq_coe {f : D(α,β)} : f.toFun = (f : α → β) := rfl
/--
@isnad1 id=eq.0h3v.s6.014c3aa6f742 from=translated src=- shape=fe41b201 vocab=6827d5f3
-/
@[simp] lemma coe_to_continuous_map (f : D(α,β)) : ⇑f.toContinuousMap = f := rfl
/--
@isnad1 id=eq.0h4v.s5.dd1f5bbe6dc0 from=translated src=- shape=681aa3ba vocab=6e2c08af
-/
@[simp] protected lemma coe_coe {F : Type*} [FunLike F α β] [DirectedMapClass F α β] (f : F)
    : ⇑(f : D(α,β)) = f := rfl

/--
@isnad1 id=eq.1h4v.s6.f676e96935bd from=translated src=- shape=632a3698 vocab=c84b2c49
-/
@[ext] theorem ext {f g : D(α,β)} (h : ∀ x, f x = g x) : f = g := DFunLike.ext f g h

variable (α)

/-- The identity map is directed -/
protected def id : D(α,α) where
  toFun := id
  directed_toFun := fun x y γ γ_path => γ_path

/--
@isnad1 id=eq.0h1v.s4.fa4bc1167589 from=translated src=- shape=f3fa249b vocab=f4fc4dc1
-/
@[simp] lemma coe_id : ⇑(DirectedMap.id α) = id := rfl

/-- Constant maps are directed -/
def const (b : β) : D(α,β) where
  toFun := fun _ : α => b
  directed_toFun := fun x y γ _ => isDipath_constant b

/--
@isnad1 id=eq.0h3v.s5.2170243e47e3 from=translated src=- shape=6e3123bb vocab=82b5c3b7
-/
@[simp] lemma coe_const (b : β) : ⇑(const α b) = Function.const α b := rfl

variable {α}

/-- The composition of directed maps is directed -/
def comp (f : D(β,γ)) (g : D(α,β)) : D(α,γ) where
  toFun := f ∘ g
  directed_toFun := fun x y p hp => f.directed_toFun (p.map g.continuous_toFun)
      (g.directed_toFun p hp)

/--
@isnad1 id=eq.0h2v.s4.3eb8b152d294 from=translated src=- shape=1233aa71 vocab=55338bfa
-/
@[simp] lemma id_apply (a : α) : DirectedMap.id α a = a := rfl
/--
@isnad1 id=eq.0h4v.s5.fff6dfca8539 from=translated src=- shape=37d4f185 vocab=f82f0f8b
-/
@[simp] lemma const_apply (b : β) (a : α) : const α b a = b := rfl
/--
@isnad1 id=eq.0h5v.s6.300941e93a72 from=translated src=- shape=610af539 vocab=8bb53f43
-/
@[simp] lemma coe_comp (f : D(β,γ)) (g : D(α,β)) : ⇑(f.comp g) = f ∘ g := rfl
/--
@isnad1 id=eq.0h6v.s6.c8f661c8b948 from=translated src=- shape=80d14110 vocab=00e8476a
-/
@[simp] lemma comp_apply (f : D(β,γ)) (g : D(α,β)) (a : α) : f.comp g a = f (g a) := rfl
/--
@isnad1 id=eq.0h7v.s6.740138b61c5b from=translated src=- shape=8fca5d78 vocab=d19a9749
-/
@[simp] lemma comp_assoc (f : D(γ,δ)) (g : D(β,γ)) (h : D(α,β)) :
  (f.comp g).comp h = f.comp (g.comp h) := rfl
/--
@isnad1 id=eq.0h3v.s5.e82ecd2f58b2 from=translated src=- shape=cf0f0d7a vocab=df3984fd
-/
@[simp] lemma id_comp (f : D(α,β)) : (DirectedMap.id β).comp f = f := ext fun _ => rfl
/--
@isnad1 id=eq.0h3v.s5.dbbec2dacec1 from=translated src=- shape=61ad44b3 vocab=df3984fd
-/
@[simp] lemma comp_id (f : D(α,β)) : f.comp (DirectedMap.id α) = f := ext fun _ => rfl
/--
@isnad1 id=eq.0h5v.s5.9faa8d4d48f0 from=translated src=- shape=ea57fd8d vocab=101e99dd
-/
@[simp] lemma const_comp (c : γ) (f : D(α,β)) : (const β c).comp f = const α c
    := ext <| fun _ => rfl
/--
@isnad1 id=eq.0h5v.s6.68910e88ac70 from=translated src=- shape=2ef182f2 vocab=1395b1a6
-/
@[simp] lemma comp_const (f : D(β,γ)) (b : β) : f.comp (const α b) = const α (f b)
    := ext <| fun _ => rfl

/--
@isnad1 id=injectiv.0h2v.s5.b239dc923279 from=translated src=- shape=0eccae72 vocab=61409e09
-/
lemma coe_injective : @Function.Injective D(α,β) (α → β) (↑) :=
  fun f g h => by cases f; cases g; congr; exact ContinuousMap.ext (congrFun h)

end DirectedMap
