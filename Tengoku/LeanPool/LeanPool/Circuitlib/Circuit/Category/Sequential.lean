/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Tengoku.LeanPool.LeanPool.Circuitlib.Circuit.Wires
public import Tengoku

/-! # Sequential circuit category

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

@[expose] public section

namespace Circuit

/-- Category of sequential circuits. -/
structure SequentialCircuitCategory (V : Type*) (G : Type*) where of (V) (G) ::
  /-- The number of wires of this object. -/
  obj : ℕ

attribute [inline, simp] SequentialCircuitCategory.obj

@[simp]
instance : OfNat (SequentialCircuitCategory V G) n where
  ofNat := .of V G n

namespace SequentialCircuitCategory

/-- A stream of values, i.e. an infinite sequence indexed by time. -/
@[inline]
def Stream := Stream'

instance [Preorder α] : Preorder (Stream α) where
  le xs ys := (xs.zip (fun x y => (x, y)) ys).All ((fun (x, y) => x <= y))
  le_refl _ _ := le_refl _
  le_trans _ _ _ h₁ h₂ i := le_trans (h₁ i) (h₂ i)

/-- Map a function over a stream pointwise. -/
abbrev Stream.map {α : Type*} {β : Type*} : (α → β) → Stream α → Stream β := Stream'.map

/--
@isnad1 id=eq.0h5v.s4.96de4d39b21c from=translated src=- shape=2f12060e vocab=384af5d3
-/
@[simp]
lemma Stream'.map_apply (f : α → β) (s : Stream' α) (t : ℕ) :
    Stream'.map f s t = f (s t) := rfl

universe u v

variable {V : Type v} {G : Type u}

/-- A stream function is causal if the output at time `t` depends only on inputs up to time `t`. -/
def Causal (f : Stream α → Stream β) : Prop :=
  ∀ (x y : Stream α) (t : ℕ), (∀ s, s ≤ t → x s = y s) → f x t = f y t

/-- Homomorphism. -/
def Hom (V : Type v) [Preorder V] (I O : SequentialCircuitCategory V G) :=
  { f : Stream (Wires V I.obj) → Stream (Wires V O.obj) // Monotone f ∧ Causal f }

/-- The underlying identity wire-function. -/
@[inline, simp]
def idVal : Stream (Wires V n) → Stream (Wires V n) := fun x => x

variable [Preorder V]

/--
@isnad1 id=monotone.0h2v.s5.3f608d0170da from=translated src=- shape=88b0cf79 vocab=67ddba7e
-/
@[simp]
lemma id_monotone : Monotone (idVal (V:=V) (n:=n)) := monotone_id

omit [Preorder V] in
/--
@isnad1 id=causal.0h2v.s3.89d3617357f7 from=translated src=- shape=5ba35046 vocab=1e01f9b3
-/
@[simp]
lemma id_causal : Causal (idVal (V:=V) (n:=n)) := fun _ _ t h => h t le_rfl

/-- The identity morphism. -/
@[inline, simp]
def id : SequentialCircuitCategory.Hom V X X := ⟨idVal, ⟨id_monotone, id_causal⟩⟩

open CategoryTheory

@[inline, simp]
instance : Category.{v} (SequentialCircuitCategory V G) where
  Hom := Hom V
  id _ := id
  comp f g := ⟨g.val ∘ f.val,
    ⟨Monotone.comp g.property.1 f.property.1,
     fun x y t h => g.property.2 _ _ t
      fun s hs => f.property.2 x y s
        fun s' hs' => h s' (le_trans hs' hs)⟩⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

/-- The monoidal product of two objects, adding their wire counts. -/
@[inline, simp]
abbrev tensorObj (X Y : SequentialCircuitCategory V G) : SequentialCircuitCategory V G :=
  .of V G (X.obj + Y.obj)

omit [Preorder V] in
/--
@isnad1 id=eq.0h4v.s5.7f63ff727449 from=translated src=- shape=7268f4cd vocab=1a6236e8
-/
lemma tensorHom_val_add
    {X₁ X₂ : SequentialCircuitCategory V G} :
    min X₁.obj (X₁.obj + X₂.obj) = X₁.obj := by simp

omit [Preorder V] in
/--
@isnad1 id=eq.0h4v.s5.e876b23c33d5 from=translated src=- shape=53446b24 vocab=3700bfd7
-/
lemma tensorHom_val_sub
    {X₁ X₂ : SequentialCircuitCategory V G} :
    X₁.obj + X₂.obj - X₁.obj = X₂.obj := by simp

/-- The underlying wire-function of the monoidal product of two morphisms. -/
@[inline, simp]
abbrev tensorHomVal
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂)
    (v : Stream (Wires V (X₁.obj + X₂.obj))) :
    Stream (Wires V (Y₁.obj + Y₂.obj)) :=
  Stream'.zip (fun a b => a.append b)
    (f.val (Stream'.map (fun w => (w.take X₁.obj).cast tensorHom_val_add) v))
    (g.val (Stream'.map (fun w => (w.drop X₁.obj).cast tensorHom_val_sub) v))

omit [Preorder V] in
/--
@isnad1 id=eq.0h5v.s7.549c1811572e from=translated src=- shape=a73657d1 vocab=43e85e0a
-/
lemma tensorHom_take
    {X₁ X₂ : SequentialCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj)) :
    (a.take X₁.obj).cast tensorHom_val_add =
    Vector.ofFn fun i => a.get (Fin.castAdd X₂.obj i) := by
  unfold Wires at a
  apply Wires.ext
  intro i
  simp [Vector.get]
  rfl

/-- The first projection used when tensoring sequential morphisms. -/
@[inline, simp]
abbrev tensorHomEq' {X₁ X₂ : SequentialCircuitCategory V G} (w : Vector V (X₁.obj + X₂.obj)) :=
  Vector.ofFn fun i ↦ Vector.get w (Fin.castAdd X₂.obj i)

/--
@isnad1 id=eq.0h8v.s7.25f0ef972118 from=translated src=- shape=bcdd7991 vocab=7abb26da
-/
lemma tensorHom_eq
    {X₁ Y₁ X₂ : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (f : X₁ ⟶ Y₁)
    (t : ℕ) :
    (f.val (Stream'.map tensorHomEq' v) t).toArray.size = Y₁.obj :=
  (f.val _ t).size_toArray

/--
@isnad1 id=eq.0h11v.s8.94254c635519 from=translated src=- shape=624a48ee vocab=e8c3825e
-/
lemma tensorHom_eq_left
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (t : ℕ) (j : Fin Y₁.obj)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    ((tensorHomVal f g v).get t).get (Fin.castAdd Y₂.obj j) =
    (f.val (Stream'.map tensorHomEq' v) t).get j := by
  simp only [tensorHom_take, tensorHomVal, Stream'.zip, Stream'.get,
    Wires.get_append_left]
  rfl

/--
@isnad1 id=eq.0h11v.s8.35367728d4d7 from=translated src=- shape=db6fcfe9 vocab=9dd98b21
-/
lemma tensorHom_eq_right
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (t : ℕ) (j : Fin Y₂.obj)
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    ((tensorHomVal f g v).get t).get (Fin.natAdd Y₁.obj j) =
    (g.val (Stream'.map (fun w =>
      Vector.ofFn fun i ↦ Vector.get w (Fin.natAdd X₁.obj i)) v) t).get j := by
  have hdrop : ∀ (a : Wires V (X₁.obj + X₂.obj)),
      (a.drop X₁.obj).cast tensorHom_val_sub =
      Vector.ofFn fun i => a.get (Fin.natAdd X₁.obj i) := fun a => by
    unfold Wires at a
    apply Wires.ext
    intro i
    simp [Vector.get]
    rfl
  simp only [tensorHom_take, hdrop, tensorHomVal, Stream'.zip, Stream'.get,
    Wires.get_append_right]
  rfl

/--
@isnad1 id=monotone.0h8v.s7.8dad129fcfae from=translated src=- shape=fe0c2b90 vocab=d0823c42
-/
@[simp]
lemma tensorHom_monotone
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    Monotone (tensorHomVal f g) := fun v₁ v₂ h t i =>
  Fin.addCases
    (fun j => by
      have lhs_eq := tensorHom_eq_left v₁ t j f g
      have rhs_eq := tensorHom_eq_left v₂ t j f g
      rw [lhs_eq, rhs_eq]
      exact f.property.1 (fun t' k => by
        simp only [Stream'.map, Stream'.get, Wires.get_ofFn]
        exact h t' (k.castAdd _)) t j)
    (fun j => by
      have lhs_eq := tensorHom_eq_right v₁ t j f g
      have rhs_eq := tensorHom_eq_right v₂ t j f g
      rw [lhs_eq, rhs_eq]
      exact g.property.1 (fun t' k => by
        simp only [Stream'.map, Stream'.get, Wires.get_ofFn]
        exact h t' (k.natAdd _)) t j)
    i

/--
@isnad1 id=causal.0h8v.s6.fa074d53c03d from=translated src=- shape=1daec792 vocab=4e681d02
-/
@[simp]
lemma tensorHom_causal
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    Causal (tensorHomVal f g) := fun x y t h => by
  simp only [tensorHomVal]
  have hf : f.val (Stream'.map (fun w => (w.take X₁.obj).cast tensorHom_val_add) x) t =
      f.val (Stream'.map (fun w => (w.take X₁.obj).cast tensorHom_val_add) y) t :=
    f.property.2 _ _ t fun s hs =>
      congrArg (fun w : Wires V (X₁.obj + X₂.obj) =>
        (w.take X₁.obj).cast tensorHom_val_add) (h s hs)
  have hg : g.val (Stream'.map (fun w => (w.drop X₁.obj).cast tensorHom_val_sub) x) t =
      g.val (Stream'.map (fun w => (w.drop X₁.obj).cast tensorHom_val_sub) y) t :=
    g.property.2 _ _ t fun s hs =>
      congrArg (fun w : Wires V (X₁.obj + X₂.obj) =>
        (w.drop X₁.obj).cast tensorHom_val_sub) (h s hs)
  unfold Stream'.zip Stream'.get
  rw [hf, hg]

/-- The monoidal product of two morphisms. -/
@[inline, simp]
abbrev tensorHom
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  ⟨tensorHomVal f g, ⟨tensorHom_monotone f g, tensorHom_causal f g⟩⟩

/-- The underlying wire-function of the forward direction of a wire-count isomorphism. -/
@[simp]
abbrev isoHomVal (h : n = m) : Stream (Wires V n) → Stream (Wires V m) :=
  Stream'.map (·.cast h)

/--
@isnad1 id=monotone.1h3v.s5.60f26d6b0711 from=translated src=- shape=1857295c vocab=b778bf80
-/
@[simp]
lemma iso_hom_monotone (h : n = m) : Monotone (isoHomVal (V:=V) h) :=
  fun _ _ hab t i => hab t (i.cast h.symm)

omit [Preorder V] in
/--
@isnad1 id=causal.1h3v.s4.037ecb8efaee from=translated src=- shape=9811dcc9 vocab=7e146d37
-/
@[simp]
lemma iso_hom_causal (h : n = m) : Causal (isoHomVal (V:=V) h) :=
  fun _ _ t heq => congrArg (·.cast h) (heq t le_rfl)

/-- The forward direction of a wire-count isomorphism. -/
@[simp]
abbrev isoHom (h : n = m) :
    { f : Stream (Wires V n) → Stream (Wires V m) // Monotone f ∧ Causal f } :=
  ⟨isoHomVal h, ⟨iso_hom_monotone h, iso_hom_causal h⟩⟩

/-- The underlying wire-function of the inverse direction of a wire-count isomorphism. -/
@[simp]
abbrev isoInvVal (h : n = m) : Stream (Wires V m) → Stream (Wires V n) :=
  Stream'.map (·.cast h.symm)

/--
@isnad1 id=monotone.1h3v.s5.d7aaf36db106 from=translated src=- shape=5bfab985 vocab=f2332f53
-/
lemma iso_inv_monotone (h : n = m) : Monotone (isoInvVal (V:=V) h) :=
  fun _ _ hab t i => hab t (i.cast h)

omit [Preorder V] in
/--
@isnad1 id=causal.1h3v.s4.a59a5d705397 from=translated src=- shape=fcc753df vocab=18b80088
-/
lemma iso_inv_causal (h : n = m) : Causal (isoInvVal (V:=V) h) :=
  fun _ _ t heq => congrArg (·.cast h.symm) (heq t le_rfl)

/-- The inverse direction of a wire-count isomorphism. -/
@[simp]
abbrev isoInv (h : n = m) :
    { f : Stream (Wires V m) → Stream (Wires V n) // Monotone f ∧ Causal f } :=
  ⟨isoInvVal h, ⟨iso_inv_monotone h, iso_inv_causal h⟩⟩

/--
@isnad1 id=eq.1h4v.s6.59b2682841fa from=translated src=- shape=bc0dfa4e vocab=0125f387
-/
@[simp]
lemma iso_hom_inv_id
    (h : n = m) :
    isoHom h ≫ isoInv h = 𝟙 (OfNat.ofNat n : SequentialCircuitCategory V G) :=
  Subtype.ext (funext fun _ => rfl)

/--
@isnad1 id=eq.1h4v.s6.e481529ed2e5 from=translated src=- shape=e3be9b5d vocab=0125f387
-/
lemma iso_inv_hom_id
    (h : n = m) :
    isoInv h ≫ isoHom h = 𝟙 (OfNat.ofNat m : SequentialCircuitCategory V G) :=
  Subtype.ext (funext fun _ => rfl)

omit [Preorder V] in
/--
@isnad1 id=eq.0h4v.s7.7d09cb6db5f8 from=translated src=- shape=88543a94 vocab=b3bbeb9f
-/
@[simp]
lemma id_coe_apply
    [Preorder V]
    (X : SequentialCircuitCategory V G) (v : Stream (Wires V X.obj)) :
    (𝟙 X : Hom V X X).val v = v := rfl

/-- The isomorphism between objects with equal wire counts. -/
@[inline, simp]
def iso
    (h : n = m) :
    SequentialCircuitCategory.of V G n ≅ SequentialCircuitCategory.of V G m :=
  { hom := isoHom h
    inv := isoInv h
    hom_inv_id := iso_hom_inv_id h
    inv_hom_id := iso_inv_hom_id h }

/--
@isnad1 id=eq.0h4v.s6.3df4ea90360d from=translated src=- shape=bd1781b3 vocab=39ff87ac
-/
@[simp]
lemma whisker
    (X Y : SequentialCircuitCategory V G) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (X.tensorObj Y) := by
  apply Subtype.ext
  funext v t
  change (tensorHomVal (𝟙 X) (𝟙 Y) v).get t = v.get t
  apply Wires.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v t j (𝟙 X) (𝟙 Y)]
    simp [CategoryStruct.id, id, idVal, Stream'.map, Stream'.get, Wires.get_ofFn]
  · rw [tensorHom_eq_right v t j (𝟙 X) (𝟙 Y)]
    simp [CategoryStruct.id, id, idVal, Stream'.map, Stream'.get, Wires.get_ofFn]

/-- Left whiskering of a morphism by a fixed object. -/
@[inline, simp]
abbrev whiskerLeft
    (X : SequentialCircuitCategory V G)
    {Y₁ Y₂ : SequentialCircuitCategory V G} :
    (Y₁ ⟶ Y₂) →
    (tensorObj X Y₁ ⟶ tensorObj X Y₂) :=
  tensorHom (𝟙 X)

/-- Right whiskering of a morphism by a fixed object. -/
@[inline, simp]
abbrev whiskerRight
    {X₁ X₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ X₂)
    (Y : SequentialCircuitCategory V G) : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom f (𝟙 Y)

/--
@isnad1 id=eq.0h8v.s7.e142c39ce329 from=translated src=- shape=62a875cd vocab=2688e4aa
-/
@[simp]
lemma tensorHom_def
    {W X Y Z : SequentialCircuitCategory V G} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorHom f g = whiskerRight f Y ≫ whiskerLeft X g := by
  apply Subtype.ext
  funext v t
  change (tensorHomVal f g v).get t =
    (tensorHomVal id g (tensorHomVal f id v)).get t
  apply Wires.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v t j f g, tensorHom_eq_left _ t j id g]
    simp only [id, Stream'.map, idVal, Wires.get_ofFn]
    exact (tensorHom_eq_left v t j f id).symm
  · rw [tensorHom_eq_right v t j f g, tensorHom_eq_right _ t j id g]
    simp only [id]
    have heq : (Stream'.map (fun w =>
        Vector.ofFn fun i ↦ w.get (Fin.natAdd W.obj i)) v) =
      (Stream'.map (fun w =>
        Vector.ofFn fun i ↦ w.get (Fin.natAdd X.obj i))
          (tensorHomVal f ⟨idVal, ⟨id_monotone, id_causal⟩⟩ v)) := by
      funext t'
      apply Wires.ext
      intro k
      simp only [Stream'.map, Wires.get_ofFn]
      have := (tensorHom_eq_right v t' k f (𝟙 Y)).symm
      simp only [CategoryStruct.id, id, idVal, Stream'.map,
        Wires.get_ofFn] at this
      exact this
    exact congrArg (fun s => (g.val s t).get j) heq

/--
@isnad1 id=eq.0h4v.s6.3df4ea90360d from=translated src=- shape=bd1781b3 vocab=39ff87ac
-/
@[simp]
lemma id_tensorHom_id
    (X₁ X₂ : SequentialCircuitCategory V G) :
    tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (X₁.tensorObj X₂) := whisker X₁ X₂

/--
@isnad1 id=eq.0h12v.s7.ea9cb638198f from=translated src=- shape=ec861311 vocab=62437658
-/
@[simp]
lemma tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : SequentialCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply Subtype.ext
  funext v t
  change (tensorHomVal g₁ g₂ (tensorHomVal f₁ f₂ v)).get t =
    (tensorHomVal (f₁ ≫ g₁) (f₂ ≫ g₂) v).get t
  apply Wires.ext
  intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left _ t j g₁ g₂,
        tensorHom_eq_left v t j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp, Function.comp]
    exact congrArg (fun s => (g₁.val s t).get j)
      (funext fun t' => Wires.ext fun k => by
        simp only [Stream'.map, Wires.get_ofFn]
        exact tensorHom_eq_left v t' k f₁ f₂)
  · rw [tensorHom_eq_right _ t j g₁ g₂,
        tensorHom_eq_right v t j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp, Function.comp]
    exact congrArg (fun s => (g₂.val s t).get j)
      (funext fun t' => Wires.ext fun k => by
        simp only [Stream'.map, Wires.get_ofFn]
        exact tensorHom_eq_right v t' k f₁ f₂)

/-- The monoidal unit, the object with no wires. -/
@[inline, simp]
def tensorUnit : SequentialCircuitCategory V G := .of V G 0

omit [Preorder V] in
/--
@isnad1 id=eq.0h5v.s6.0cf3abb6f646 from=translated src=- shape=b6d57b64 vocab=46960c5e
-/
@[simp]
lemma associator_eq
    (X Y Z : SequentialCircuitCategory V G) :
    X.obj + Y.obj + Z.obj = X.obj + (Y.obj + Z.obj) :=
  Nat.add_assoc X.obj Y.obj Z.obj

/-- The associator isomorphism of the monoidal structure. -/
@[inline, simp]
def associator
    (X Y Z : SequentialCircuitCategory V G) :
    (X.tensorObj Y).tensorObj Z ≅ X.tensorObj (Y.tensorObj Z) :=
  iso (associator_eq X Y Z)

/--
@isnad1 id=eq.0h11v.s8.6d0fd80977da from=translated src=- shape=127251c1 vocab=02cdcb17
-/
lemma associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : SequentialCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (Y₁.associator Y₂ Y₃).hom =
      (X₁.associator X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  have hi : i.val < Y₁.obj + (Y₂.obj + Y₃.obj) := i.isLt
  simp only [CategoryStruct.comp, Function.comp, tensorHom,
    tensorHomVal, associator, iso, isoHom, isoHomVal,
    Stream'.map, Stream'.zip, Stream'.get,
    Wires.get_cast_vector, Wires.get_append,
    Wires.get_append_wires_vector, Wires.get_append_vector_wires]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (congr 1 <;>
          first
            | exact Fin.ext (by simp; try omega)
            | (refine congrFun (congrArg _ (funext fun t' => Wires.ext fun k => ?_)) t
               simp only [Stream'.map, Stream'.get, Wires.get_cast,
                 Wires.get_cast_vector, Wires.get_take, Wires.get_take_vector,
                 Wires.get_drop, Wires.get_drop_vector]
               all_goals (refine congrArg _ (Fin.ext ?_); simp; omega)))

/--
@isnad1 id=eq.0h6v.s8.0895b04ad26f from=translated src=- shape=e1e093ba vocab=912d8f2a
-/
lemma pentagon
    (W X Y Z : SequentialCircuitCategory V G) :
    whiskerRight (W.associator X Y).hom Z ≫
      (W.associator (X.tensorObj Y) Z).hom ≫
      whiskerLeft W (X.associator Y Z).hom =
    ((W.tensorObj X).associator Y Z).hom ≫ (W.associator X (Y.tensorObj Z)).hom := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  have hi : i.val < W.obj + (X.obj + (Y.obj + Z.obj)) := i.isLt
  simp only [CategoryStruct.comp, Function.comp,
    tensorHomVal, associator, iso, isoHom, isoHomVal,
    CategoryStruct.id, id, idVal, Stream'.map, Stream'.zip, Stream'.get,
    Wires.get_cast, Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (refine congrArg _ (Fin.ext ?_); simp <;> omega)

omit [Preorder V] in
/--
@isnad1 id=eq.0h3v.s4.46efcee26a21 from=translated src=- shape=44da2d3c vocab=7dbe312b
-/
lemma leftUnitor_eq
    (X : SequentialCircuitCategory V G) :
    (tensorUnit (V:=V) (G:=G)).obj + X.obj = X.obj :=
  Nat.zero_add X.obj

omit [Preorder V] in
/--
@isnad1 id=eq.0h3v.s4.355619c86802 from=translated src=- shape=a2e0ab5c vocab=7dbe312b
-/
lemma rightUnitor_eq
    (X : SequentialCircuitCategory V G) :
    X.obj + (tensorUnit (V:=V) (G:=G)).obj = X.obj :=
  Nat.add_zero X.obj

/-- The left unitor isomorphism of the monoidal structure. -/
@[simp]
abbrev leftUnitor (X : SequentialCircuitCategory V G) : tensorObj tensorUnit X ≅ X :=
  iso (leftUnitor_eq X)

/-- The right unitor isomorphism of the monoidal structure. -/
@[simp]
abbrev rightUnitor (X : SequentialCircuitCategory V G) : tensorObj X tensorUnit ≅ X :=
  iso (rightUnitor_eq X)

/--
@isnad1 id=eq.0h5v.s7.0f11b5c16559 from=translated src=- shape=70b9694c vocab=b7bce495
-/
lemma leftUnitor_naturality
    {X Y : SequentialCircuitCategory V G} (f : X ⟶ Y) :
    whiskerLeft tensorUnit f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  have hi : i.val < Y.obj := i.isLt
  have h0 : (tensorUnit (V := V) (G := G)).obj = 0 := rfl
  simp only [CategoryStruct.comp, Function.comp, tensorHomVal,
    leftUnitor, iso, isoHom, isoHomVal, CategoryStruct.id, id, idVal,
    Stream'.map, Stream'.zip, Stream'.get,
    Wires.get_cast_vector,
    Wires.get_append_vector_wires,
    Wires.get_take]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (congr 1;
          first
            | exact Fin.ext (by rfl)
            | (refine congrFun (congrArg _ (funext fun t' => Wires.ext fun k => ?_)) t
               simp only [Stream'.map, Stream'.get, Wires.get_cast,
                 Wires.get_cast_vector, Wires.get_drop]
               all_goals (refine congrArg _ (Fin.ext ?_); simp)))

/--
@isnad1 id=eq.0h5v.s7.dd6b6fc19876 from=translated src=- shape=6841d722 vocab=01fbd4f7
-/
lemma rightUnitor_naturality
    {X Y : SequentialCircuitCategory V G}
    (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  have hi : i.val < Y.obj := i.isLt
  have h0 : (tensorUnit (V := V) (G := G)).obj = 0 := rfl
  simp only [CategoryStruct.comp, Function.comp, tensorHomVal,
    rightUnitor, iso, isoHom, isoHomVal, CategoryStruct.id, id, idVal,
    Stream'.map, Stream'.zip, Stream'.get,
    Wires.get_cast_vector,
    Wires.get_append_wires_vector,
    Wires.get_drop]
  (split_ifs;
    congr 1;
      first
        | exact Fin.ext (by rfl)
        | (refine congrFun (congrArg _ (funext fun t' => Wires.ext fun k => ?_)) t
           simp only [Stream'.map, Stream'.get, Wires.get_cast,
             Wires.get_cast_vector, Wires.get_take]))

open MonoidalCategory

/--
@isnad1 id=eq.0h4v.s7.64deedc4385a from=translated src=- shape=b9e78d22 vocab=2de1bab9
-/
lemma triangle
    (X Y : SequentialCircuitCategory V G) :
    (associator X tensorUnit Y).hom ≫ whiskerLeft X (leftUnitor Y).hom =
    whiskerRight (rightUnitor X).hom Y := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  have hi : i.val < X.obj + Y.obj := i.isLt
  have h0 : (tensorUnit (V := V) (G := G)).obj = 0 := rfl
  simp only [CategoryStruct.comp, Function.comp,
    tensorHomVal, associator, leftUnitor, rightUnitor, iso, isoHom, isoHomVal,
    CategoryStruct.id, id, idVal, Stream'.map, Stream'.zip, Stream'.get,
    Wires.get_cast, Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    (refine congrArg _ (Fin.ext ?_); simp)

@[inline, simp]
instance : MonoidalCategory.{v} (SequentialCircuitCategory V G) where
  tensorObj
  tensorHom
  whiskerLeft
  whiskerRight
  tensorHom_def
  id_tensorHom_id
  tensorHom_comp_tensorHom
  whiskerLeft_id := whisker
  id_whiskerRight := whisker
  tensorUnit
  associator
  associator_naturality
  leftUnitor
  leftUnitor_naturality
  rightUnitor
  rightUnitor_naturality
  pentagon
  triangle

/--
@isnad1 id=eq.0h4v.s5.a722043159f6 from=translated src=- shape=6ac2c575 vocab=3594bfff
-/
@[simp]
lemma monoidal_tensorObj_obj
    (X Y : SequentialCircuitCategory V G) :
    (X ⊗ Y).obj = X.obj + Y.obj := rfl

/--
@isnad1 id=eq.0h4v.s6.7eebe4f565fb from=translated src=- shape=343ed860 vocab=0702a41e
-/
lemma braiding_hom_eq
    {X Y : SequentialCircuitCategory V G} :
    (X ⊗ Y).obj - X.obj + min X.obj (X ⊗ Y).obj = (Y ⊗ X).obj :=
  by simp

/-- The underlying wire-function of the braiding, swapping two blocks of wires. -/
@[inline, simp]
abbrev braidingHomVal
    (X Y : SequentialCircuitCategory V G) :
    Stream (Wires V (X ⊗ Y).obj) →
    Stream (Wires V (Y ⊗ X).obj) :=
  Stream.map (fun v => ((v.drop X.obj).append (v.take X.obj)).cast braiding_hom_eq)

/--
@isnad1 id=lt.0h5v.s6.f364b4bc2de0 from=translated src=- shape=9813f585 vocab=dde8f652
-/
lemma braiding_hom_lt
    {X Y : SequentialCircuitCategory V G}
    {j : Fin Y.obj} :
    X.obj + ↑j < (X ⊗ Y).obj := by
  simp_all

/--
@isnad1 id=lt.0h5v.s5.acb939be8d99 from=translated src=- shape=251607d3 vocab=18b1d1ef
-/
lemma braiding_hom_ge
    {X Y : SequentialCircuitCategory V G}
    {j : Fin X.obj} :
    ↑j < (X ⊗ Y).obj := by
  change j.val < X.obj + Y.obj
  omega

/--
@isnad1 id=monotone.0h4v.s7.9ab0a33466ef from=translated src=- shape=8ecb36f3 vocab=194830cc
-/
lemma braiding_hom_monotone
    {X Y : SequentialCircuitCategory V G} :
    Monotone (X.braidingHomVal Y) := fun a b hab t i => by
  simp only [braidingHomVal, monoidal_tensorObj_obj, Stream.map, Stream'.map, Stream'.get,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_drop]
  split_ifs <;> exact hab t _

/--
@isnad1 id=causal.0h4v.s6.0e8d00daf777 from=translated src=- shape=131fb8df vocab=719d964d
-/
lemma braiding_hom_causal
    {X Y : SequentialCircuitCategory V G} :
    Causal (X.braidingHomVal Y) := fun _ _ t h =>
  congrArg (fun w : Wires V (X ⊗ Y).obj =>
    ((w.drop X.obj).append (w.take X.obj)).cast braiding_hom_eq) (h t le_rfl)

/-- The braiding morphism, swapping two blocks of wires. -/
@[inline]
def braidingHom (X Y : SequentialCircuitCategory V G) : X ⊗ Y ⟶ Y ⊗ X :=
  ⟨braidingHomVal X Y, ⟨braiding_hom_monotone, braiding_hom_causal⟩⟩

/--
@isnad1 id=eq.0h4v.s7.236058fe15b3 from=translated src=- shape=64bfd792 vocab=3d8f4bac
-/
lemma braiding_hom_inv_id
    {X Y : SequentialCircuitCategory V G} :
    X.braidingHom Y ≫ Y.braidingHom X = 𝟙 (X ⊗ Y) := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  have hi : i.val < X.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, braidingHom, braidingHomVal, id_coe_apply,
    monoidal_tensorObj_obj, Stream.map, Stream'.map, Stream'.get,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (refine congrArg _ (Fin.ext ?_); simp <;> omega)

/-- The braiding isomorphism of the symmetric monoidal structure. -/
@[inline]
def braiding (X Y : SequentialCircuitCategory V G) : X ⊗ Y ≅ Y ⊗ X :=
  { hom := braidingHom X Y
    inv := braidingHom Y X
    hom_inv_id := braiding_hom_inv_id
    inv_hom_id := braiding_hom_inv_id }

/--
@isnad1 id=eq.0h6v.s8.ce18c083ef7f from=translated src=- shape=e38df357 vocab=7651e3a7
-/
lemma braiding_naturality_left
    {X Y : SequentialCircuitCategory V G}
    (f : X ⟶ Y)
    (Z : SequentialCircuitCategory V G) :
    f ▷ Z ≫ (Y.braiding Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  have hi : i.val < Z.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom,
    tensorHomVal, braiding, braidingHom, braidingHomVal,
    monoidal_tensorObj_obj, CategoryStruct.id, id, idVal,
    Stream.map, Stream'.map, Stream'.zip, Stream'.get,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_append_wires_vector, Wires.get_append_vector_wires,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (refine congrArg _ (Fin.ext ?_); simp)
      | (congr 1 <;>
          first
            | exact Fin.ext (by simp; try omega)
            | (refine congrFun (congrArg _ (funext fun t' => Wires.ext fun k => ?_)) t
               simp only [Stream'.map, Stream'.get,
                 Wires.get_cast_vector, Wires.get_append_vector,
                 Wires.get_take, Wires.get_drop, Wires.get_drop_vector]
               all_goals
                 split_ifs <;>
                   first
                     | (exfalso; omega)
                     | (refine congrArg _ (Fin.ext ?_); simp)))

/--
@isnad1 id=eq.0h6v.s8.beb6d945f892 from=translated src=- shape=9f6cec64 vocab=7651e3a7
-/
lemma braiding_naturality_right
    (X : SequentialCircuitCategory V G)
    {Y Z : SequentialCircuitCategory V G}
    (f : Y ⟶ Z) :
    X ◁ f ≫ (X.braiding Z).hom = (braiding X Y).hom ≫ f ▷ X := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  have hi : i.val < Z.obj + X.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom,
    tensorHomVal, braiding, braidingHom, braidingHomVal,
    monoidal_tensorObj_obj, CategoryStruct.id, id, idVal,
    Stream.map, Stream'.map, Stream'.zip, Stream'.get,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_append_wires_vector, Wires.get_append_vector_wires,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (refine congrArg _ (Fin.ext ?_); simp)
      | (congr 1 <;>
          first
            | exact Fin.ext (by simp; try omega)
            | (refine congrFun (congrArg _ (funext fun t' => Wires.ext fun k => ?_)) t
               simp only [Stream'.map, Stream'.get,
                 Wires.get_cast_vector, Wires.get_append_vector,
                 Wires.get_take, Wires.get_take_vector, Wires.get_drop]
               all_goals
                 split_ifs <;>
                   first
                     | (exfalso; omega)
                     | (refine congrArg _ (Fin.ext ?_); simp)))

omit [Preorder V] in
/--
@isnad1 id=lt.1h5v.s5.d228757db833 from=translated src=- shape=aa8d92f5 vocab=b75f8c1a
-/
lemma braiding_add
    {X Y : SequentialCircuitCategory V G}
    (h : ↑i < Y.obj) :
    X.obj + ↑i < X.obj + Y.obj := by omega

/--
@isnad1 id=lt.0h5v.s6.2196f08df67e from=translated src=- shape=485b7397 vocab=5b14ddd0
-/
lemma braiding_sub
    {X Y : SequentialCircuitCategory V G}
    {i : Fin (Y ⊗ X).obj} :
    ↑i - Y.obj < (X ⊗ Y).obj := by
  have : i.val < Y.obj + X.obj := i.isLt
  change i.val - Y.obj < X.obj + Y.obj
  omega

omit [Preorder V] in
/--
@isnad1 id=not.0h5v.s5.7b24d7db8c97 from=translated src=- shape=4c79ab04 vocab=7402fb56
-/
lemma braiding_get_ge
    {X Y : SequentialCircuitCategory V G}
    {j : Fin X.obj} :
    ¬Y.obj + ↑j < Y.obj := by omega

omit [Preorder V] in
/--
@isnad1 id=eq.1h6v.s5.d8044b38e447 from=translated src=- shape=6fcb4b00 vocab=b9b30d05
-/
lemma iso_hom_get
    (h : n = m) (v : Stream (Wires V n)) (t : ℕ) (i : Fin m) :
    (isoHomVal (V:=V) h v t).get i = (v t).get ⟨i.val, h ▸ i.isLt⟩ := by
  simp only [isoHomVal, Stream'.map, Stream'.get, Wires.get_cast]

/--
@isnad1 id=eq.0h7v.s8.bba3b88ad286 from=translated src=- shape=dcdaaf37 vocab=0e0b2b66
-/
lemma braiding_get
    (X Y : SequentialCircuitCategory V G)
    (v : Stream (Wires V (X ⊗ Y).obj))
    (t : ℕ)
    (i : Fin (Y ⊗ X).obj) :
    (X.braidingHomVal Y v t).get i =
      if h : i.val < Y.obj
      then (v t).get ⟨X.obj + i.val, braiding_add h⟩
      else (v t).get ⟨i.val - Y.obj, braiding_sub⟩ := by
  have hi : i.val < Y.obj + X.obj := i.isLt
  simp only [braidingHomVal, monoidal_tensorObj_obj, Stream.map, Stream'.map, Stream'.get,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_drop]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (refine congrArg _ (Fin.ext ?_); simp)

/--
@isnad1 id=eq.0h11v.s9.8567cb7d3812 from=translated src=- shape=bccf6475 vocab=449387e3
-/
lemma tensorHom_get
    {X₁ Y₁ X₂ Y₂ : SequentialCircuitCategory V G}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂)
    (v : Stream (Wires V (X₁.obj + X₂.obj)))
    (t : ℕ)
    (i : Fin (Y₁.obj + Y₂.obj)) :
    (tensorHomVal f g v t).get i =
    if h : i.val < Y₁.obj
    then (f.val (Stream'.map tensorHomEq' v) t).get ⟨i.val, h⟩
    else (g.val (Stream'.map (fun w =>
      Vector.ofFn fun k => w.get (Fin.natAdd X₁.obj k)) v) t).get
      ⟨i.val - Y₁.obj, by omega⟩ := by
  change ((tensorHomVal f g v).get t).get i = _
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left]
    simp only [Fin.val_castAdd, dite_eq_left j.isLt]
  · rw [tensorHom_eq_right]
    simp only [Fin.val_natAdd, dite_eq_right (show ¬(Y₁.obj + j.val < Y₁.obj) from by omega)]
    congr 1
    exact Fin.ext (by simp)

omit [Preorder V] in
/--
@isnad1 id=eq.0h7v.s6.7c3b7a56d9ce from=translated src=- shape=a37b0e8f vocab=0dde24f0
-/
lemma tensorObj_size_eq_forward
    {X Y Z : SequentialCircuitCategory V G}
    (v : Stream (Wires V ((X.tensorObj Y).tensorObj Z).obj)) :
    (v t).toArray.size = ((X.tensorObj Y).tensorObj Z).obj := (v t).size_toArray

/--
@isnad1 id=eq.0h5v.s10.9d06e8de02bc from=translated src=- shape=69d5725b vocab=6ba78b2d
-/
lemma hexagon_forward
    (X Y Z : SequentialCircuitCategory V G) :
    (α_ X Y Z).hom ≫ (X.braiding (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
    (X.braiding Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (X.braiding Z).hom := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  have hi : i.val < Y.obj + (Z.obj + X.obj) := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.associator, whiskerLeft,
    whiskerRight, tensorHom, tensorHomVal, associator, iso, isoHom, isoHomVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj, CategoryStruct.id, id, idVal,
    Stream.map, Stream'.map, Stream'.zip, Stream'.get,
    Wires.get_cast, Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (refine congrArg _ (Fin.ext ?_); simp <;> omega)

omit [Preorder V] in
/--
@isnad1 id=eq.0h7v.s6.b19b53f8e565 from=translated src=- shape=0f951318 vocab=0dde24f0
-/
lemma tensorObj_size_eq_reverse
    {X Y Z : SequentialCircuitCategory V G}
    (v : Stream (Wires V (X.tensorObj (Y.tensorObj Z)).obj)) :
    (v t).toArray.size = (X.tensorObj (Y.tensorObj Z)).obj := (v t).size_toArray

/--
@isnad1 id=eq.0h5v.s10.611b4e244cd8 from=translated src=- shape=828e7174 vocab=724d07ba
-/
lemma hexagon_reverse
    (X Y Z : SequentialCircuitCategory V G) :
    (α_ X Y Z).inv ≫ ((X ⊗ Y).braiding Z).hom ≫ (α_ Z X Y).inv =
    X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  have hi : i.val < Z.obj + X.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, MonoidalCategoryStruct.associator, whiskerLeft,
    whiskerRight, tensorHom, tensorHomVal, associator, iso, isoInv, isoInvVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj, CategoryStruct.id, id, idVal,
    Stream.map, Stream'.map, Stream'.zip, Stream'.get,
    Wires.get_cast, Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (refine congrArg _ (Fin.ext ?_); simp; omega)

/--
@isnad1 id=eq.0h4v.s8.6dd932d7ab76 from=translated src=- shape=153897f2 vocab=1edbf16a
-/
lemma symmetry
    (X Y : SequentialCircuitCategory V G) :
    (X.braiding Y).hom ≫ (Y.braiding X).hom = 𝟙 (X ⊗ Y) := by
  change (X.braidingHom Y) ≫ (Y.braidingHom X) = 𝟙 (tensorObj X Y)
  apply Subtype.ext
  funext v t
  apply Wires.ext
  intro i
  simp only [CategoryStruct.comp, Function.comp, braidingHom, braiding_get]
  have htXY : (X ⊗ Y).obj = X.obj + Y.obj := rfl
  split <;> split <;>
  exact congrArg (v t).get (Fin.ext (by simp only []; omega))

@[inline, simp]
instance : SymmetricCategory (SequentialCircuitCategory V G) where
  braiding
  braiding_naturality_left
  braiding_naturality_right
  hexagon_forward
  hexagon_reverse
  symmetry

end SequentialCircuitCategory

end Circuit
