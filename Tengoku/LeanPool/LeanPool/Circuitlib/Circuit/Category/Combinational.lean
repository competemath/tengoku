/-
Copyright (c) 2026 Matt Hunzinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Matt Hunzinger
-/
module

public import Tengoku.LeanPool.LeanPool.Circuitlib.Circuit.Category.Basic
public import Tengoku

/-! # Combinational circuit category

## References

* [Ghica, Kaye, and Sprunger, *A Complete Theory of Sequential Digital Circuits*][Ghica2025]

-/

@[expose] public section

namespace Circuit

/-- Category of combinational circuits. -/
structure CombinationalCircuitCategory (V : Type*) (G : Type*) where of (V) (G) ::
  /-- The number of wires of this object. -/
  obj : ℕ

attribute [inline, simp] CombinationalCircuitCategory.obj

@[simp]
instance : OfNat (CombinationalCircuitCategory V G) n where
  ofNat := .of V G n

namespace CombinationalCircuitCategory

universe u v

variable {V : Type v} {G : Type u}

/-- Homomorphism. -/
def Hom (V : Type v) [Preorder V] (I O : CombinationalCircuitCategory V G) :=
  { f : Wires V I.obj → Wires V O.obj // Monotone f }

/-- The underlying identity wire-function. -/
@[inline, simp]
def idVal : Wires V n → Wires V n := fun x => x

/--
@isnad1 id=monotone.0h2v.s4.18830464422e from=translated src=- shape=3b1fda34 vocab=344ed39b
-/
@[simp]
lemma id_monotone [Preorder V] : Monotone (idVal (V:=V) (n:=n)) := monotone_id

/-- The identity morphism. -/
@[inline, simp]
def id [Preorder V] : CombinationalCircuitCategory.Hom V X X := ⟨idVal, id_monotone⟩

open CategoryTheory

@[inline, simp]
instance [Preorder V] : Category.{v} (CombinationalCircuitCategory V G) where
  Hom := Hom V
  id _ := id
  comp f g := ⟨g.val ∘ f.val, Monotone.comp g.property f.property⟩
  id_comp _ := by rfl
  comp_id _ := by rfl
  assoc _ _ _ := by rfl

/--
@isnad1 id=eq.0h4v.s6.8bb86b1e5537 from=translated src=- shape=a627156e vocab=b88cb3e4
-/
@[simp]
lemma id_coe_apply
    [Preorder V]
    (X : CombinationalCircuitCategory V G) (v : Wires V X.obj) :
    (𝟙 X : Hom V X X).val v = v := rfl

/-- The wire-function that duplicates its single input wire. -/
@[inline, simp]
def fork (w : Wires V 1) : Wires V 2 := #v[w.get 0, w.get 0]

/--
@isnad1 id=monotone.0h1v.s5.8b956141c7a1 from=translated src=- shape=7914ba20 vocab=e8bbdfbd
-/
@[simp]
lemma fork_monotone [Preorder V] : Monotone (fork (V:=V)) := fun _ _ h i => by
  obtain ⟨i, hi⟩ := i; have : i = 0 ∨ i = 1 := by omega
  rcases this with rfl | rfl <;> exact h 0

/-- The wire-function that joins two input wires by taking their supremum. -/
@[inline, simp]
def join [SemilatticeSup V] (w : Wires V 2) : Wires V 1 := #v[w.get 0 ⊔ w.get 1]

/--
@isnad1 id=monotone.0h1v.s5.d1fe88ed1bf7 from=translated src=- shape=7914ba20 vocab=34bf2802
-/
@[simp]
lemma join_monotone [SemilatticeSup V] : Monotone (join (V:=V)) := fun _ _ h i => by
  obtain ⟨i, hi⟩ := i; have : i = 0 := by omega
  subst this; exact sup_le_sup (h 0) (h 1)

/-- The monoidal product of two objects, adding their wire counts. -/
@[inline, simp]
abbrev tensorObj (X Y : CombinationalCircuitCategory V G) : CombinationalCircuitCategory V G :=
  .of V G (X.obj + Y.obj)

@[inline]
instance
    [SemilatticeSup V]
    [Gate V G]
    [Bot V] :
    CircuitCategory V G (CombinationalCircuitCategory V G) where
  gate g := ⟨Gate.gate g, Gate.gate_monotone g⟩
  stub := ⟨fun _ => #v[⊥], fun _ _ _ => le_refl _⟩
  drop := ⟨fun _ => #v[], fun _ _ _ => le_refl _⟩
  fork := ⟨fork, fork_monotone⟩
  join := ⟨join, join_monotone⟩

/--
@isnad1 id=eq.0h4v.s5.d5f5407b9467 from=translated src=- shape=7268f4cd vocab=51bd3412
-/
lemma tensorHom_val_add
    {X₁ X₂ : CombinationalCircuitCategory V G} :
    min X₁.obj (X₁.obj + X₂.obj) = X₁.obj :=
  by simp

/--
@isnad1 id=eq.0h4v.s5.b61663fcec05 from=translated src=- shape=53446b24 vocab=9663d1ea
-/
lemma tensorHom_val_sub
    {X₁ X₂ : CombinationalCircuitCategory V G} :
    X₁.obj + X₂.obj - X₁.obj = X₂.obj :=
  by simp

variable [SemilatticeSup V]

/-- The underlying wire-function of the monoidal product of two morphisms. -/
@[inline, simp]
abbrev tensorHomVal
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂)
    (v : Wires V (X₁.obj + X₂.obj)) :
    Wires V (Y₁.obj + Y₂.obj) :=
  (f.val ((v.take X₁.obj).cast tensorHom_val_add)).append
    (g.val ((v.drop X₁.obj).cast tensorHom_val_sub))

/--
@isnad1 id=eq.0h7v.s7.d06ee80befbf from=translated src=- shape=2f0f649e vocab=276655f6
-/
lemma tensorHom_eq
    {X₁ Y₁ X₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (f : X₁ ⟶ Y₁) :
    (f.val (Vector.ofFn fun i ↦ Vector.get a (Fin.castAdd X₂.obj i))).toArray.size = Y₁.obj :=
  (f.val (Vector.ofFn (fun i => a.get (i.castAdd _)))).size_toArray

omit [SemilatticeSup V] in
/--
@isnad1 id=eq.0h5v.s7.f9b4b692b1ef from=translated src=- shape=a73657d1 vocab=c36b5921
-/
lemma tensorHom_take
    {X₁ X₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj)) :
    (a.take X₁.obj).cast tensorHom_val_add =
    Vector.ofFn fun i => a.get (Fin.castAdd X₂.obj i) := by
  unfold Wires at a
  apply Wires.ext; intro i
  simp [Vector.get]
  rfl

omit [SemilatticeSup V] in
/--
@isnad1 id=eq.0h5v.s7.43e0a9b02f52 from=translated src=- shape=36f406e2 vocab=4bc0c929
-/
lemma tensorHom_drop
    {X₁ X₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj)) :
    (a.drop X₁.obj).cast tensorHom_val_sub =
    Vector.ofFn fun i => a.get (Fin.natAdd X₁.obj i) := by
  unfold Wires at a
  apply Wires.ext; intro i
  simp [Vector.get]
  rfl

/--
@isnad1 id=eq.0h10v.s7.a78eb452bddf from=translated src=- shape=ebd01a59 vocab=e720b83d
-/
lemma tensorHom_eq_left
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (j : Fin Y₁.obj)
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (tensorHomVal f g a).get (Fin.castAdd Y₂.obj j) =
    Vector.get (f.val (Vector.ofFn fun i => Vector.get a (Fin.castAdd X₂.obj i))) j := by
  simp only [tensorHomVal, Wires.get_append_left, tensorHom_take]

/--
@isnad1 id=eq.0h10v.s7.794f940e3564 from=translated src=- shape=58881713 vocab=476ee876
-/
lemma tensorHom_eq_right
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (a : Wires V (X₁.obj + X₂.obj))
    (j : Fin Y₂.obj)
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    (tensorHomVal f g a).get (Fin.natAdd Y₁.obj j) =
    Vector.get (g.val (Vector.ofFn fun i => Vector.get a (Fin.natAdd X₁.obj i))) j := by
  simp only [tensorHomVal, Wires.get_append_right, tensorHom_drop]

/--
@isnad1 id=eq.0h10v.s9.3fc2fbd0ecfa from=translated src=- shape=10802e15 vocab=2370a65c
-/
lemma tensorHom_get
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) (w : Wires V (X₁.obj + X₂.obj))
    (i : Fin (Y₁.obj + Y₂.obj)) :
    (tensorHomVal f g w).get i =
    if h : i.val < Y₁.obj
    then (f.val (Vector.ofFn fun k => w.get (Fin.castAdd X₂.obj k))).get ⟨i.val, h⟩
    else (g.val (Vector.ofFn fun k => w.get (Fin.natAdd X₁.obj k))).get
      ⟨i.val - Y₁.obj, by omega⟩ := by
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · simp only [tensorHom_eq_left, Fin.val_castAdd, dite_eq_left j.isLt]
  · simp only [tensorHom_eq_right, Fin.val_natAdd,
               dite_eq_right (show ¬(Y₁.obj + j.val < Y₁.obj) from by omega)]
    congr 1; exact Fin.ext (by simp)

/--
@isnad1 id=monotone.0h8v.s7.961552f718d4 from=translated src=- shape=1daec792 vocab=8c069669
-/
@[simp]
lemma tensorHom_monotone
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    Monotone (tensorHomVal f g) := fun a b h i =>
  Fin.addCases
    (fun j => by
      have lhs_eq := tensorHom_eq_left a j f g
      have rhs_eq := tensorHom_eq_left b j f g
      rw [lhs_eq, rhs_eq]
      exact f.property (fun k => by
        simp only [Vector.get, Vector.toArray_ofFn, Fin.val_cast, Array.getElem_ofFn]
        exact h (k.castAdd _)) j)
    (fun j => by
      have lhs_eq := tensorHom_eq_right a j f g
      have rhs_eq := tensorHom_eq_right b j f g
      rw [lhs_eq, rhs_eq]
      exact g.property (fun k => by
        simp only [Vector.get, Vector.toArray_ofFn, Fin.val_cast, Array.getElem_ofFn]
        exact h (k.natAdd _)) j)
    i

/-- The monoidal product of two morphisms. -/
@[inline, simp]
abbrev tensorHom
    {X₁ Y₁ X₂ Y₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ Y₁)
    (g : X₂ ⟶ Y₂) :
    tensorObj X₁ X₂ ⟶ tensorObj Y₁ Y₂ :=
  ⟨tensorHomVal f g, tensorHom_monotone f g⟩

/-- The underlying wire-function of the forward direction of a wire-count isomorphism. -/
@[simp]
abbrev isoHomVal (h : n = m) : Wires V n → Wires V m := (·.cast h)

/--
@isnad1 id=monotone.1h3v.s5.a2143396beed from=translated src=- shape=30dc62be vocab=0bab507d
-/
@[simp]
lemma iso_hom_monotone (h : n = m) : Monotone (isoHomVal (V:=V) h) :=
  fun _ _ hab i => hab (i.cast h.symm)

/-- The forward direction of a wire-count isomorphism. -/
@[simp]
abbrev isoHom (h : n = m) : { f : Wires V n → Wires V m // Monotone f } :=
  ⟨isoHomVal h, iso_hom_monotone h⟩

/-- The underlying wire-function of the inverse direction of a wire-count isomorphism. -/
@[simp]
abbrev isoInvVal (h : n = m) : Wires V m → Wires V n := (·.cast h.symm)

/--
@isnad1 id=monotone.1h3v.s5.4691d248e402 from=translated src=- shape=2831734e vocab=ace29d32
-/
lemma iso_inv_monotone (h : n = m) : Monotone (isoInvVal (V:=V) h) :=
  fun _ _ hab i => hab (i.cast h)

/-- The inverse direction of a wire-count isomorphism. -/
@[simp]
abbrev isoInv (h : n = m) : { f : Wires V m → Wires V n // Monotone f } :=
  ⟨isoInvVal h, iso_inv_monotone h⟩

/--
@isnad1 id=eq.1h4v.s7.c9a432101d0d from=translated src=- shape=bc0dfa4e vocab=367b7f28
-/
@[simp]
lemma iso_hom_inv_id
    (h : n = m) :
    isoHom h ≫ isoInv h = 𝟙 (OfNat.ofNat n : CombinationalCircuitCategory V G) := by
  apply Subtype.ext; funext v; rfl

/--
@isnad1 id=eq.1h4v.s7.7463638a0df6 from=translated src=- shape=e3be9b5d vocab=367b7f28
-/
lemma iso_inv_hom_id
    (h : n = m) :
    isoInv h ≫ isoHom h = 𝟙 (OfNat.ofNat m : CombinationalCircuitCategory V G) := by
  apply Subtype.ext; funext v; rfl

/-- The isomorphism between objects with equal wire counts. -/
@[inline, simp]
def iso
    (h : n = m) :
    CombinationalCircuitCategory.of V G n ≅ CombinationalCircuitCategory.of V G m :=
  { hom := isoHom h
    inv := isoInv h
    hom_inv_id := iso_hom_inv_id h
    inv_hom_id := iso_inv_hom_id h }

/--
@isnad1 id=eq.0h4v.s6.9c670589dfc7 from=translated src=- shape=bd1781b3 vocab=ede356ab
-/
@[simp]
lemma whisker
    (X Y : CombinationalCircuitCategory V G) :
    tensorHom (𝟙 X) (𝟙 Y) = 𝟙 (X.tensorObj Y) := by
  apply Subtype.ext; funext v
  change tensorHomVal (𝟙 X) (𝟙 Y) v = v
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j (𝟙 X) (𝟙 Y)]
    simp only [CategoryStruct.id, id, idVal, Wires.get_ofFn]
  · rw [tensorHom_eq_right v j (𝟙 X) (𝟙 Y)]
    simp only [CategoryStruct.id, id, idVal, Wires.get_ofFn]

/-- Left whiskering of a morphism by a fixed object. -/
@[inline, simp]
abbrev whiskerLeft
    (X : CombinationalCircuitCategory V G)
    {Y₁ Y₂ : CombinationalCircuitCategory V G} :
    (Y₁ ⟶ Y₂) →
    (tensorObj X Y₁ ⟶ tensorObj X Y₂) :=
  tensorHom (𝟙 X)

/-- Right whiskering of a morphism by a fixed object. -/
@[inline, simp]
abbrev whiskerRight
    {X₁ X₂ : CombinationalCircuitCategory V G}
    (f : X₁ ⟶ X₂)
    (Y : CombinationalCircuitCategory V G) : tensorObj X₁ Y ⟶ tensorObj X₂ Y :=
  tensorHom f (𝟙 Y)

/--
@isnad1 id=eq.0h8v.s7.37d17b1e363b from=translated src=- shape=62a875cd vocab=e4d9e06d
-/
@[simp]
lemma tensorHom_def
    {W X Y Z : CombinationalCircuitCategory V G} (f : W ⟶ X) (g : Y ⟶ Z) :
    tensorHom f g = whiskerRight f Y ≫ whiskerLeft X g := by
  apply Subtype.ext; funext v
  change tensorHomVal f g v = tensorHomVal id g (tensorHomVal f id v)
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j f g, tensorHom_eq_left _ j id g]
    simp only [id, idVal, Wires.get_ofFn]
    exact (tensorHom_eq_left v j f id).symm
  · rw [tensorHom_eq_right v j f g, tensorHom_eq_right _ j id g]
    simp only [id]
    exact congrArg (fun x => (g.val x).get j)
      (Wires.ext (fun k => by
        conv_rhs => rw [Wires.get_ofFn]
        exact (tensorHom_eq_right v k f (𝟙 _)).symm))

/--
@isnad1 id=eq.0h4v.s6.9c670589dfc7 from=translated src=- shape=bd1781b3 vocab=ede356ab
-/
@[simp]
lemma id_tensorHom_id
    (X₁ X₂ : CombinationalCircuitCategory V G) :
    tensorHom (𝟙 X₁) (𝟙 X₂) = 𝟙 (X₁.tensorObj X₂) := by
  apply Subtype.ext; funext v
  change tensorHomVal (𝟙 X₁) (𝟙 X₂) v = v
  unfold tensorHomVal
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left v j (𝟙 X₁) (𝟙 X₂)]
    simp only [CategoryStruct.id, id, idVal, Wires.get_ofFn]
  · rw [tensorHom_eq_right v j (𝟙 X₁) (𝟙 X₂)]
    simp only [CategoryStruct.id, id, idVal, Wires.get_ofFn]

/--
@isnad1 id=eq.0h12v.s7.3cae42d7a92c from=translated src=- shape=ec861311 vocab=f9d6dd53
-/
@[simp]
lemma tensorHom_comp_tensorHom
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : CombinationalCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁)
    (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  apply Subtype.ext; funext v
  change tensorHomVal g₁ g₂ (tensorHomVal f₁ f₂ v) = tensorHomVal (f₁ ≫ g₁) (f₂ ≫ g₂) v
  apply Wires.ext; intro i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [tensorHom_eq_left _ j g₁ g₂, tensorHom_eq_left v j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp]
    exact congrArg (fun x => (g₁.val x).get j)
      (Wires.ext (fun k => by
        conv_lhs => rw [Wires.get_ofFn]
        exact tensorHom_eq_left v k f₁ f₂))
  · rw [tensorHom_eq_right _ j g₁ g₂, tensorHom_eq_right v j (f₁ ≫ g₁) (f₂ ≫ g₂)]
    simp only [CategoryStruct.comp]
    exact congrArg (fun x => (g₂.val x).get j)
      (Wires.ext (fun k => by
        conv_lhs => rw [Wires.get_ofFn]
        exact tensorHom_eq_right v k f₁ f₂))

/-- The monoidal unit, the object with no wires. -/
@[inline, simp]
def tensorUnit : CombinationalCircuitCategory V G := .of V G 0

omit [SemilatticeSup V] in
/--
@isnad1 id=eq.0h5v.s6.7c1abc3c6663 from=translated src=- shape=b6d57b64 vocab=3b7f355f
-/
@[simp]
lemma associator_eq
    (X Y Z : CombinationalCircuitCategory V G) :
    X.obj + Y.obj + Z.obj = X.obj + (Y.obj + Z.obj) :=
  Nat.add_assoc X.obj Y.obj Z.obj

/-- The associator isomorphism of the monoidal structure. -/
@[inline, simp]
def associator
    (X Y Z : CombinationalCircuitCategory V G) :
    (X.tensorObj Y).tensorObj Z ≅ X.tensorObj (Y.tensorObj Z) :=
  iso (associator_eq X Y Z)

/--
@isnad1 id=eq.0h11v.s8.e3ad9de659c6 from=translated src=- shape=127251c1 vocab=4c20ff0e
-/
lemma associator_naturality
    {X₁ X₂ X₃ Y₁ Y₂ Y₃ : CombinationalCircuitCategory V G}
    (f₁ : X₁ ⟶ Y₁)
    (f₂ : X₂ ⟶ Y₂)
    (f₃ : X₃ ⟶ Y₃) :
    tensorHom (tensorHom f₁ f₂) f₃ ≫ (Y₁.associator Y₂ Y₃).hom =
      (X₁.associator X₂ X₃).hom ≫ tensorHom f₁ (tensorHom f₂ f₃) := by
  apply Subtype.ext; funext v; unfold Wires at v; apply Vector.ext; intro i hi
  simp [CategoryStruct.comp, Function.comp, Vector.append, Vector.cast]

/--
@isnad1 id=eq.0h6v.s8.4ffd71211ea3 from=translated src=- shape=e1e093ba vocab=745980b3
-/
lemma pentagon
    (W X Y Z : CombinationalCircuitCategory V G) :
    whiskerRight (W.associator X Y).hom Z ≫
      (W.associator (X.tensorObj Y) Z).hom ≫
      whiskerLeft W (X.associator Y Z).hom =
    ((W.tensorObj X).associator Y Z).hom ≫ (W.associator X (Y.tensorObj Z)).hom := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < W.obj + (X.obj + (Y.obj + Z.obj)) := i.isLt
  simp only [CategoryStruct.comp, Function.comp, associator, iso, isoHom, isoHomVal,
    tensorHomVal, CategoryStruct.id, id, idVal,
    Wires.get_append_vector, Wires.get_cast, Wires.get_cast_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;> exact congrArg v.get (Fin.ext (by simp <;> omega))

omit [SemilatticeSup V] in
/--
@isnad1 id=eq.0h3v.s4.4c870e21d91c from=translated src=- shape=44da2d3c vocab=1249920f
-/
lemma leftUnitor_eq
    (X : CombinationalCircuitCategory V G) :
    (tensorUnit (V:=V) (G:=G)).obj + X.obj = X.obj :=
  Nat.zero_add X.obj

omit [SemilatticeSup V] in
/--
@isnad1 id=eq.0h3v.s4.2035e648ba4e from=translated src=- shape=a2e0ab5c vocab=1249920f
-/
lemma rightUnitor_eq
    (X : CombinationalCircuitCategory V G) :
    X.obj + (tensorUnit (V:=V) (G:=G)).obj = X.obj :=
  Nat.add_zero X.obj

/-- The left unitor isomorphism of the monoidal structure. -/
@[simp]
abbrev leftUnitor (X : CombinationalCircuitCategory V G) : tensorObj tensorUnit X ≅ X :=
  iso (leftUnitor_eq X)

/-- The right unitor isomorphism of the monoidal structure. -/
@[simp]
abbrev rightUnitor (X : CombinationalCircuitCategory V G) : tensorObj X tensorUnit ≅ X :=
  iso (rightUnitor_eq X)

/--
@isnad1 id=eq.0h5v.s7.8104fe5171b2 from=translated src=- shape=70b9694c vocab=6d0578ae
-/
lemma leftUnitor_naturality
    {X Y : CombinationalCircuitCategory V G} (f : X ⟶ Y) :
    whiskerLeft tensorUnit f ≫ (leftUnitor Y).hom = (leftUnitor X).hom ≫ f := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have harg : (Vector.ofFn fun k : Fin X.obj =>
      Vector.get v (Fin.natAdd (tensorUnit (V := V) (G := G)).obj k))
      = Vector.cast (leftUnitor_eq X) v := by
    apply Wires.ext; intro k
    simp only [Wires.get_ofFn, Wires.get_cast]
    exact congrArg v.get (Fin.ext (by simp))
  simp only [CategoryStruct.comp, Function.comp, leftUnitor, iso, isoHom, isoHomVal]
  rw [Wires.get_cast, tensorHom_get,
    dite_eq_right (show ¬ (i.val < (tensorUnit (V := V) (G := G)).obj) from by simp), harg]
  exact congrArg _ (Fin.ext (by simp))

/--
@isnad1 id=eq.0h5v.s7.8ee1e3c654ae from=translated src=- shape=6841d722 vocab=8f09965f
-/
lemma rightUnitor_naturality
    {X Y : CombinationalCircuitCategory V G}
    (f : X ⟶ Y) :
    whiskerRight f tensorUnit ≫ (rightUnitor Y).hom = (rightUnitor X).hom ≫ f := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have harg : (Vector.ofFn fun k : Fin X.obj =>
      Vector.get v (Fin.castAdd (tensorUnit (V := V) (G := G)).obj k))
      = Vector.cast (rightUnitor_eq X) v := by
    apply Wires.ext; intro k
    simp only [Wires.get_ofFn, Wires.get_cast]
    exact congrArg v.get (Fin.ext (by simp))
  simp only [CategoryStruct.comp, Function.comp, rightUnitor, iso, isoHom, isoHomVal]
  rw [Wires.get_cast, tensorHom_get, dite_eq_left (show i.val < Y.obj from i.isLt), harg]

open MonoidalCategory

/--
@isnad1 id=eq.0h4v.s7.4ee4e69e2902 from=translated src=- shape=b9e78d22 vocab=ea9bda30
-/
lemma triangle
    (X Y : CombinationalCircuitCategory V G) :
    (associator X tensorUnit Y).hom ≫ whiskerLeft X (leftUnitor Y).hom =
    whiskerRight (rightUnitor X).hom Y := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < X.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, associator, leftUnitor, rightUnitor, iso,
    isoHom, isoHomVal, tensorHomVal,
    CategoryStruct.id, id, idVal,
    Wires.get_append_vector, Wires.get_cast, Wires.get_cast_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;> exact congrArg v.get (Fin.ext (by simp))

@[inline, simp]
instance : MonoidalCategory.{v} (CombinationalCircuitCategory V G) where
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
@isnad1 id=eq.0h4v.s6.b4ad5603f1bf from=translated src=- shape=6ac2c575 vocab=e080e1aa
-/
@[simp]
lemma monoidal_tensorObj_obj
    (X Y : CombinationalCircuitCategory V G) :
    (X ⊗ Y).obj = X.obj + Y.obj := rfl

/--
@isnad1 id=eq.0h2v.s5.066afd88f5ed from=translated src=- shape=1b6729ee vocab=f87e0933
-/
@[simp]
lemma monoidal_tensorUnit_obj :
    (𝟙_ (CombinationalCircuitCategory V G)).obj = 0 := rfl

/--
@isnad1 id=eq.0h4v.s6.134d5ad24cf0 from=translated src=- shape=a627156e vocab=d0c6df6d
-/
@[simp]
lemma id_hom_apply
    (X : CombinationalCircuitCategory V G) (v : Wires V X.obj) :
    (CategoryStruct.id X : Hom V X X).val v = v := rfl

omit [SemilatticeSup V] in
/--
@isnad1 id=eq.0h4v.s5.b61663fcec05 from=translated src=- shape=53446b24 vocab=9663d1ea
-/
lemma sub_eq {X Y : CombinationalCircuitCategory V G} : X.obj + Y.obj - X.obj = Y.obj := by omega

/--
@isnad1 id=eq.0h6v.s9.7c905e8c569e from=translated src=- shape=3f36b073 vocab=8a0ee110
-/
@[simp]
lemma associator_hom_apply
    (X Y Z : CombinationalCircuitCategory V G)
    (v : Wires V ((X ⊗ Y) ⊗ Z).obj) :
    (α_ X Y Z).hom.val v = v.cast (associator_eq X Y Z) := rfl

/--
@isnad1 id=eq.0h6v.s9.d344ea1cdef4 from=translated src=- shape=dce2eaad vocab=a916bc5b
-/
@[simp]
lemma associator_inv_apply
    (X Y Z : CombinationalCircuitCategory V G)
    (v : Wires V (X ⊗ (Y ⊗ Z)).obj) :
    (α_ X Y Z).inv.val v = v.cast (associator_eq X Y Z).symm := rfl

/--
@isnad1 id=eq.0h4v.s7.f6cf0c97448d from=translated src=- shape=343ed860 vocab=f64c1360
-/
lemma braiding_hom_eq
    {X Y : CombinationalCircuitCategory V G} :
    (X ⊗ Y).obj - X.obj + min X.obj (X ⊗ Y).obj = (Y ⊗ X).obj := by simp

/-- The underlying wire-function of the braiding, swapping two blocks of wires. -/
@[inline, simp]
abbrev braidingHomVal
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X ⊗ Y).obj) :
    Wires V (Y ⊗ X).obj :=
  ((v.drop X.obj).append (v.take X.obj)).cast braiding_hom_eq

/--
@isnad1 id=lt.0h5v.s6.2196910992c1 from=translated src=- shape=9813f585 vocab=73f6b399
-/
lemma braiding_hom_lt
    {X Y : CombinationalCircuitCategory V G}
    {j : Fin Y.obj} :
    X.obj + ↑j < (X ⊗ Y).obj := by
  simp_all

/--
@isnad1 id=lt.0h5v.s5.576eb2da2ba8 from=translated src=- shape=251607d3 vocab=9471da3a
-/
lemma braiding_hom_ge
    {X Y : CombinationalCircuitCategory V G}
    {j : Fin X.obj} :
    ↑j < (X ⊗ Y).obj := by
  change j.val < X.obj + Y.obj
  omega

/--
@isnad1 id=monotone.0h4v.s7.e238c2501849 from=translated src=- shape=131fb8df vocab=b6c4def5
-/
@[simp]
lemma braiding_hom_monotone
    {X Y : CombinationalCircuitCategory V G} :
    Monotone (X.braidingHomVal Y) := fun a b hab i => by
  simp only [braidingHomVal, monoidal_tensorObj_obj, Wires.get_cast_vector,
    Wires.get_append_vector, Wires.get_take,
    Wires.get_drop]
  split_ifs <;> exact hab _

/-- The braiding morphism, swapping two blocks of wires. -/
@[inline, simp]
def braidingHom (X Y : CombinationalCircuitCategory V G) : X ⊗ Y ⟶ Y ⊗ X :=
  ⟨braidingHomVal X Y, braiding_hom_monotone⟩

/--
@isnad1 id=eq.0h4v.s8.a35f4e86a307 from=translated src=- shape=64bfd792 vocab=e27e0843
-/
lemma braiding_hom_inv_id
    {X Y : CombinationalCircuitCategory V G} :
    X.braidingHom Y ≫ Y.braidingHom X = 𝟙 (X ⊗ Y) := by
  apply Subtype.ext; funext v
  apply Wires.ext; intro i
  have hi : i.val < X.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, braidingHom, braidingHomVal,
    monoidal_tensorObj_obj, id_coe_apply, Wires.get_cast_vector,
    Wires.get_append_vector, Wires.get_take, Wires.get_take_vector,
    Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;> exact congrArg v.get (Fin.ext (by simp <;> omega))

/-- The braiding isomorphism of the symmetric monoidal structure. -/
@[inline, simp]
def braiding (X Y : CombinationalCircuitCategory V G) : X ⊗ Y ≅ Y ⊗ X :=
  { hom := braidingHom X Y
    inv := braidingHom Y X
    hom_inv_id := braiding_hom_inv_id
    inv_hom_id := braiding_hom_inv_id }

/--
@isnad1 id=eq.0h6v.s9.c21daf799cdd from=translated src=- shape=e38df357 vocab=d39c574d
-/
lemma braiding_naturality_left
    {X Y : CombinationalCircuitCategory V G}
    (f : X ⟶ Y)
    (Z : CombinationalCircuitCategory V G) :
    f ▷ Z ≫ (Y.braiding Z).hom = (braiding X Z).hom ≫ Z ◁ f := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < Z.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom, tensorHomVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj, CategoryStruct.id, id, idVal,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_append_wires_vector, Wires.get_append_vector_wires,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp)))
      | (congr 1 <;>
          first
            | exact Fin.ext (by simp; try omega)
            | (refine congrArg f.val (Wires.ext fun k => ?_)
               simp only [Wires.get_cast_vector,
                 Wires.get_append_vector,
                 Wires.get_take,
                 Wires.get_drop, Wires.get_drop_vector]
               split_ifs <;>
                 first
                   | (exfalso; omega)
                   | (exact congrArg v.get (Fin.ext (by simp)))))

/--
@isnad1 id=eq.0h8v.s10.6486ac63c965 from=translated src=- shape=2f8914ae vocab=f3f0c77a
-/
lemma braiding_eq
    {X Y Z : CombinationalCircuitCategory V G}
    {f : Y ⟶ Z}
    {v : Wires V (X ⊗ Y).obj}
    {j : Fin X.obj} :
    Vector.get ((X ◁ f ≫ (X.braiding Z).hom).val v) (Fin.natAdd Z.obj j) =
    Vector.get (((X.braiding Y).hom ≫ f ▷ X).val v) (Fin.natAdd Z.obj j) := by
  have hj : j.val < X.obj := j.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom, tensorHomVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj, CategoryStruct.id, id, idVal,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_append_wires_vector, Wires.get_append_vector_wires,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector,
    Fin.val_natAdd]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp)))

/--
@isnad1 id=eq.0h6v.s9.e7ea25869590 from=translated src=- shape=9f6cec64 vocab=d39c574d
-/
lemma braiding_naturality_right
    (X : CombinationalCircuitCategory V G)
    {Y Z : CombinationalCircuitCategory V G}
    (f : Y ⟶ Z) :
    X ◁ f ≫ (X.braiding Z).hom = (braiding X Y).hom ≫ f ▷ X := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < Z.obj + X.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom, tensorHomVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj, CategoryStruct.id, id, idVal,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_append_wires_vector, Wires.get_append_vector_wires,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp)))
      | (congr 1 <;>
          first
            | exact Fin.ext (by simp; try omega)
            | (refine congrArg f.val (Wires.ext fun k => ?_)
               simp only [Wires.get_cast_vector,
                 Wires.get_append_vector,
                 Wires.get_take, Wires.get_take_vector,
                 Wires.get_drop]
               split_ifs <;>
                 first
                   | (exfalso; omega)
                   | (exact congrArg v.get (Fin.ext (by simp)))))

omit [SemilatticeSup V] in
/--
@isnad1 id=lt.1h5v.s5.1645ca21dfab from=translated src=- shape=aa8d92f5 vocab=6fbbf96f
-/
lemma braiding_add
    {X Y : CombinationalCircuitCategory V G}
    (h : ↑i < Y.obj) :
    X.obj + ↑i < X.obj + Y.obj := by omega

/--
@isnad1 id=lt.0h5v.s7.6c11b5dc5a7e from=translated src=- shape=485b7397 vocab=d8bc6635
-/
lemma braiding_sub
    {X Y : CombinationalCircuitCategory V G}
    {i : Fin (Y ⊗ X).obj} :
    ↑i - Y.obj < (X ⊗ Y).obj := by
  have : i.val < Y.obj + X.obj := i.isLt
  change i.val - Y.obj < X.obj + Y.obj
  omega

omit [SemilatticeSup V] in
/--
@isnad1 id=not.0h5v.s5.1cc671b1c5ae from=translated src=- shape=4c79ab04 vocab=1c811456
-/
lemma braiding_get_ge
    {X Y : CombinationalCircuitCategory V G}
    {j : Fin X.obj} :
    ¬Y.obj + ↑j < Y.obj := by omega

/--
@isnad1 id=eq.0h6v.s9.4121bb2e0581 from=translated src=- shape=b1348fd4 vocab=38ccf491
-/
lemma braiding_get
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X ⊗ Y).obj)
    (i : Fin (Y ⊗ X).obj) :
    ((X.braiding Y).hom.val v).get i =
      if h : i.val < Y.obj
      then v.get ⟨X.obj + i.val, braiding_add h⟩
      else v.get ⟨i.val - Y.obj, braiding_sub⟩ := by
  have hi : i.val < Y.obj + X.obj := i.isLt
  simp only [braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj,
    Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_drop]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp)))

/--
@isnad1 id=eq.0h6v.s8.d1288bdffa64 from=translated src=- shape=a654d115 vocab=0878b4e8
-/
lemma braiding_get_castAdd
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X.obj + Y.obj)) (j : Fin Y.obj) :
    ((braiding X Y).hom.val v).get (Fin.castAdd X.obj j) =
    v.get (Fin.natAdd X.obj j) := by
  simp only [braiding_get, Fin.val_castAdd, dite_eq_left j.isLt]
  exact congrArg v.get (Fin.ext (by simp))

/--
@isnad1 id=eq.0h6v.s8.503a4f538dbf from=translated src=- shape=75ee9f97 vocab=0878b4e8
-/
lemma braiding_get_natAdd
    (X Y : CombinationalCircuitCategory V G)
    (v : Wires V (X.obj + Y.obj)) (j : Fin X.obj) :
    ((braiding X Y).hom.val v).get (Fin.natAdd Y.obj j) =
    v.get (Fin.castAdd Y.obj j) := by
  simp only [braiding_get, braiding_get_ge, Fin.val_natAdd]
  exact congrArg v.get (Fin.ext (by simp))

/--
@isnad1 id=eq.0h5v.s10.024ac37076c6 from=translated src=- shape=69d5725b vocab=4024b15f
-/
lemma hexagon_forward
    (X Y Z : CombinationalCircuitCategory V G) :
    (α_ X Y Z).hom ≫ (X.braiding (Y ⊗ Z)).hom ≫ (α_ Y Z X).hom =
    (X.braiding Y).hom ▷ Z ≫ (α_ Y X Z).hom ≫ Y ◁ (X.braiding Z).hom := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < Y.obj + (Z.obj + X.obj) := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom, tensorHomVal,
    MonoidalCategoryStruct.associator, associator, iso, isoHom, isoHomVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj,
    CategoryStruct.id, id, idVal,
    Wires.get_cast, Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp <;> omega)))

/--
@isnad1 id=eq.0h5v.s10.443c3ec82f23 from=translated src=- shape=828e7174 vocab=21405a7b
-/
lemma hexagon_reverse
    (X Y Z : CombinationalCircuitCategory V G) :
    (α_ X Y Z).inv ≫ ((X ⊗ Y).braiding Z).hom ≫ (α_ Z X Y).inv =
    X ◁ (Y.braiding Z).hom ≫ (α_ X Z Y).inv ≫ (X.braiding Z).hom ▷ Y := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  have hi : i.val < Z.obj + X.obj + Y.obj := i.isLt
  simp only [CategoryStruct.comp, Function.comp, MonoidalCategoryStruct.whiskerLeft,
    MonoidalCategoryStruct.whiskerRight, whiskerLeft, whiskerRight, tensorHom, tensorHomVal,
    MonoidalCategoryStruct.associator, associator, iso, isoInv, isoInvVal,
    braiding, braidingHom, braidingHomVal, monoidal_tensorObj_obj,
    CategoryStruct.id, id, idVal,
    Wires.get_cast, Wires.get_cast_vector, Wires.get_append_vector,
    Wires.get_take, Wires.get_take_vector, Wires.get_drop, Wires.get_drop_vector]
  split_ifs <;>
    first
      | (exfalso; omega)
      | (exact congrArg v.get (Fin.ext (by simp; omega)))

/--
@isnad1 id=eq.0h4v.s8.cfc89ec2c9dd from=translated src=- shape=153897f2 vocab=85f40a4f
-/
lemma symmetry
    (X Y : CombinationalCircuitCategory V G) :
    (X.braiding Y).hom ≫ (Y.braiding X).hom = 𝟙 (X ⊗ Y) := by
  apply Subtype.ext; funext v; apply Wires.ext; intro i
  simp only [CategoryStruct.comp, Function.comp, braiding_get]
  have htXY : (X ⊗ Y).obj = X.obj + Y.obj := rfl
  split <;> split <;>
  exact congrArg v.get (Fin.ext (by simp only []; omega))

@[inline, simp]
instance : SymmetricCategory (CombinationalCircuitCategory V G) where
  braiding
  braiding_naturality_left
  braiding_naturality_right
  hexagon_forward
  hexagon_reverse
  symmetry

end CombinationalCircuitCategory

end Circuit
