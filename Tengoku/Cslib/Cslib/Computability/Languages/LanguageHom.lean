/-
Copyright (c) 2025 Ching-Tsun Chou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ching-Tsun Chou
-/

module

public import Tengoku.Cslib.Cslib.Init
public import Tengoku.Seed.Computability.Language

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Language homomorphism
-/

@[expose] public section

namespace Language

open scoped Computability

variable {α β : Type*}

/-- A language homomorphism from `α` to `β` is a map from `List α` to `List β` which
preserves the empty word `[]` and concatenation `(· ++ ·)`.-/
@[ext]
structure Hom (α β : Type*) where
  /-- The map of a language homomorphism.-/
  toFun : List α → List β
  map_nil' : toFun [] = []
  map_append' (as as' : List α) : toFun (as ++ as') = toFun as ++ toFun as'

/-- This is to support the function application notation for language homomorphisms.-/
instance : FunLike (Hom α β) (List α) (List β) where
  coe (f : Hom α β) := f.toFun
  coe_injective (_ _ : Hom α β) := by
    intro _
    ext1
    assumption

namespace Hom

/--
@isnad1 id=iff.0h4v.s5.88837d7d9d8d from=translated src=- shape=9e9e4457 vocab=d8b99fdb
-/
theorem ext_iff' (f f' : Hom α β) :
    f = f' ↔ ∀ as, f as = f' as := by
  constructor
  · grind
  · intro h
    ext1
    ext1 as
    exact h as

/--
@isnad1 id=eq.0h3v.s4.16677a530abe from=translated src=- shape=8a58a2ad vocab=22854910
-/
@[simp, scoped grind =]
theorem map_nil (f : Hom α β) : f [] = [] := f.map_nil'

/--
@isnad1 id=eq.0h5v.s6.68eeba1ab753 from=translated src=- shape=f081a51a vocab=1e03643f
-/
@[simp, scoped grind =]
theorem map_append (f : Hom α β) (as as' : List α) : f (as ++ as') = (f as) ++ (f as') :=
  f.map_append' as as'

/--
@isnad1 id=eq.0h5v.s6.e47804c75279 from=translated src=- shape=7dde8474 vocab=2dbce0a4
-/
@[scoped grind =]
theorem map_cons (f : Hom α β) (a : α) (as : List α) :
    f (a :: as) = f [a] ++ f as := by
  rw [← List.singleton_append, map_append]

/-- This auxiliary function should not be used outside this file.
Instead, use the equivalence `lift` below.-/
def liftAux (f : α → List β) : Hom α β where
  toFun := List.flatMap f
  map_nil' := List.flatMap_nil
  map_append' := fun _ _ ↦ List.flatMap_append

/--
@isnad1 id=eq.0h3v.s5.ec6b145582aa from=translated src=- shape=33ca6fe7 vocab=3e383a66
-/
theorem liftAux_eq_flatMap (f : α → List β) : liftAux f = List.flatMap f :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.1a237f97bf6c from=translated src=- shape=4f8dc6a4 vocab=2080573f
-/
theorem listAux_left_inv (f : α → List β) :
    (fun f a ↦ f [a]) (liftAux f) = f := by
  simp [liftAux_eq_flatMap]

/--
@isnad1 id=eq.0h3v.s5.b433a9c88413 from=translated src=- shape=7e1e186a vocab=2080573f
-/
theorem listAux_right_inv (f : Hom α β) :
    liftAux (fun a ↦ f [a]) = f := by
  rw [ext_iff']
  intro as
  induction as with
  | nil => simp [map_nil]
  | cons a as h_ind =>
    rw [map_cons f, ← h_ind]
    simp [liftAux_eq_flatMap]

/-- An equivalence from `f : α → List β` to `Hom α β`, whose forward direction can be
used to define language homomorphisms conveniently.-/
def lift : (α → List β) ≃ (Hom α β) where
  toFun := liftAux
  invFun := fun f a ↦ f [a]
  left_inv := listAux_left_inv
  right_inv := listAux_right_inv

/-- `lift.toFun` is in fact `List.flatMap`.
@isnad1 id=eq.0h3v.s6.ca04035f1d33 from=translated src=- shape=1463455a vocab=17cda995
-/
theorem lift_eq_flatMap (f : α → List β) : lift f = List.flatMap f :=
  rfl

end Hom

section ImagePreimage

/-- The image of a language under a function `f`, which need not be a language homomorphism.-/
def image (f : List α → List β) (l : Language α) : Language β :=
  f '' l

/-- The preimage of a language under a function `f`, which need not be a language homomorphism.-/
def preimage (f : List α → List β) (l : Language β) : Language α :=
  f ⁻¹' l

/--
@isnad1 id=iff.0h5v.s5.f95b6a7f927c from=translated src=- shape=3874e5b3 vocab=2836388b
-/
@[simp, scoped grind =]
theorem mem_image (f : List α → List β) (l : Language α) (bs : List β) :
    bs ∈ l.image f ↔ ∃ as, as ∈ l ∧ f as = bs := by
  rfl

/--
@isnad1 id=iff.0h5v.s5.b6ceb34a5cd6 from=translated src=- shape=536facd7 vocab=3acc49d8
-/
@[simp, scoped grind =]
theorem mem_preimage (f : List α → List β) (l : Language β) (as : List α) :
    as ∈ l.preimage f ↔ f as ∈ l := by
  rfl

/--
@isnad1 id=eq.0h4v.s5.6537dc3467da from=translated src=- shape=be0c191e vocab=bfa698c0
-/
theorem image_singleton (f : List α → List β) (as : List α) :
    ({as} : Language α).image f = {f as} :=
  Set.image_singleton

/--
@isnad1 id=eq.0h3v.s5.43d85a9313fa from=translated src=- shape=640c10b2 vocab=6c186d63
-/
@[simp]
theorem image_zero (f : List α → List β) : (0 : Language α).image f = 0 :=
  Set.image_empty _

/--
@isnad1 id=eq.0h5v.s5.9402a459e953 from=translated src=- shape=5499cf14 vocab=a5611eb4
-/
theorem image_add (f : List α → List β) (l1 l2 : Language α) :
    (l1 + l2).image f = l1.image f + l2.image f :=
  Set.image_union _ _ _

/--
@isnad1 id=eq.0h5v.s6.58ddcaad992d from=translated src=- shape=fa8415ee vocab=a0526a71
-/
theorem image_iSup (f : List α → List β) {I : Type*} (l : I → Language α) :
    (⨆ i : I, l i).image f = ⨆ i : I, (l i).image f :=
  Set.image_iUnion

/-! The following distributive laws for the `image` operation requires the function `f`
to be a language homomorphism. -/

/--
@isnad1 id=eq.0h3v.s5.60595a214bc0 from=translated src=- shape=61bc37af vocab=0f3a1172
-/
theorem image_one (f : Hom α β) : (1 : Language α).image f = 1 := by
  ext bs
  simp

/--
@isnad1 id=eq.0h5v.s6.bc81463faf26 from=translated src=- shape=589a0799 vocab=3bdf4c6e
-/
theorem image_mul (f : Hom α β) (l1 l2 : Language α) :
    (l1 * l2).image f = l1.image f * l2.image f := by
  ext bs
  simp [mem_mul]

/--
@isnad1 id=eq.0h5v.s6.c29ca5d163bb from=translated src=- shape=ad32b2b0 vocab=96b42130
-/
theorem image_pow (f : Hom α β) (l : Language α) (n : ℕ) :
    (l^n).image f = (l.image f)^n := by
  induction n with
  | zero => simp [image_one]
  | succ n h_ind => simp [pow_succ, image_mul, h_ind]

/--
@isnad1 id=eq.0h4v.s5.9c20bf36956d from=translated src=- shape=bccfc35a vocab=c7bf418e
-/
theorem image_kstar (f : Hom α β) (l : Language α) :
    (l∗).image f = (l.image f)∗ := by
  simp [kstar_eq_iSup_pow, image_iSup, image_pow]

end ImagePreimage

end Language
