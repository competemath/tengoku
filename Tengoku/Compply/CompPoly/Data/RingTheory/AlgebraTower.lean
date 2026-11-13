/-
Copyright (c) 2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chung Thai Nguyen, Quang Dao
-/
module

public import Tengoku.Seed.LinearAlgebra.Matrix.Reindex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Towers of algebras and their equivalences

An `AlgebraTower` is a preorder-indexed family of commutative semirings with ring
homomorphisms between comparable levels. Self-maps are identities, and the maps compose
along chains of indices. Each map induces an algebra structure on its target, and
composition gives compatible scalar actions across three levels.

An `AlgebraTowerEquiv` consists of ring equivalences at each level that commute with
the tower maps.
-/

@[expose] public section
namespace Tengoku.Compply end Tengoku.Compply open Tengoku.Compply 
/-- A preorder-indexed family of commutative semirings with compatible ring homomorphisms.

The map from a level to itself is the identity. For `i ≤ j ≤ k`, the map from `i` to `k`
is the composite of the maps from `i` to `j` and from `j` to `k`.-/
class _root_.Tengoku.Compply.AlgebraTower {ι : Type*} [Preorder ι] (AT : ι → Type*)
  [∀ i, CommSemiring (AT i)] where
  /-- Ring homomorphisms from `AT i` to `AT j` for all `i ≤ j`.-/
  protected algebraMap : ∀ i j, (h : i ≤ j) → (AT i →+* AT j)
  /-- The ring homomorphism from level `i` to itself is the identity.-/
  algebraMap_self' : ∀ i, algebraMap i i le_rfl = RingHom.id (AT i)
  /-- Every image element commutes with every element of the target semiring.-/
  commutes' : ∀ (i j : ι) (h : i ≤ j) (r : AT i) (x : AT j),
    (algebraMap i j h r) * x = x * (algebraMap i j h r)
  /-- The map from `i` to `k` is the composite of the maps from `i` to `j` and `j` to `k`.-/
  coherence' : ∀ (i j k : ι) (h1 : i ≤ j) (h2 : j ≤ k),
    algebraMap i k (h1.trans h2) =
      (algebraMap j k h2).comp (algebraMap i j h1)

variable {ι : Type*} [Preorder ι]
  {A : ι → Type*} [∀ i, CommSemiring (A i)] [AlgebraTower A]
  {B : ι → Type*} [∀ i, CommSemiring (B i)] [AlgebraTower B]
  {C : ι → Type*} [∀ i, CommSemiring (C i)] [AlgebraTower C]

/-- The tower map from level `i` to itself is the identity for every proof of `i ≤ i`.
@isnad1 id=eq.1h3v.s6.c21abba8ae34 from=translated src=- shape=958e85b2 vocab=0e3e550d
-/
@[simp]
lemma Tengoku.Compply.AlgebraTower.algebraMap_self (i : ι) (h : i ≤ i) :
    AlgebraTower.algebraMap (AT := A) i i h = RingHom.id (A i) :=
  AlgebraTower.algebraMap_self' i

/-- The tower map from level `i` to itself fixes every element of that level.
@isnad1 id=eq.1h4v.s6.327237b1a41b from=translated src=- shape=af7f6c4c vocab=7f4829dd
-/
lemma Tengoku.Compply.AlgebraTower.algebraMap_self_apply (i : ι) (h : i ≤ i) (x : A i) :
    AlgebraTower.algebraMap (AT := A) i i h x = x := by
  rw [AlgebraTower.algebraMap_self, RingHom.id_apply]

@[simp]
abbrev Tengoku.Compply.AlgebraTower.toAlgebra {i j : ι} (h : i ≤ j) : Algebra (A i) (A j) :=
  (AlgebraTower.algebraMap (i:=i) (j:=j) (h:=h)).toAlgebra

/--
@isnad1 id=isscalar.2h6v.s7.08d488861c2f from=translated src=- shape=6bad97c5 vocab=b13e853b
-/
@[simp]
instance Tengoku.Compply.AlgebraTower.toIsScalarTower (a : AlgebraTower C) {i j k : ι}
    (h1 : i ≤ j) (h2 : j ≤ k) :
    letI : Algebra (C i) (C j) := by exact a.toAlgebra h1
    letI : Algebra (C j) (C k) := by exact a.toAlgebra h2
    letI : Algebra (C i) (C k) := by exact a.toAlgebra (h1.trans h2)
    IsScalarTower (C i) (C j) (C k) := by
  let instIJ: Algebra (C i) (C j) := by exact a.toAlgebra h1
  let instJK: Algebra (C j) (C k) := by exact a.toAlgebra h2
  let instIK: Algebra (C i) (C k) := by exact a.toAlgebra (h1.trans h2)
  exact {
    smul_assoc := fun (x : C i) (y : C j) (z : C k) => by
      simp_rw [Algebra.smul_def]
      simp only [map_mul]
      rw [←RingHom.comp_apply]
      unfold instIJ instJK instIK AlgebraTower.toAlgebra
      simp_rw [RingHom.algebraMap_toAlgebra]
      have h_assoc := a.coherence' (i:=i) (j:=j) (k:=k) (h1:=h1) (h2:=h2)
      rw [h_assoc]
      rw [mul_assoc]
  }

structure _root_.Tengoku.Compply.AlgebraTowerEquiv (A : ι → Type*) [∀ i, CommSemiring (A i)] [a : AlgebraTower A]
  (B : ι → Type*) [∀ i, CommSemiring (B i)] [b : AlgebraTower B]
  where
    toRingEquiv : ∀ i, (A i ≃+* B i)
    commutesLeft' : ∀ (i j : ι) (h : i ≤ j) (r : A i),
      (b.algebraMap (i:=i) (j:=j) (h:=h)) ((toRingEquiv i) r) =
      (toRingEquiv j) (a.algebraMap (i:=i) (j:=j) (h:=h) r)

/--
@isnad1 id=eq.1h7v.s9.fb71cf7b9bc7 from=translated src=- shape=8de9e4e7 vocab=53955731
-/
lemma Tengoku.Compply.AlgebraTowerEquiv.commutesRight' (e : AlgebraTowerEquiv A B)
    {i j : ι} (h : i ≤ j) (r : B i) :
  AlgebraTower.algebraMap (AT:=A) (i:=i) (j:=j) (h:=h) ((e.toRingEquiv i).symm r) =
  (e.toRingEquiv j).symm (AlgebraTower.algebraMap (AT:=B) (i:=i) (j:=j) (h:=h) r):= by
  apply (e.toRingEquiv j).injective
  set r2: A i := (e.toRingEquiv i).symm r
  rw [←e.commutesLeft' (i:=i) (j:=j) (h:=h) (r:=r2)]
  simp only [RingEquiv.apply_symm_apply]
  have h_e_r2_rfl: e.toRingEquiv i r2 = r := by exact RingEquiv.apply_symm_apply (e.toRingEquiv i) r
  rw [h_e_r2_rfl]

def Tengoku.Compply.AlgebraTowerEquiv.symm (e : AlgebraTowerEquiv A B) : AlgebraTowerEquiv B A where
  toRingEquiv := fun i => (e.toRingEquiv i).symm
  commutesLeft' := fun i j h r => by exact commutesRight' e h r

def Tengoku.Compply.AlgebraTowerEquiv.algebraMapRightUp (e : AlgebraTowerEquiv A B) (i j : ι)
    (h : i ≤ j) : (A i) →+* (B j) := by
  have hBij: B i →+* B j := AlgebraTower.algebraMap (AT:=B) (i:=i) (j:=j) (h:=h)
  have hiRingEquiv: RingEquiv (A i) (B i) := e.toRingEquiv i
  exact hBij.comp hiRingEquiv.toRingHom

def Tengoku.Compply.AlgebraTowerEquiv.algebraMapLeftUp (e : AlgebraTowerEquiv A B) (i j : ι)
    (h : i ≤ j) : (B i) →+* (A j) := by
  have hAij: A i →+* A j := AlgebraTower.algebraMap (AT:=A) (i:=i) (j:=j) (h:=h)
  have hjRingEquiv: RingEquiv (B i) (A i) := (e.toRingEquiv i).symm
  exact hAij.comp hjRingEquiv.toRingHom

abbrev Tengoku.Compply.AlgebraTowerEquiv.toAlgebraOverLeft (e : AlgebraTowerEquiv A B) (i j : ι)
    (h : i ≤ j) : Algebra (A i) (B j) := by
  exact (e.algebraMapRightUp i j h).toAlgebra

abbrev Tengoku.Compply.AlgebraTowerEquiv.toAlgebraOverRight (e : AlgebraTowerEquiv A B) (i j : ι)
    (h : i ≤ j) : Algebra (B i) (A j) := by
  exact (e.algebraMapLeftUp i j h).toAlgebra

def Tengoku.Compply.AlgebraTowerEquiv.toAlgEquivOverLeft (e : AlgebraTowerEquiv A B) (i j : ι) (h : i ≤ j) :
    letI : Algebra (A i) (A j) := by exact AlgebraTower.toAlgebra h
    letI : Algebra (A i) (B j) := by exact e.toAlgebraOverLeft i j h
    AlgEquiv (A i) (A j) (B j) := by
  letI instAij: Algebra (A i) (A j) := by exact AlgebraTower.toAlgebra h
  letI instAiBij: Algebra (A i) (B j) := by exact e.toAlgebraOverLeft i j h
  letI instAlgEquiv: AlgEquiv (A i) (A j) (B j) := by exact {
    toEquiv := by
      have hRingEquiv := e.toRingEquiv j
      exact hRingEquiv.toEquiv
    commutes' := fun r => by
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe]
      unfold instAij instAiBij
      simp only [AlgebraTowerEquiv.algebraMapRightUp, RingHom.algebraMap_toAlgebra]
      simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]
      exact Eq.symm (e.commutesLeft' i j h r)
    map_mul' := fun x y => by
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, map_mul]
    map_add' := fun x y => by
      simp only [RingEquiv.toEquiv_eq_coe, Equiv.toFun_as_coe, EquivLike.coe_coe, map_add]
  }
  exact instAlgEquiv

def Tengoku.Compply.AlgebraTowerEquiv.toAlgEquivOverRight (e : AlgebraTowerEquiv A B) (i j : ι) (h : i ≤ j) :
    letI : Algebra (B i) (B j) := by exact AlgebraTower.toAlgebra h
    letI : Algebra (B i) (A j) := by exact e.toAlgebraOverRight i j h
    AlgEquiv (B i) (B j) (A j) := (e.symm.toAlgEquivOverLeft i j h)
-- Tengoku: root names of this library moved to Tengoku.Compply so they do not collide with other libraries (generated)
