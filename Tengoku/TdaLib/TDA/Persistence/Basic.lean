import Tengoku.Seed.CategoryTheory.Category.Preorder
import Tengoku.Seed.CategoryTheory.Whiskering
import Tengoku.Seed.Algebra.Category.ModuleCat.Basic
import Tengoku.Seed.Data.ZMod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Preorder-indexed persistence modules

A persistence module is a covariant functor from a preorder, viewed as a category, to the category
of modules over a ring. An inequality `p ≤ q` induces a morphism from the value at `p` to the value
at `q`. Reindexing is precomposition by a monotone map, and natural transformations reindex by
left whiskering.

This API uses mathlib's preorder category and `ModuleCat` at the pinned revision
`0df444a360eaa60ab8c11dca51a86af692955474`, in particular
`Mathlib/CategoryTheory/Category/Preorder.lean`, `Mathlib/CategoryTheory/Whiskering.lean`, and
`Mathlib/Algebra/Category/ModuleCat/Basic.lean`. The ring, index, module-carrier, and reindex-domain
universes are independent. The core requires only a ring and preorders; no field or
finite-dimensional assumptions are imposed.
-/

universe u v w x y

namespace TDA.Persistence

open CategoryTheory

/-- A covariant persistence module on a preorder `P` over a ring `R`.

`R : Type u`, the index `P : Type v`, and the carrier universe `w` of `ModuleCat.{w} R` are
independent.-/
abbrev PModule (R : Type u) [Ring R] (P : Type v) [Preorder P] :=
  P ⥤ ModuleCat.{w} R

variable {R : Type u} [Ring R] {P : Type v} [Preorder P]

/-- The covariant structure morphism induced by `h : p ≤ q`.-/
def structureMap (M : PModule.{u,v,w} R P) {p q : P} (h : p ≤ q) :
    M.obj p ⟶ M.obj q :=
  M.map (homOfLE h)

/-- The underlying `R`-linear map of a persistence-module structure morphism.-/
def structureMapLinear (M : PModule.{u,v,w} R P) {p q : P} (h : p ≤ q) :
    M.obj p →ₗ[R] M.obj q :=
  (structureMap M h).hom

/-- A structure map at an index to itself is the identity morphism.
@isnad1 id=eq.1h4v.s6.66959e1ddc69 from=translated src=- shape=c38e6010 vocab=b1a1ca84
-/
@[simp]
theorem structureMap_self (M : PModule.{u,v,w} R P) {p : P} (h : p ≤ p) :
    structureMap M h = 𝟙 (M.obj p) := by
  simp [structureMap]

/-- Structure maps compose in the covariant order: first `p → q`, then `q → r`.
@isnad1 id=eq.2h6v.s7.78550750f029 from=translated src=- shape=a86fd3ff vocab=dd3e51fa
-/
theorem structureMap_comp (M : PModule.{u,v,w} R P) {p q r : P}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    structureMap M hpq ≫ structureMap M hqr = structureMap M (hpq.trans hqr) := by
  change M.map (homOfLE hpq) ≫ M.map (homOfLE hqr) =
    M.map (homOfLE (hpq.trans hqr))
  rw [← M.map_comp, CategoryTheory.homOfLE_comp]

/-- The underlying linear map of a self-structure map is the identity.
@isnad1 id=eq.1h4v.s7.da0c629fd372 from=translated src=- shape=74e3e7ac vocab=e4628949
-/
@[simp]
theorem structureMapLinear_self (M : PModule.{u,v,w} R P) {p : P} (h : p ≤ p) :
    structureMapLinear M h = LinearMap.id := by
  simp [structureMapLinear, structureMap_self]

/-- The linear map of a composite structure map is the later map after the earlier map.
@isnad1 id=eq.2h6v.s8.ca2c957aba54 from=translated src=- shape=d9bc85a5 vocab=a4b4a58d
-/
theorem structureMapLinear_comp (M : PModule.{u,v,w} R P) {p q r : P}
    (hpq : p ≤ q) (hqr : q ≤ r) :
    structureMapLinear M (hpq.trans hqr) =
      (structureMapLinear M hqr).comp (structureMapLinear M hpq) := by
  change (structureMap M (hpq.trans hqr)).hom = _
  rw [← structureMap_comp M hpq hqr]
  exact ModuleCat.hom_comp _ _

/-- Restrict a persistence module along a monotone map, by precomposition.-/
def reindex {Q : Type x} [Preorder Q] (u : Q →o P) (M : PModule.{u,v,w} R P) :
    PModule.{u,x,w} R Q :=
  u.toFunctor ⋙ M

/-- The value of a reindexed persistence module at `q` is the original value at `u q`.
@isnad1 id=eq.0h6v.s6.9fa52b806a7e from=translated src=- shape=8d8ab65e vocab=4807effd
-/
@[simp]
theorem reindex_obj {Q : Type x} [Preorder Q] (u : Q →o P)
    (M : PModule.{u,v,w} R P) (q : Q) :
    (reindex u M).obj q = M.obj (u q) := rfl

/-- The structure map of a reindexed module is the original structure map at the mapped
inequality.
@isnad1 id=eq.1h7v.s7.83e9e2f0dde2 from=translated src=- shape=da9dace2 vocab=81475cbc
-/
@[simp]
theorem structureMap_reindex {Q : Type x} [Preorder Q] (u : Q →o P)
    (M : PModule.{u,v,w} R P) {q₁ q₂ : Q} (h : q₁ ≤ q₂) :
    structureMap (reindex u M) h = structureMap M (u.monotone' h) := rfl

/-- The underlying linear structure map is preserved by reindexing.
@isnad1 id=eq.1h7v.s8.f7e9101fc5e0 from=translated src=- shape=f903627b vocab=2bcb8759
-/
@[simp]
theorem structureMapLinear_reindex {Q : Type x} [Preorder Q] (u : Q →o P)
    (M : PModule.{u,v,w} R P) {q₁ q₂ : Q} (h : q₁ ≤ q₂) :
    structureMapLinear (reindex u M) h = structureMapLinear M (u.monotone' h) := rfl

/-- Reindexing along the identity order hom is definitionally equal to the original module.
@isnad1 id=eq.0h3v.s5.73a69debbef4 from=translated src=- shape=b2cc2c4b vocab=c101c28e
-/
theorem reindex_id (M : PModule.{u,v,w} R P) :
    reindex (OrderHom.id : P →o P) M = M := rfl

/-- Successive reindexing is definitionally equal to precomposition by the composite order hom.
@isnad1 id=eq.0h7v.s6.dce4807907ac from=translated src=- shape=0630a20c vocab=32c9251a
-/
theorem reindex_comp {Q : Type x} [Preorder Q] {S : Type y} [Preorder S]
    (u : Q →o P) (v : S →o Q) (M : PModule.{u,v,w} R P) :
    reindex v (reindex u M) = reindex (u.comp v) M := rfl

/-- Reindex a natural transformation by left whiskering with the indexing functor.-/
def reindexNatTrans {Q : Type x} [Preorder Q] (u : Q →o P)
    {M N : PModule.{u,v,w} R P} (α : M ⟶ N) : reindex u M ⟶ reindex u N :=
  Functor.whiskerLeft u.toFunctor α

/-- The component of a reindexed natural transformation at `q` is the original component at
`u q`.
@isnad1 id=eq.0h8v.s7.9030e468d7b5 from=translated src=- shape=842691b3 vocab=641e55d8
-/
@[simp]
theorem reindexNatTrans_app {Q : Type x} [Preorder Q] (u : Q →o P)
    {M N : PModule.{u,v,w} R P} (α : M ⟶ N) (q : Q) :
    (reindexNatTrans u α).app q = α.app (u q) := rfl

/-- Reindexing preserves identity natural transformations.
@isnad1 id=eq.0h5v.s7.d20b0e99abc8 from=translated src=- shape=3b211e05 vocab=c421bd56
-/
@[simp]
theorem reindexNatTrans_id {Q : Type x} [Preorder Q] (u : Q →o P)
    (M : PModule.{u,v,w} R P) :
    reindexNatTrans u (𝟙 M) = 𝟙 (reindex u M) := by
  change Functor.whiskerLeft u.toFunctor (𝟙 M) = 𝟙 (u.toFunctor ⋙ M)
  rfl

/-- Reindexing preserves composition of natural transformations.
@isnad1 id=eq.0h9v.s8.8c75fb9c9ddd from=translated src=- shape=6767b6b2 vocab=9e9d7dcd
-/
@[simp]
theorem reindexNatTrans_comp {Q : Type x} [Preorder Q]
    (u : Q →o P) {M N L : PModule.{u,v,w} R P} (α : M ⟶ N) (β : N ⟶ L) :
    reindexNatTrans u (α ≫ β) = reindexNatTrans u α ≫ reindexNatTrans u β := by
  change Functor.whiskerLeft u.toFunctor (α ≫ β) =
    Functor.whiskerLeft u.toFunctor α ≫ Functor.whiskerLeft u.toFunctor β
  rfl

/-! ### Two-stage regression diagrams -/

/-- On the `Fin 2` preorder, the off-diagonal structure map is zero and the self maps are identity.
The equality-based construction is intentionally limited to `Fin 2`.-/
def zeroTransitionDiagram (S : Type u) [Ring S] :
    PModule.{u,0,u} S (Fin 2) where
  obj _ := ModuleCat.of S S
  map {p q} _ := if p = q then 𝟙 (ModuleCat.of S S) else 0
  map_id p := by simp
  map_comp {p q r} f g := by
    have hpq : p ≤ q := leOfHom f
    have hqr : q ≤ r := leOfHom g
    fin_cases p <;> fin_cases q <;> fin_cases r <;> simp_all

/-- A zero-transition diagram over the integers.-/
def integerZeroTransition : PModule.{0,0,0} ℤ (Fin 2) :=
  zeroTransitionDiagram ℤ

/-- The integer two-stage example has zero as its `0 → 1` structure map.
@isnad1 id=eq.0h0v.s10.96a92ad9e928 from=translated src=- shape=b672715b vocab=cbd11783
-/
theorem integerZeroTransition_map :
    structureMapLinear integerZeroTransition (show (0 : Fin 2) ≤ 1 by decide) = 0 := rfl

/-- The integer two-stage example has a nonidentity transition map.
@isnad1 id=ne.0h0v.s9.e8cbb693c2fd from=translated src=- shape=7d94a69b vocab=5051f72f
-/
theorem integerZeroTransition_nonidentity :
    structureMapLinear integerZeroTransition (show (0 : Fin 2) ≤ 1 by decide) ≠ LinearMap.id := by
  intro h
  have h₁ := congrArg (fun f : ℤ →ₗ[ℤ] ℤ => f 1) h
  change (0 : ℤ) = 1 at h₁
  exact zero_ne_one h₁

/-- A zero-transition diagram over the field `ZMod 2`.-/
def zmodTwoZeroTransition : PModule.{0,0,0} (ZMod 2) (Fin 2) :=
  zeroTransitionDiagram (ZMod 2)

/-- The `ZMod 2` two-stage example has zero as its `0 → 1` structure map.
@isnad1 id=eq.0h0v.s11.f2320bb91cb3 from=translated src=- shape=eae7ef0b vocab=981ea7f7
-/
theorem zmodTwoZeroTransition_map :
    structureMapLinear zmodTwoZeroTransition (show (0 : Fin 2) ≤ 1 by decide) = 0 := rfl

/-- The `ZMod 2` two-stage example has a nonidentity transition map.
@isnad1 id=ne.0h0v.s10.a91f3f22cb4e from=translated src=- shape=2bf68eef vocab=11839734
-/
theorem zmodTwoZeroTransition_nonidentity :
    structureMapLinear zmodTwoZeroTransition (show (0 : Fin 2) ≤ 1 by decide) ≠ LinearMap.id := by
  intro h
  have h₁ := congrArg (fun f : ZMod 2 →ₗ[ZMod 2] ZMod 2 => f 1) h
  change (0 : ZMod 2) = 1 at h₁
  exact zero_ne_one h₁

/-- On the same two-stage index, the identity diagram has identity as its transition map.-/
def identityTransitionDiagram (S : Type u) [Ring S] :
    PModule.{u,0,u} S (Fin 2) where
  obj _ := ModuleCat.of S S
  map _ := 𝟙 (ModuleCat.of S S)
  map_id _ := by simp
  map_comp _ _ := by simp

/-- The integer identity diagram has the identity `0 → 1` structure map.
@isnad1 id=eq.0h0v.s7.7c4bf133dcbd from=translated src=- shape=dd4b9d67 vocab=c712e5af
-/
theorem integerIdentityTransition_map :
    structureMap (identityTransitionDiagram ℤ)
      (show (0 : Fin 2) ≤ 1 by decide) = 𝟙 (ModuleCat.of ℤ ℤ) := rfl

end TDA.Persistence
