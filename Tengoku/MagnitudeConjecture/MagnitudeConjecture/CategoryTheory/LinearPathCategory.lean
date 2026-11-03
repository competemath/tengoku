import Tengoku.Seed.Algebra.Category.ModuleCat.Basic
import Tengoku.Seed.CategoryTheory.InducedCategory
import Tengoku.Seed.CategoryTheory.Linear.FunctorCategory
import Tengoku.Seed.CategoryTheory.PathCategory.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination
import Tengoku.Seed.LinearAlgebra.Finsupp.VectorSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The free linear category on a quiver

This constructs a linear category whose objects are the vertices of a quiver
and whose morphisms are finite linear combinations of paths.  The construction
uses the representable projective quiver representations, so associativity and
linearity of composition come from the functor category.  It is adapted from
the Tau Ceti-derived quiver foundation used by the sibling `subcat-research`
formalization, with only the path-category interface retained here.
-/

set_option autoImplicit false
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace MagnitudeConjecture.LinearPathCategory

universe u v w

variable {k : Type u} [Field k]
variable {Q : Type v} [Quiver.{w} Q]

/-- Representations of a quiver over `k`.-/
abbrev QuiverRep (k : Type u) (Q : Type v) [Field k] [Quiver Q] :=
  Paths Q ⥤ ModuleCat k

/-- The trivial path acts as the identity in every quiver representation.
@isnad1 id=eq.0h4v.s7.c14512dd37f5 from=translated src=- shape=4486754d vocab=08523a3c
-/
@[simp]
theorem QuiverRep.map_nil (M : QuiverRep k Q) (a : Q) :
    M.map (Quiver.Path.nil : Quiver.Path a a) =
      𝟙 (M.obj (show Paths Q from a)) :=
  M.map_id a

/-- The representable projective at `i`, with path basis in every component.-/
noncomputable def representable (k : Type u) (Q : Type v)
    [Field k] [Quiver.{w} Q] (i : Q) : QuiverRep k Q :=
  Paths.lift
    { obj := fun j ↦ ModuleCat.of k (Quiver.Path i j →₀ k)
      map := fun {a _} e ↦
        ModuleCat.ofHom (Finsupp.lmapDomain k k fun p : Quiver.Path i a ↦ p.cons e) }

private theorem representable_map_toPath (i : Q) {a b : Q} (e : a ⟶ b) :
    (representable k Q i).map e.toPath =
      ModuleCat.ofHom (Finsupp.lmapDomain k k fun p : Quiver.Path i a ↦ p.cons e) :=
  Paths.lift_toPath _ e

private theorem representable_map_single (i : Q) {a b : Q}
    (p : Quiver.Path a b) (q : Quiver.Path i a) (c : k) :
    (representable k Q i).map p (Finsupp.single q c) =
      Finsupp.single (q.comp p) c := by
  induction p with
  | nil =>
      rw [QuiverRep.map_nil, ModuleCat.id_apply]
      rfl
  | cons p e ih =>
      have hcons : (representable k Q i).map (p.cons e) =
          (representable k Q i).map p ≫ (representable k Q i).map e.toPath :=
        (representable k Q i).map_comp p e.toPath
      rw [hcons, ModuleCat.comp_apply, ih, representable_map_toPath]
      exact Finsupp.mapDomain_single

private theorem representable_map (i : Q) {a b : Q} (p : Quiver.Path a b) :
    (representable k Q i).map p =
      ModuleCat.ofHom (Finsupp.lmapDomain k k fun q : Quiver.Path i a ↦ q.comp p) := by
  refine ModuleCat.hom_ext (Finsupp.lhom_ext fun q c ↦ ?_)
  change (representable k Q i).map p (Finsupp.single q c) =
      Finsupp.mapDomain (fun r : Quiver.Path i a ↦ r.comp p) (Finsupp.single q c)
  rw [Finsupp.mapDomain_single, representable_map_single]

/-- Paths `i ⟶ j` form a basis of the `j` component of the representable at
`i`.-/
noncomputable def representableBasis (i j : Q) :
    Module.Basis (Quiver.Path i j) k
      ((representable k Q i).obj (show Paths Q from j)) :=
  Finsupp.basisSingleOne

/-- A path acts on a representable by concatenation.
@isnad1 id=eq.0h7v.s10.3c2709656be7 from=translated src=- shape=c2ed5cc5 vocab=782f73f9
-/
@[simp]
theorem representable_map_basis (i : Q) {a b : Q}
    (p : Quiver.Path a b) (q : Quiver.Path i a) :
    (representable k Q i).map p (representableBasis i a q) =
      representableBasis i b (q.comp p) :=
  representable_map_single i p q 1

/-- The morphism from a representable determined by an element at its
representing vertex.-/
noncomputable def representableHom (i : Q) (M : QuiverRep k Q)
    (x : M.obj (show Paths Q from i)) :
    representable k Q i ⟶ M where
  app j := ModuleCat.ofHom
    (Finsupp.linearCombination k fun p : Quiver.Path i j ↦ M.map p x)
  naturality {a b} p := by
    have hcomp : ∀ q : Quiver.Path i a,
        (M.map p) ((M.map q) x) = M.map (q.comp p) x := fun q ↦
      (congrArg
        (fun g : M.obj (show Paths Q from i) ⟶
            M.obj (show Paths Q from b) ↦ g x)
        (M.map_comp q p)).symm
    rw [representable_map]
    exact ModuleCat.hom_ext (Finsupp.lmapDomain_linearCombination (R := k)
      (v := fun q : Quiver.Path i a ↦ M.map q x)
      (v' := fun r : Quiver.Path i b ↦ M.map r x)
      (fun q : Quiver.Path i a ↦ q.comp p) (M.map p).hom hcomp)

/--
@isnad1 id=eq.0h7v.s10.cc6b2953c018 from=translated src=- shape=804ab22a vocab=b6e2ebde
-/
@[simp]
theorem representableHom_app_basis (i : Q) (M : QuiverRep k Q)
    (x : M.obj (show Paths Q from i)) (j : Q) (p : Quiver.Path i j) :
    (representableHom i M x).app j (representableBasis i j p) = M.map p x := by
  have h : (representableHom i M x).app j (representableBasis i j p) =
      (1 : k) • M.map p x := Finsupp.linearCombination_single k 1 p
  rwa [one_smul] at h

/--
@isnad1 id=eq.0h5v.s10.aece8f05a42c from=translated src=- shape=cff5731a vocab=22b8e80a
-/
theorem representableHom_app_nil (i : Q) (M : QuiverRep k Q)
    (x : M.obj (show Paths Q from i)) :
    (representableHom i M x).app i
      (representableBasis i i Quiver.Path.nil) = x := by
  simp

/--
@isnad1 id=eq.0h5v.s10.3c02baf62608 from=translated src=- shape=0be6fd50 vocab=c7c5d8cf
-/
@[simp]
theorem representableHom_app_nil_self {i : Q} {M : QuiverRep k Q}
    (f : representable k Q i ⟶ M) :
    representableHom i M
      (f.app i (representableBasis i i Quiver.Path.nil)) = f := by
  refine NatTrans.ext (funext fun j ↦ ModuleCat.hom_ext
    ((representableBasis i j).ext fun p ↦ ?_))
  have h := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (f.naturality p))
    (representableBasis i i Quiver.Path.nil)
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    representable_map_basis, Quiver.Path.nil_comp] at h
  simp only [representableHom_app_basis, h]

/-- The Yoneda-style linear equivalence between morphisms out of a
representable and the corresponding vertex component.-/
noncomputable def representableHomEquiv (i : Q) (M : QuiverRep k Q) :
    (representable k Q i ⟶ M) ≃ₗ[k]
      M.obj (show Paths Q from i) where
  toFun f := f.app i (representableBasis i i Quiver.Path.nil)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun x := representableHom i M x
  left_inv f := representableHom_app_nil_self f
  right_inv x := representableHom_app_nil i M x

/--
@isnad1 id=eq.0h5v.s11.f1b1c5886259 from=translated src=- shape=dd365f2f vocab=b7d64f61
-/
@[simp]
theorem representableHomEquiv_apply (i : Q) (M : QuiverRep k Q)
    (f : representable k Q i ⟶ M) :
    representableHomEquiv i M f =
      f.app i (representableBasis i i Quiver.Path.nil) :=
  rfl

/--
@isnad1 id=eq.0h5v.s10.4a09ae9a3ac9 from=translated src=- shape=8a800767 vocab=60522915
-/
@[simp]
theorem representableHomEquiv_symm_apply (i : Q) (M : QuiverRep k Q)
    (x : M.obj (show Paths Q from i)) :
    (representableHomEquiv i M).symm x = representableHom i M x :=
  rfl

/-- The free linear path category, realized as the full subcategory of quiver
representations on the representables.-/
abbrev Category (k : Type u) [Field k] (Q : Type v) [Quiver.{w} Q] :=
  InducedCategory (QuiverRep k Q) (representable k Q)

/-- A quiver vertex as an object of the free linear path category.-/
def obj (k : Type u) [Field k] (Q : Type v) [Quiver.{w} Q] (x : Q) :
    Category k Q :=
  x

/-- The underlying quiver vertex of an object of the free linear category.-/
def vertex (x : Category k Q) : Q :=
  x

/-- Morphisms in the free linear category are finite linear combinations of
paths, with the path direction reversed by the representable convention.-/
def homPathLinearEquiv (x y : Category k Q) :
    (x ⟶ y) ≃ₗ[k] (Quiver.Path (vertex y) (vertex x) →₀ k) :=
  InducedCategory.homLinearEquiv.trans
    ((representableHomEquiv (k := k) (Q := Q) (vertex x)
      (representable k Q (vertex y))).trans
      (representableBasis (k := k) (Q := Q) (vertex y) (vertex x)).repr)

/-- The morphism represented by one path.-/
def pathHom {x y : Category k Q}
    (p : Quiver.Path (vertex y) (vertex x)) : x ⟶ y :=
  (homPathLinearEquiv x y).symm (Finsupp.single p 1)

/-- Paths form a basis of every Hom space.-/
def homPathBasis (x y : Category k Q) :
    Module.Basis (Quiver.Path (vertex y) (vertex x)) k (x ⟶ y) :=
  Finsupp.basisSingleOne.map (homPathLinearEquiv x y).symm

/--
@isnad1 id=eq.0h5v.s10.441a6630885a from=translated src=- shape=5fedf3ee vocab=842180eb
-/
@[simp]
theorem homPathBasis_apply (x y : Category k Q)
    (p : Quiver.Path (vertex y) (vertex x)) :
    homPathBasis x y p = pathHom p := by
  apply (homPathLinearEquiv x y).injective
  simp [homPathBasis, pathHom]

/--
@isnad1 id=eq.0h5v.s10.de3c5a91720b from=translated src=- shape=92987bd2 vocab=36f43770
-/
@[simp]
theorem homPathLinearEquiv_pathHom {x y : Category k Q}
    (p : Quiver.Path (vertex y) (vertex x)) :
    homPathLinearEquiv x y (pathHom p) = Finsupp.single p 1 :=
  (homPathLinearEquiv x y).apply_symm_apply _

/--
@isnad1 id=eq.0h3v.s10.f4f0a3a685fa from=translated src=- shape=95c468ee vocab=5e2825f1
-/
@[simp]
theorem homPathLinearEquiv_id (x : Category k Q) :
    homPathLinearEquiv x x (𝟙 x) = Finsupp.single Quiver.Path.nil 1 := by
  change
    (representableBasis (k := k) (Q := Q) (vertex x) (vertex x)).repr
      (((𝟙 (representable k Q (vertex (k := k) (Q := Q) x)) :
          representable k Q (vertex (k := k) (Q := Q) x) ⟶
            representable k Q (vertex (k := k) (Q := Q) x))).app
          (show Paths Q from vertex (k := k) (Q := Q) x)
        (representableBasis (k := k) (Q := Q) (vertex x) (vertex x)
          Quiver.Path.nil)) =
      Finsupp.single Quiver.Path.nil 1
  simp

/--
@isnad1 id=eq.0h3v.s7.5fde200b60bd from=translated src=- shape=6d627d2b vocab=1289e74d
-/
@[simp]
theorem pathHom_nil (x : Category k Q) :
    pathHom (Quiver.Path.nil : Quiver.Path (vertex x) (vertex x)) = 𝟙 x := by
  apply (homPathLinearEquiv x x).injective
  simp

/-- The natural transformation underlying a path-basis morphism.
@isnad1 id=eq.0h5v.s9.aad4e849908e from=translated src=- shape=301b82b5 vocab=59e84bef
-/
theorem pathHom_hom {x y : Category k Q}
    (p : Quiver.Path (vertex y) (vertex x)) :
    (pathHom p).hom =
      representableHom (vertex x) (representable k Q (vertex y))
        (representableBasis (vertex y) (vertex x) p) := by
  apply (representableHomEquiv (vertex x)
    (representable k Q (vertex y))).injective
  apply (representableBasis (vertex y) (vertex x)).repr.injective
  change homPathLinearEquiv x y (pathHom p) = _
  simp

/--
@isnad1 id=eq.0h7v.s7.6d390396b2f3 from=translated src=- shape=59ae5179 vocab=a8c396bd
-/
@[simp, reassoc]
theorem pathHom_comp {x y z : Category k Q}
    (p : Quiver.Path (vertex y) (vertex x))
    (q : Quiver.Path (vertex z) (vertex y)) :
    pathHom p ≫ pathHom q = pathHom (q.comp p) := by
  apply InducedCategory.hom_ext
  rw [InducedCategory.comp_hom, pathHom_hom, pathHom_hom, pathHom_hom]
  apply (representableHomEquiv (vertex x)
    (representable k Q (vertex z))).injective
  rw [representableHomEquiv_apply, representableHomEquiv_apply]
  change
    (representableHom (vertex y) (representable k Q (vertex z))
      (representableBasis (vertex z) (vertex y) q)).app
        (show Paths Q from vertex (k := k) (Q := Q) x)
        ((representableHom (vertex x) (representable k Q (vertex y))
          (representableBasis (vertex y) (vertex x) p)).app
            (show Paths Q from vertex (k := k) (Q := Q) x)
            (representableBasis (vertex x) (vertex x) Quiver.Path.nil)) =
      (representableHom (vertex x) (representable k Q (vertex z))
        (representableBasis (vertex z) (vertex x) (q.comp p))).app
          (show Paths Q from vertex (k := k) (Q := Q) x)
          (representableBasis (vertex x) (vertex x) Quiver.Path.nil)
  simp

end MagnitudeConjecture.LinearPathCategory
