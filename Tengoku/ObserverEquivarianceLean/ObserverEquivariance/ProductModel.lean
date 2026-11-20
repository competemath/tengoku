import Tengoku.ObserverEquivarianceLean.ObserverEquivariance.Core

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The product model `S × Pair G`

The canonical normalized presentation datum on the product `O = S × Pair G` over an arbitrary
base category `S`, with projection `p = Prod.fst` (paper `thm:normalform`, the product side of
the strict normal form; also the model used in `ex:twist`, `sec:records`, `sec:holonomy`).

Field choices (paper, display before `thm:normalform`):
* action `(s, a) · h = (s, a h)`, identity on the base component of arrows;
* basepoints `b_s = (s, 1)`, coordinates `coord (s, a) = a`;
* reindexing `u* y = (s, y₂)` with chosen lift `χ_{u,y} = (u, *)`;
* vertical translations `ltrans g x = (𝟙, *)`.

Every hom-set of `Pair G` is a singleton, so arrows of `S × Pair G` are determined by their
first component (`productHom_ext`), which is how all coherence laws are discharged.
-/
namespace Tengoku.ObserverEquivarianceLean end Tengoku.ObserverEquivarianceLean open Tengoku.ObserverEquivarianceLean
open CategoryTheory

namespace ProductModel

/-! ## Local helpers about arrows of `S × Pair G` -/

/-- Arrows of `S × Pair G` are determined by their base component, since every hom-set of
    `Pair G` is a singleton (helper for paper `thm:normalform`, product side).
@isnad1 id=eq.1h6v.s7.73097c8d783a from=translated src=- shape=0782b35a vocab=4833e689
-/
theorem productHom_ext {S : Type*} [Category S] {G : Type*} {x y : S × Pair G}
    {f g : x ⟶ y} (h : f.1 = g.1) : f = g :=
  Prod.ext h (Subsingleton.elim _ _)

/-- The base component of an `eqToHom` in `S × Pair G` is the `eqToHom` of the base
    components (helper for paper `thm:normalform`, product side).
@isnad1 id=eq.1h4v.s6.e4136d0369cb from=translated src=- shape=9bf73f8e vocab=72d1e657
-/
@[simp] theorem eqToHom_fst {S : Type*} [Category S] {G : Type*} {x y : S × Pair G}
    (h : x = y) : (eqToHom h).1 = eqToHom (congrArg Prod.fst h) := by
  subst h; rfl

end ProductModel

open ProductModel

/-- The product model as a normalized presentation datum (paper `def:data`, product side of
    `thm:normalform`): `O = S × Pair G`, `p = Prod.fst`, right action `(s,a)·h = (s, a h)`,
    basepoints `(s, 1)`, coordinates `(s,a) ↦ a`, reindexing `u*(t,a) = (s,a)` with chosen lift
    `(u, *)`, and vertical translations `(𝟙, *)`.  Faithfulness (N6) holds because the
    `Pair G` component of every hom-set is a singleton.-/
def _root_.Tengoku.ObserverEquivarianceLean.productData (S : Type*) [Category S] (G : Type*) [Group G] :
    OEData G (CategoryTheory.Prod.fst S (Pair G)) where
  act x h := (x.1, ⟨x.2.pt * h⟩)
  act_one x := by rcases x with ⟨s, ⟨a⟩⟩; simp
  act_mul x g h := by rcases x with ⟨s, ⟨a⟩⟩; simp [mul_assoc]
  p_act _ _ := rfl
  act_free x g h e := mul_left_cancel (congrArg (fun z : S × Pair G => z.2.pt) e)
  actHom f _ := (f.1, ⟨⟩)
  actHom_id _ _ := rfl
  actHom_comp _ _ _ := rfl
  actHom_one f := productHom_ext (by simp)
  actHom_mul f g h := productHom_ext (by simp)
  p_actHom f _ := (by simp : f.1 = 𝟙 _ ≫ f.1 ≫ 𝟙 _)
  base s := (s, ⟨1⟩)
  p_base _ := rfl
  coord x := x.2.pt
  base_coord x := by rcases x with ⟨s, ⟨a⟩⟩; simp
  coord_base _ g := by simp
  reind := @fun s _ _ y _ => (s, y.2)
  p_reind _ _ _ := rfl
  chi := @fun _ _ u y hy => (u ≫ eqToHom hy.symm, ⟨⟩)
  p_chi u _ hy := (by simp : u ≫ eqToHom hy.symm = 𝟙 _ ≫ u ≫ eqToHom hy.symm)
  reind_base _ := rfl
  reind_act _ _ _ _ := rfl
  chi_act u y hy g := productHom_ext (by simp)
  ltrans _ x := (𝟙 x.1, ⟨⟩)
  p_ltrans _ _ := (eqToHom_refl _ _).symm
  reind_id y hy := Prod.ext hy.symm rfl
  chi_id y hy := productHom_ext (by simp)
  reind_comp _ _ _ _ := rfl
  chi_comp u v z hz := productHom_ext (by simp)
  p_faithful := ⟨fun {_ _} {_ _} h => productHom_ext h⟩

section ProductDataSimp

variable {S : Type*} [Category S] {G : Type*} [Group G]

/-- Action of the product model (paper `thm:normalform`): `(s, a) · h = (s, a h)`.
@isnad1 id=eq.0h4v.s6.b3faaee08627 from=translated src=- shape=6ecd396a vocab=ca290c73
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.productData_act (x : S × Pair G) (h : G) :
    (productData S G).act x h = (x.1, ⟨x.2.pt * h⟩) := rfl

/-- Morphism action of the product model (paper `thm:normalform`): `(u, *) · h = (u, *)`.
@isnad1 id=eq.0h6v.s8.8cd910f9a209 from=translated src=- shape=a57757c7 vocab=b467c567
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.productData_actHom {x y : S × Pair G} (f : x ⟶ y) (h : G) :
    (productData S G).actHom f h = (f.1, ⟨⟩) := rfl

/-- Basepoints of the product model (paper `thm:normalform`): `b_s = (s, 1)`.
@isnad1 id=eq.0h3v.s6.bc3dead2de18 from=translated src=- shape=47d15845 vocab=035a7cfd
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.productData_base (s : S) :
    (productData S G).base s = (s, ⟨1⟩) := rfl

/-- Coordinates of the product model (paper `thm:normalform`): `coord (s, a) = a`.
@isnad1 id=eq.0h3v.s6.f3b8da9cb233 from=translated src=- shape=0e8b6f3c vocab=5639b913
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.productData_coord (x : S × Pair G) :
    (productData S G).coord x = x.2.pt := rfl

/-- Reindexing of the product model (paper `thm:normalform`): `u* (t, a) = (s, a)`.
@isnad1 id=eq.1h6v.s7.c5a14c68cf0c from=translated src=- shape=a0574239 vocab=8e1c0f8f
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.productData_reind {s t : S} (u : s ⟶ t) (y : S × Pair G)
    (hy : (CategoryTheory.Prod.fst S (Pair G)).obj y = t) :
    (productData S G).reind u y hy = (s, y.2) := rfl

/-- Chosen cartesian lifts of the product model (paper `thm:normalform`): `χ_{u,y} = (u, *)`,
    with the endpoint cast `t = y₁`.
@isnad1 id=eq.1h6v.s8.849d9768b1ed from=translated src=- shape=7e578f15 vocab=f1e62fdd
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.productData_chi {s t : S} (u : s ⟶ t) (y : S × Pair G)
    (hy : (CategoryTheory.Prod.fst S (Pair G)).obj y = t) :
    (productData S G).chi u y hy = (u ≫ eqToHom hy.symm, ⟨⟩) := rfl

/-- Vertical translations of the product model (paper `def:data` (N5)): `ltrans g x = (𝟙, *)`.
@isnad1 id=eq.0h4v.s9.b42a242069df from=translated src=- shape=b8cdf95e vocab=5b0164ea
-/
@[simp] theorem _root_.Tengoku.ObserverEquivarianceLean.productData_ltrans (g : G) (x : S × Pair G) :
    (productData S G).ltrans g x = (𝟙 x.1, ⟨⟩) := rfl

end ProductDataSimp

/-- The action functor of the product model IS the product action of `thm:normalform`
    (strict functor equality): `(productData S G).actFunctor h = normalFormProductAction h`.
@isnad1 id=eq.0h3v.s6.51a165bcbe7f from=translated src=- shape=876404e3 vocab=0408702c
-/
theorem _root_.Tengoku.ObserverEquivarianceLean.productData_actFunctor (S : Type*) [Category S] (G : Type*) [Group G] (h : G) :
    (productData S G).actFunctor h = normalFormProductAction h := rfl

/-- The pair groupoid on a nonempty type is connected (paper `def:data`, Pair groupoid;
    used for connected bases such as `S = Pair({0,1})` in `ex:twist`).
@isnad1 id=isconnec.0h1v.s3.d8ce33fea043 from=translated src=- shape=1666ae32 vocab=15c8e541
-/
instance _root_.Tengoku.ObserverEquivarianceLean.isConnected_pair (X : Type*) [Nonempty X] : IsConnected (Pair X) := by
  haveI : Nonempty (Pair X) := ⟨⟨Classical.arbitrary X⟩⟩
  exact zigzag_isConnected (fun a b => Zigzag.of_hom (⟨⟩ : a ⟶ b))
-- Tengoku: root names of this library moved to Tengoku.ObserverEquivarianceLean so they do not collide with other libraries (generated)
