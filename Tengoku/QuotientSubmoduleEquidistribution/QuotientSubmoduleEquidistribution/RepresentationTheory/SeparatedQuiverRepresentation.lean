import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.RepresentationTheory.SeparatedQuiver
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.Foundation.RepresentationTheory.Quiver.Representation.Basic
import Tengoku.Seed.CategoryTheory.PathCategory.MorphismProperty

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coordinate data for representations of a separated quiver
-/

set_option autoImplicit false
noncomputable section

open CategoryTheory

namespace QuotientSubmoduleEquidistribution.SeparatedQuiver

universe uK uV v w

variable (K : Type uK) (V : Type uV)
variable [Field K] [Quiver.{v} V]

/-- Vertex spaces and arrow maps for the bipartite separated quiver.-/
structure RepresentationData where
  plus : V → ModuleCat.{w} K
  minus : V → ModuleCat.{w} K
  arrow : ∀ {i j : V}, (i ⟶ j) → (plus i ⟶ minus j)

namespace RepresentationData

variable {K V}

/-- A morphism of separated-quiver coordinate data.-/
structure Hom (D E : RepresentationData.{uK, uV, v, w} K V) where
  plus : ∀ i, D.plus i ⟶ E.plus i
  minus : ∀ i, D.minus i ⟶ E.minus i
  comm : ∀ {i j : V} (e : i ⟶ j),
    D.arrow e ≫ minus j = plus i ≫ E.arrow e

/--
@isnad1 id=eq.2h6v.s7.852b8feafe60 from=translated src=- shape=5c954622 vocab=a876cee4
-/
@[ext]
theorem Hom.ext {D E : RepresentationData.{uK, uV, v, w} K V}
    {f g : Hom D E} (hplus : f.plus = g.plus)
    (hminus : f.minus = g.minus) : f = g := by
  cases f
  cases g
  simp_all

instance category :
    Category (RepresentationData.{uK, uV, v, w} K V) where
  Hom := Hom
  id D :=
    { plus := fun _ ↦ 𝟙 _
      minus := fun _ ↦ 𝟙 _
      comm := by simp }
  comp f g :=
    { plus := fun i ↦ f.plus i ≫ g.plus i
      minus := fun i ↦ f.minus i ≫ g.minus i
      comm := by
        intro i j e
        rw [← Category.assoc, f.comm e, Category.assoc,
          g.comm e, ← Category.assoc] }
  assoc := by intros; ext <;> rfl
  id_comp := by intros; ext <;> simp
  comp_id := by intros; ext <;> simp

/-- Coordinate data as a prefunctor on the arrows of the separated quiver.-/
def toPrefunctor
    (D : RepresentationData.{uK, uV, v, w} K V) :
    Vertex V ⥤q ModuleCat.{w} K where
  obj
    | Sum.inl i => D.plus i
    | Sum.inr i => D.minus i
  map {a b} e := by
    cases a with
    | inl i =>
        cases b with
        | inl j => exact PEmpty.elim e
        | inr j => exact D.arrow e
    | inr i =>
        cases b with
        | inl j => exact PEmpty.elim e
        | inr j => exact PEmpty.elim e

/-- Coordinate data determine a representation of the separated quiver.-/
def toQuiverRep
    (D : RepresentationData.{uK, uV, v, w} K V) :
    QuotientSubmoduleEquidistribution.Foundation.QuiverRep K (Vertex V) :=
  CategoryTheory.Paths.lift D.toPrefunctor

/--
@isnad1 id=eq.0h4v.s6.dd294ffdc6a4 from=translated src=- shape=1dda83cc vocab=b0f31d1f
-/
@[simp]
theorem toQuiverRep_obj_plus
    (D : RepresentationData.{uK, uV, v, w} K V) (i : V) :
    D.toQuiverRep.obj (Sum.inl i) = D.plus i := rfl

/--
@isnad1 id=eq.0h4v.s6.052d55ee7ef2 from=translated src=- shape=1dda83cc vocab=59436736
-/
@[simp]
theorem toQuiverRep_obj_minus
    (D : RepresentationData.{uK, uV, v, w} K V) (i : V) :
    D.toQuiverRep.obj (Sum.inr i) = D.minus i := rfl

/--
@isnad1 id=eq.0h6v.s7.9d61ab7efa4f from=translated src=- shape=fbe4d3e0 vocab=b811d04c
-/
@[simp]
theorem toQuiverRep_map_arrow
    (D : RepresentationData.{uK, uV, v, w} K V)
    {i j : V} (e : i ⟶ j) :
    D.toQuiverRep.map
        (Quiver.Hom.toPath
          (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e)) =
      D.arrow e := by
  first
    | (all_goals grind; done)
    | (all_goals simp_all; done)
    | (all_goals aesop; done)
    | (all_goals omega; done)
    | (all_goals norm_num; done)
    | (all_goals positivity; done)
    | (all_goals linarith; done)
    | (all_goals decide; done)
    | (all_goals tauto; done)

/-- A coordinate morphism induces a natural transformation of quiver
representations.-/
def toQuiverRepMap
    {D E : RepresentationData.{uK, uV, v, w} K V} (f : D ⟶ E) :
    D.toQuiverRep ⟶ E.toQuiverRep :=
  CategoryTheory.Paths.liftNatTrans
    (fun x ↦ match x with
      | Sum.inl i => f.plus i
      | Sum.inr i => f.minus i)
    (by
      intro a b e
      cases a with
      | inl i =>
          cases b with
          | inl j => exact PEmpty.elim e
          | inr j =>
              simpa only [toQuiverRep_obj_plus, toQuiverRep_obj_minus,
                toQuiverRep_map_arrow] using f.comm e
      | inr i =>
          cases b with
          | inl j => exact PEmpty.elim e
          | inr j => exact PEmpty.elim e)

/-- The functor from coordinate data to separated-quiver representations.-/
def toQuiverRepFunctor :
    RepresentationData.{uK, uV, v, w} K V ⥤
      QuotientSubmoduleEquidistribution.Foundation.QuiverRep K (Vertex V) where
  obj := toQuiverRep
  map := toQuiverRepMap
  map_id D := by
    ext x
    cases x <;> rfl
  map_comp f g := by
    ext x
    cases x <;> rfl

/-- Restrict a separated-quiver representation to its vertex spaces and
length-one arrow maps.-/
def ofQuiverRep (M : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K (Vertex V)) :
    RepresentationData.{uK, uV, v, w} K V where
  plus i := M.obj (Sum.inl i)
  minus i := M.obj (Sum.inr i)
  arrow e := M.map (Quiver.Hom.toPath e)

/-- A natural transformation restricts to a coordinate morphism.-/
def ofQuiverRepMap {M N : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K (Vertex V)} (f : M ⟶ N) :
    ofQuiverRep M ⟶ ofQuiverRep N where
  plus i := f.app (Sum.inl i)
  minus i := f.app (Sum.inr i)
  comm := by
    intro i j e
    exact f.naturality
      (Quiver.Hom.toPath
        (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e))

/-- The restriction functor from separated-quiver representations to
coordinate data.-/
def ofQuiverRepFunctor :
    QuotientSubmoduleEquidistribution.Foundation.QuiverRep K (Vertex V) ⥤
      RepresentationData.{uK, uV, v, w} K V where
  obj := ofQuiverRep
  map := ofQuiverRepMap
  map_id M := by
    apply Hom.ext <;> funext i <;> rfl
  map_comp f g := by
    apply Hom.ext <;> funext i <;> rfl

/--
@isnad1 id=faithful.0h2v.s5.0ab186236337 from=translated src=- shape=6143a9dc vocab=6743cdf0
-/
instance toQuiverRepFunctor_faithful :
    (toQuiverRepFunctor (K := K) (V := V)).Faithful where
  map_injective := by
    intro D E f g h
    apply Hom.ext
    · funext i
      exact congrArg (fun q ↦ q.app (Sum.inl i)) h
    · funext i
      exact congrArg (fun q ↦ q.app (Sum.inr i)) h

/--
@isnad1 id=full.0h2v.s5.59a9d01ff853 from=translated src=- shape=6143a9dc vocab=bb66f6cf
-/
instance toQuiverRepFunctor_full :
    (toQuiverRepFunctor (K := K) (V := V)).Full where
  map_surjective := by
    intro D E f
    let g : D ⟶ E :=
      { plus := fun i ↦ f.app (Sum.inl i)
        minus := fun i ↦ f.app (Sum.inr i)
        comm := by
          intro i j e
          have h := f.naturality
            (Quiver.Hom.toPath
              (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e))
          change D.toQuiverRep.map
                (Quiver.Hom.toPath
                  (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e)) ≫
                f.app (Sum.inr j) =
              f.app (Sum.inl i) ≫ E.toQuiverRep.map
                (Quiver.Hom.toPath
                  (show (Sum.inl i : Vertex V) ⟶ Sum.inr j from e)) at h
          rw [toQuiverRep_map_arrow, toQuiverRep_map_arrow] at h
          change D.arrow e ≫ f.app (Sum.inr j) =
            f.app (Sum.inl i) ≫ E.arrow e at h
          exact h }
    refine ⟨g, ?_⟩
    ext x
    cases x <;> rfl

/-- Reconstructing a representation from its vertex spaces and arrow maps
gives a naturally isomorphic representation.-/
def toOfQuiverRepIso (M : QuotientSubmoduleEquidistribution.Foundation.QuiverRep K (Vertex V)) :
    (toQuiverRepFunctor (K := K) (V := V)).obj
        ((ofQuiverRepFunctor (K := K) (V := V)).obj M) ≅ M :=
  CategoryTheory.Paths.liftNatIso
    (fun x ↦ match x with
      | Sum.inl i => Iso.refl (M.obj (Sum.inl i))
      | Sum.inr i => Iso.refl (M.obj (Sum.inr i)))
    (by
      intro a b e
      cases a with
      | inl i =>
          cases b with
          | inl j => exact PEmpty.elim e
          | inr j =>
              change (ofQuiverRep M).toQuiverRep.map
                    (Quiver.Hom.toPath e) ≫ 𝟙 _ =
                𝟙 _ ≫ M.map (Quiver.Hom.toPath e)
              rw [toQuiverRep_map_arrow]
              change M.map (Quiver.Hom.toPath e) ≫ 𝟙 _ =
                𝟙 _ ≫ M.map (Quiver.Hom.toPath e)
              simp
      | inr i =>
          cases b with
          | inl j => exact PEmpty.elim e
          | inr j => exact PEmpty.elim e)

/--
@isnad1 id=esssurj.0h2v.s5.6da58db87b54 from=translated src=- shape=6143a9dc vocab=760289d5
-/
instance toQuiverRepFunctor_essSurj :
    (toQuiverRepFunctor (K := K) (V := V)).EssSurj where
  mem_essImage M :=
    ⟨ofQuiverRep M, ⟨toOfQuiverRepIso M⟩⟩

/--
@isnad1 id=isequiva.0h2v.s5.369fedb20858 from=translated src=- shape=6143a9dc vocab=3f277d81
-/
instance toQuiverRepFunctor_isEquivalence :
    (toQuiverRepFunctor (K := K) (V := V)).IsEquivalence where

/-- Coordinate data are categorically equivalent to representations of the
literal separated quiver.-/
def quiverRepEquivalence :
    RepresentationData.{uK, uV, v, w} K V ≌
      QuotientSubmoduleEquidistribution.Foundation.QuiverRep K (Vertex V) :=
  (toQuiverRepFunctor (K := K) (V := V)).asEquivalence

end RepresentationData

end QuotientSubmoduleEquidistribution.SeparatedQuiver
