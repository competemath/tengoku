/-
Copyright (c) 2026 Arthur Freitas Ramos, David Hulak, Ruy de Queiroz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Hulak, Ruy de Queiroz
-/
module

public import Tengoku.LeanPool.LeanPool.FiniteGraphFundamentalGroup.TopologicalCover
public import Tengoku.LeanPool.LeanPool.FiniteGraphFundamentalGroup.Consequences
public import Tengoku
import Tengoku.LeanPool.LeanPool.FiniteGraphFundamentalGroup.TreeContraction

/-!
# Comparison of combinatorial and topological fundamental groups

This module identifies the free-groupoid computation with the fundamental group of the realization.
-/

@[expose] public section

attribute [local implicit_reducible]
  Quiver.Symmetrify Quiver.FreeGroupoid Quiver.FreeGroupoid.of IsFreeGroupoid.Generators
  WideSubquiver WideSubquiver.toType WideSubquiver.quiver IsFreeGroupoid.quiverGenerators
  Quiver.symmetrifyQuiver Quiver.wideSubquiverSymmetrify

open Set Function
open CategoryTheory CategoryTheory.SingleObj Quiver
open unitInterval
open ContinuousMap

noncomputable section

universe u

namespace FiniteGraphFreeGroup

variable {V : Type u} [Quiver.{u} V]

/-- Evaluates a symmetric path in the canonical cover as a base free-groupoid morphism. -/
def coverSymPathValue {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    (graphCoverSymmetricFreeGroupoidMap root).obj a ⟶
      (graphCoverSymmetricFreeGroupoidMap root).obj b :=
  (CategoryTheory.Paths.lift (graphCoverSymmetricFreeGroupoidMap root)).map p

/--
@isnad1 id=eq.0h7v.s8.5e14c9bd0cea from=translated src=- shape=f909b6a3 vocab=faca35b2
-/
theorem coverSymPathValue_cons {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) b c) :
    coverSymPathValue (@Quiver.Path.cons (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) _ _ _ p e) =
      coverSymPathValue p ≫ (graphCoverSymmetricFreeGroupoidMap root).map e := by
  exact CategoryTheory.Paths.lift_cons (graphCoverSymmetricFreeGroupoidMap root) p e

/--
@isnad1 id=eq.0h5v.s8.f79ce2327082 from=translated src=- shape=1e34e599 vocab=00963961
-/
theorem graphCoverSymmetricFreeGroupoidMap_endpoint {root : V}
    {y z : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) y z) :
    (z : graphCoverVertex root).2 =
      (y : graphCoverVertex root).2 ≫
        (graphCoverSymmetricFreeGroupoidMap root).map e := by
  change graphCoverVertex root at y z
  cases e using Sum.casesOn with
  | inl e =>
      exact e.property.symm
  | inr e =>
      change z.2 = y.2 ≫ Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.1)
      simpa only [Groupoid.inv_eq_inv] using (IsIso.eq_comp_inv _).2 e.property

/--
@isnad1 id=eq.0h4v.s7.280c9d327026 from=translated src=- shape=3eeae688 vocab=b3e30cef
-/
theorem coverSymPathValue_endpoint {root : V} (x : graphCoverVertex root)
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) x) :
    x.2 = coverSymPathValue p := by
  induction p using
      (@Quiver.Path.rec (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))) with
  | nil =>
      rfl
  | @cons y z p e ih =>
      change graphCoverVertex root at y z
      rw [coverSymPathValue_cons]
      exact (graphCoverSymmetricFreeGroupoidMap_endpoint e).trans
        (congrArg (fun q => q ≫ (graphCoverSymmetricFreeGroupoidMap root).map e) ih)

/-- Evaluates a symmetric path in the base graph's free groupoid. -/
abbrev baseSymPathValue {a b : Symmetrify V}
    (p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b) :
    (Quiver.FreeGroupoid.of V).obj a ⟶ (Quiver.FreeGroupoid.of V).obj b :=
  Quot.mk _ p

/--
@isnad1 id=eq.0h5v.s7.5f583f43e2ef from=translated src=- shape=435d3814 vocab=cac815a0
-/
theorem coverSymPathValue_eq_baseSymPathValue {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    coverSymPathValue p =
      baseSymPathValue ((graphCoverProjection root).symmetrify.mapPath p) := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [coverSymPathValue_cons, ih]
      cases e using Sum.casesOn <;> rfl
/-- Sends every graph edge to its generator in the free group on total edges. -/
def graphFreeGroupPrefunctor {V : Type u} [Quiver.{u} V] :
    V ⥤q CategoryTheory.SingleObj (FreeGroup (Quiver.Total V)) where
  obj _ := ()
  map e := FreeGroup.of ⟨_, _, e⟩

/-- Extracts the monoid value represented by a morphism in a one-object category. -/
abbrev singleObjHomValue {M : Type u}
    {x y : CategoryTheory.SingleObj M} (f : x ⟶ y) : M := f

/-- The functor from the free graph groupoid to the free group on total edges. -/
abbrev graphFreeGroupoidToFreeGroup {V : Type u} [Quiver.{u} V] :
    Quiver.FreeGroupoid V ⥤ CategoryTheory.SingleObj (FreeGroup (Quiver.Total V)) :=
  Quiver.FreeGroupoid.lift (graphFreeGroupPrefunctor (V := V))

/-- The signed base-edge letter represented by an edge of the symmetric cover. -/
def coverSymEdgeLetter {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    Quiver.Total V × Bool := by
  cases e using Sum.casesOn with
  | inl e => exact (⟨_, _, e.1⟩, true)
  | inr e => exact (⟨_, _, e.1⟩, false)

/-- The signed base-edge word represented by a path in the symmetric cover. -/
def coverSymPathWord {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    List (Quiver.Total V × Bool) := by
  induction p with
  | nil => exact []
  | cons p e ih => exact coverSymEdgeLetter e :: ih

/--
@isnad1 id=eq.0h7v.s6.b1614617ffe2 from=translated src=- shape=7e725b47 vocab=16785266
-/
theorem coverSymPathWord_cons {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) b c) :
    coverSymPathWord
      (@Quiver.Path.cons (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root)) _ _ _ p e) =
      coverSymEdgeLetter e :: coverSymPathWord p := by
  rfl

/-- Paths in a symmetrified quiver that never immediately traverse an edge and its reverse. -/
inductive symPathNoBacktrack {W : Type u} [Quiver.{u} W]
    {a : Symmetrify W} : ∀ {b : Symmetrify W},
      @Quiver.Path (Symmetrify W) (Quiver.symmetrifyQuiver W) a b → Prop
  | nil : symPathNoBacktrack
      (@Quiver.Path.nil (Symmetrify W) (Quiver.symmetrifyQuiver W) a)
  | cons {b c : Symmetrify W}
      (p : @Quiver.Path (Symmetrify W) (Quiver.symmetrifyQuiver W) a b)
      (e : @Quiver.Hom (Symmetrify W) (Quiver.symmetrifyQuiver W) b c) :
      symPathNoBacktrack p →
      (∀ {d : Symmetrify W}
        (q : @Quiver.Path (Symmetrify W) (Quiver.symmetrifyQuiver W) a d)
        (f : @Quiver.Hom (Symmetrify W) (Quiver.symmetrifyQuiver W) d b),
        p = @Quiver.Path.cons (Symmetrify W) (Quiver.symmetrifyQuiver W)
          _ _ _ q f →
          (⟨b, c, e⟩ : Quiver.Total (Symmetrify W)) ≠
            ⟨b, d, Quiver.reverse f⟩) →
      symPathNoBacktrack
        (@Quiver.Path.cons (Symmetrify W) (Quiver.symmetrifyQuiver W)
          _ _ _ p e)

/--
@isnad1 id=sympathn.1h4v.s5.5e79fd8fd08b from=translated src=- shape=b497851f vocab=5bd9e162
-/
theorem symPathNoBacktrack_of_shortest {W : Type u} [Quiver.{u} W]
    {r a : Symmetrify W}
    (p : @Quiver.Path (Symmetrify W) (Quiver.symmetrifyQuiver W) r a)
    (hshort : ∀ q : @Quiver.Path (Symmetrify W)
      (Quiver.symmetrifyQuiver W) r a, p.length ≤ q.length) :
    symPathNoBacktrack p := by
  induction p using
      (@Quiver.Path.rec (Symmetrify W) (Quiver.symmetrifyQuiver W)) with
  | nil =>
      exact symPathNoBacktrack.nil
  | @cons b c p e ih =>
      apply symPathNoBacktrack.cons p e
      · apply ih
        intro q
        have h := hshort
          (@Quiver.Path.cons (Symmetrify W) (Quiver.symmetrifyQuiver W)
            _ _ _ q e)
        simp only [Quiver.Path.length_cons] at h ⊢
        omega
      · intro d q f hpq hcancel
        have hc : c = d := congrArg Quiver.Total.right hcancel
        cases hc
        have h := hshort q
        rw [hpq] at h
        simp only [Quiver.Path.length_cons] at h
        omega

/--
@isnad1 id=eq.2h7v.s7.34617b6c8b61 from=translated src=- shape=2ee97538 vocab=1f7e3498
-/
theorem coverSymEdgeLetter_cancel {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (f : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) b c)
    (hbase : (coverSymEdgeLetter e).1 = (coverSymEdgeLetter f).1)
    (hbool : (coverSymEdgeLetter e).2 = !(coverSymEdgeLetter f).2) :
    (⟨b, c, e⟩ : Quiver.Total (Symmetrify (graphCoverVertex root))) =
      ⟨b, a, Quiver.reverse f⟩ := by
  change graphCoverVertex root at a b c
  cases e using Sum.casesOn with
  | inl e =>
      cases f using Sum.casesOn with
      | inl f => simp [coverSymEdgeLetter] at hbool
      | inr f =>
          have htot :
              (⟨b.1, c.1, e.1⟩ : Quiver.Total V) =
                ⟨b.1, a.1, f.1⟩ := by
            simpa [coverSymEdgeLetter] using hbase
          have hstar := graphCoverStarEquiv_map_eq_of_total_eq
            b ⟨b, c, e⟩ ⟨b, a, f⟩ rfl rfl htot
          have hstar' := (graphCoverStarEquiv root b).injective hstar
          have htotal := graphCover_total_eq_of_star_eq
            b ⟨b, c, e⟩ ⟨b, a, f⟩ rfl rfl hstar'
          cases htotal
          rfl
  | inr e =>
      cases f using Sum.casesOn with
      | inr f => simp [coverSymEdgeLetter] at hbool
      | inl f =>
          have htot :
              (⟨c.1, b.1, e.1⟩ : Quiver.Total V) =
                ⟨a.1, b.1, f.1⟩ := by
            simpa [coverSymEdgeLetter] using hbase
          have hcostar := graphCoverCostarEquiv_map_eq_of_total_eq
            b ⟨c, b, e⟩ ⟨a, b, f⟩ rfl rfl htot
          have hcostar' := (graphCoverCostarEquiv root b).injective hcostar
          have htotal := graphCover_total_eq_of_costar_eq
            b ⟨c, b, e⟩ ⟨a, b, f⟩ rfl rfl hcostar'
          cases htotal
          rfl

/--
@isnad1 id=isreduce.1h4v.s6.b9ab60ab30d3 from=translated src=- shape=bf696369 vocab=7104c897
-/
theorem coverSymPathWord_isReduced {root : V}
    {a : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a)
    (hp : symPathNoBacktrack p) :
    FreeGroup.IsReduced (coverSymPathWord p) := by
  induction hp with
  | nil =>
      exact FreeGroup.IsReduced.nil
  | @cons b c p e hp hlast ih =>
      rw [coverSymPathWord_cons]
      cases p with
      | nil =>
          exact FreeGroup.IsReduced.singleton
      | @cons d b q f =>
          rw [coverSymPathWord_cons]
          rw [FreeGroup.isReduced_cons_cons]
          constructor
          · intro hbase
            by_contra hbool
            have hopp : (coverSymEdgeLetter e).2 =
                !(coverSymEdgeLetter f).2 := Bool.eq_not_iff.mpr hbool
            have htotal := coverSymEdgeLetter_cancel f e hbase hopp
            exact hlast q f rfl htotal
          · exact ih

/-- Evaluates a symmetric cover path in the free group on base edges. -/
abbrev coverFreeGroupValue {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    FreeGroup (Quiver.Total V) :=
  singleObjHomValue ((graphFreeGroupoidToFreeGroup (V := V)).map
    (coverSymPathValue p))

/--
@isnad1 id=eq.0h3v.s5.f5ff605dbab5 from=translated src=- shape=3c2439ab vocab=56db7a4f
-/
theorem coverFreeGroupValue_nil {root : V} (x : graphCoverVertex root) :
    coverFreeGroupValue
      (Quiver.Path.nil : @Quiver.Path (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root)) x x) = 1 := by
  change (1 : FreeGroup (Quiver.Total V)) = 1
  rfl

/--
@isnad1 id=eq.0h7v.s8.52b80ffc0a9f from=translated src=- shape=29f89d86 vocab=043c321b
-/
theorem coverFreeGroupValue_cons {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) b c) :
    coverFreeGroupValue (@Quiver.Path.cons (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) _ _ _ p e) =
      singleObjHomValue ((graphFreeGroupoidToFreeGroup (V := V)).map
          ((graphCoverSymmetricFreeGroupoidMap root).map e)) *
        coverFreeGroupValue p := by
  unfold coverFreeGroupValue
  rw [coverSymPathValue_cons, Functor.map_comp, SingleObj.comp_as_mul]

/--
@isnad1 id=eq.0h2v.s7.5a43a25c2dd2 from=translated src=- shape=bf42d0b5 vocab=0235afb5
-/
theorem graphFreeGroupoidToFreeGroup_map_pos {V : Type u} [Quiver.{u} V]
    (e : Quiver.Total V) :
    singleObjHomValue ((graphFreeGroupoidToFreeGroup (V := V)).map
      ((Quiver.FreeGroupoid.of V).map e.hom)) =
      FreeGroup.of e := by
  change (Quiver.FreeGroupoid.lift (graphFreeGroupPrefunctor (V := V))).map
      ((Quiver.FreeGroupoid.of V).map e.hom) =
      (graphFreeGroupPrefunctor (V := V)).map e.hom
  have h := Quiver.FreeGroupoid.lift_spec (graphFreeGroupPrefunctor (V := V))
  have hm := congrArg (fun ψ => ψ.map e.hom) h
  have hm' : singleObjHomValue
        ((Quiver.FreeGroupoid.lift (graphFreeGroupPrefunctor (V := V))).map
          ((Quiver.FreeGroupoid.of V).map e.hom)) =
      singleObjHomValue ((graphFreeGroupPrefunctor (V := V)).map e.hom) := by
    exact hm
  simpa [graphFreeGroupPrefunctor] using hm'

/--
@isnad1 id=eq.0h5v.s8.8eebc22d4d41 from=translated src=- shape=50a784cd vocab=f97eddd2
-/
theorem coverFreeGroupMap_letter {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    singleObjHomValue ((graphFreeGroupoidToFreeGroup (V := V)).map
      ((graphCoverSymmetricFreeGroupoidMap root).map e)) =
      FreeGroup.mk [coverSymEdgeLetter e] := by
  cases e using Sum.casesOn with
  | inl e =>
      rw [graphCoverSymmetricFreeGroupoidMap_map_pos]
      have h := graphFreeGroupoidToFreeGroup_map_pos
        (V := V) (⟨_, _, e.1⟩ : Quiver.Total V)
      exact h
  | inr e =>
      change singleObjHomValue ((graphFreeGroupoidToFreeGroup (V := V)).map
        (Groupoid.inv ((Quiver.FreeGroupoid.of V).map e.1))) = _
      rw [Groupoid.inv_eq_inv, Functor.map_inv, SingleObj.inv_as_inv]
      have h := graphFreeGroupoidToFreeGroup_map_pos
        (V := V) (⟨_, _, e.1⟩ : Quiver.Total V)
      exact congrArg (fun q => q⁻¹) h

/--
@isnad1 id=eq.0h6v.s7.11477afb909f from=translated src=- shape=a739e91a vocab=ac8295cc
-/
theorem coverFreeGroupValue_cons_letter {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a)
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    coverFreeGroupValue
      (@Quiver.Path.cons (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) _ _ _ p e) =
      FreeGroup.mk [coverSymEdgeLetter e] * coverFreeGroupValue p := by
  rw [coverFreeGroupValue_cons, coverFreeGroupMap_letter]

/--
@isnad1 id=eq.0h4v.s5.1823c8647a13 from=translated src=- shape=e39aedcc vocab=cfb43132
-/
theorem coverFreeGroupValue_eq_word {root : V}
    {a : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a) :
    coverFreeGroupValue p = FreeGroup.mk (coverSymPathWord p) := by
  induction p using
      (@Quiver.Path.rec (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))) with
  | nil =>
      change (1 : FreeGroup (Quiver.Total V)) = FreeGroup.mk []
      exact FreeGroup.one_eq_mk
  | @cons y z p e ih =>
      rw [coverFreeGroupValue_cons_letter, ih, FreeGroup.mul_mk]
      rfl

/--
@isnad1 id=eq.0h5v.s6.fc61701da86c from=translated src=- shape=0fc25e6e vocab=f02473d2
-/
theorem coverSymPathWord_length {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    (coverSymPathWord p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [coverSymPathWord_cons, List.length_cons, Quiver.Path.length_cons]
      simp [ih]

/--
@isnad1 id=eq.0h5v.s6.c34adcb22540 from=translated src=- shape=8bb9f1c6 vocab=f7d1ab24
-/
theorem coverFreeGroupValue_eq_of_endpoint {root : V}
    {a : Symmetrify (graphCoverVertex root)}
    (p q : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a) :
    coverFreeGroupValue p = coverFreeGroupValue q := by
  have hvalue : coverSymPathValue p = coverSymPathValue q :=
    (coverSymPathValue_endpoint a p).symm.trans
      (coverSymPathValue_endpoint a q)
  exact congrArg (fun h => singleObjHomValue
    ((graphFreeGroupoidToFreeGroup (V := V)).map h)) hvalue

/--
@isnad1 id=eq.1h7v.s7.5ef9bfa83c46 from=translated src=- shape=96fd4699 vocab=8082ef74
-/
theorem coverSymEdge_star_eq_of_letter_eq {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (f : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a c)
    (h : coverSymEdgeLetter e = coverSymEdgeLetter f) :
    (⟨b, e⟩ : Quiver.Star a) = ⟨c, f⟩ := by
  change graphCoverVertex root at a b c
  cases e using Sum.casesOn with
  | inl e =>
      cases f using Sum.casesOn with
      | inl f =>
          have htot :
              (⟨a.1, b.1, e.1⟩ : Quiver.Total V) =
                ⟨a.1, c.1, f.1⟩ := by
            simpa [coverSymEdgeLetter] using congrArg Prod.fst h
          have hstar := graphCoverStarEquiv_map_eq_of_total_eq
            a ⟨a, b, e⟩ ⟨a, c, f⟩ rfl rfl htot
          have hstar' := (graphCoverStarEquiv root a).injective hstar
          cases hstar'
          rfl
      | inr f => simp [coverSymEdgeLetter] at h
  | inr e =>
      cases f using Sum.casesOn with
      | inl f => simp [coverSymEdgeLetter] at h
      | inr f =>
          have htot :
              (⟨b.1, a.1, e.1⟩ : Quiver.Total V) =
                ⟨c.1, a.1, f.1⟩ := by
            simpa [coverSymEdgeLetter] using congrArg Prod.fst h
          have hcostar := graphCoverCostarEquiv_map_eq_of_total_eq
            a ⟨b, a, e⟩ ⟨c, a, f⟩ rfl rfl htot
          have hcostar' := (graphCoverCostarEquiv root a).injective hcostar
          cases hcostar'
          rfl

/--
@isnad1 id=heq.1h7v.s6.fb6783df0291 from=translated src=- shape=f912ce46 vocab=b2ae3f4d
-/
theorem coverSymEdge_eq_of_letter_eq {root : V}
    {a b c : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b)
    (f : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a c)
    (h : coverSymEdgeLetter e = coverSymEdgeLetter f) : HEq e f := by
  have hstar := coverSymEdge_star_eq_of_letter_eq e f h
  exact (Sigma.ext_iff.mp hstar).2

/--
@isnad1 id=eq.1h6v.s7.daa25de43cff from=translated src=- shape=816d35bf vocab=ff6df224
-/
theorem coverSymPathStar_eq_of_word_eq {root : V}
    {a b : Symmetrify (graphCoverVertex root)}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a)
    (q : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) b)
    (h : coverSymPathWord p = coverSymPathWord q) :
    (⟨a, p⟩ : Σ c : Symmetrify (graphCoverVertex root),
      @Quiver.Path (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))
        (graphCoverRootVertex root) c) =
      ⟨b, q⟩ := by
  induction p using
      (@Quiver.Path.rec (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))) generalizing b with
  | nil =>
      cases q with
      | nil => rfl
      | cons q f => cases h
  | @cons c d p e ih =>
      cases q with
      | nil => cases h
      | @cons c' d' q f =>
          have h' : coverSymEdgeLetter e :: coverSymPathWord p =
              coverSymEdgeLetter f :: coverSymPathWord q := by
            simpa [coverSymPathWord] using h
          injection h' with hhead htail
          have hpq := ih q htail
          cases hpq
          have hstar := coverSymEdge_star_eq_of_letter_eq e f hhead
          cases hstar
          rfl

/--
@isnad1 id=eq.2h5v.s7.ed91ac865fdc from=translated src=- shape=3f8c27b2 vocab=ca33e553
-/
theorem coverSymPath_eq_of_same_endpoint_of_noBacktrack {root : V}
    {a : Symmetrify (graphCoverVertex root)}
    (p q : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a)
    (hp : symPathNoBacktrack p) (hq : symPathNoBacktrack q) : p = q := by
  classical
  have hgroup := coverFreeGroupValue_eq_of_endpoint p q
  rw [coverFreeGroupValue_eq_word p, coverFreeGroupValue_eq_word q] at hgroup
  have hword : coverSymPathWord p = coverSymPathWord q := by
    have hred := FreeGroup.reduce.sound hgroup
    simpa [(coverSymPathWord_isReduced p hp).reduce_eq,
      (coverSymPathWord_isReduced q hq).reduce_eq] using hred
  have hstar := coverSymPathStar_eq_of_word_eq p q hword
  exact eq_of_heq (Sigma.ext_iff.mp hstar).2

/--
@isnad1 id=rootedco.0h2v.s4.331adb3e59d6 from=translated src=- shape=0f05ea3a vocab=4c6eda60
-/
theorem graphCoverSymmetric_rootedConnected {V : Type u} [Quiver.{u} V]
    (root : V) :
    @RootedConnected (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) := by
  refine ⟨?_⟩
  intro x
  rcases x with ⟨v, p⟩
  refine Quot.inductionOn p ?_
  intro p
  let φ := (graphCoverProjection root).symmetrify
  obtain ⟨⟨x, q⟩, hq⟩ :=
    ((graphCoverProjection_isCovering root).symmetrify.pathStar_bijective
      (graphCoverRootVertex root)).2 ⟨v, p⟩
  have hqparts := Sigma.mk.inj_iff.mp hq
  obtain ⟨hq', hq''⟩ := hqparts
  change x.1 = v at hq'
  cases hq'
  have hmap : φ.mapPath q = p := eq_of_heq hq''
  have hx2 : x.2 = baseSymPathValue p := by
    have hx2' := (coverSymPathValue_endpoint x q).trans
      (coverSymPathValue_eq_baseSymPathValue q)
    rw [hmap] at hx2'
    exact hx2'
  have hx : x = ⟨x.1, Quot.mk _ p⟩ := by
    refine Sigma.ext (x := x) (y := ⟨x.1, Quot.mk _ p⟩) rfl ?_
    exact heq_of_eq hx2
  rw [← hx]
  exact ⟨q⟩

/--
@isnad1 id=rootedco.0h2v.s4.331adb3e59d6 from=translated src=- shape=0f05ea3a vocab=4c6eda60
-/
noncomputable instance graphCoverSymmetricRootedConnected
    {V : Type u} [Quiver.{u} V] (root : V) :
    @RootedConnected (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) :=
  graphCoverSymmetric_rootedConnected root

/-- The canonical geodesic spanning tree of the symmetrified graph cover. -/
noncomputable def graphCoverSymmetricTree {V : Type u} [Quiver.{u} V]
    (root : V) :
    WideSubquiver (Symmetrify (graphCoverVertex root)) :=
  geodesicSubtree (graphCoverRootVertex root)

noncomputable instance graphCoverSymmetricTreeArborescence
    {V : Type u} [Quiver.{u} V] (root : V) :
    Quiver.Arborescence (graphCoverSymmetricTree root) := by
  dsimp [graphCoverSymmetricTree]
  exact @Quiver.geodesicArborescence
    (Symmetrify (graphCoverVertex root))
    (Quiver.symmetrifyQuiver (graphCoverVertex root))
    (graphCoverRootVertex root)
    (graphCoverSymmetricRootedConnected root)

/--
@isnad1 id=or.0h5v.s7.6c6b62e07b23 from=translated src=- shape=0ee69d51 vocab=eabcb958
-/
theorem graphCoverSymmetric_edge_or_reverse_mem_tree {V : Type u} [Quiver.{u} V]
    (root : V)
    {a b : Symmetrify (graphCoverVertex root)}
    (e : @Quiver.Hom (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    e ∈ graphCoverSymmetricTree root a b ∨
      Quiver.reverse e ∈ graphCoverSymmetricTree root b a := by
  classical
  change e ∈ @geodesicSubtree (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) _ a b ∨
    Quiver.reverse e ∈ @geodesicSubtree (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) _ b a
  generalize hP : @shortestPath (Symmetrify (graphCoverVertex root))
    (Quiver.symmetrifyQuiver (graphCoverVertex root))
    (graphCoverRootVertex root) _ a = p
  have hp : symPathNoBacktrack p := by
    apply symPathNoBacktrack_of_shortest p
    intro q
    rw [← hP]
    exact @shortest_path_spec (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) _ a q
  by_cases hnb : symPathNoBacktrack (p.cons e)
  · left
    change ∃ q : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) a,
      @shortestPath (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))
        (graphCoverRootVertex root) _ b = q.cons e
    refine ⟨p, ?_⟩
    have hq : symPathNoBacktrack (@shortestPath
        (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))
        (graphCoverRootVertex root) _ b) := by
      apply symPathNoBacktrack_of_shortest
      intro q
      exact @shortest_path_spec (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))
        (graphCoverRootVertex root) _ b q
    exact (coverSymPath_eq_of_same_endpoint_of_noBacktrack
      (p.cons e) (@shortestPath (Symmetrify (graphCoverVertex root))
        (Quiver.symmetrifyQuiver (graphCoverVertex root))
        (graphCoverRootVertex root) _ b) hnb hq).symm
  · cases p with
    | nil =>
        exfalso
        apply hnb
        apply symPathNoBacktrack.cons (Quiver.Path.nil) e
          symPathNoBacktrack.nil
        intro d q f hpq hcancel
        exact (Quiver.Path.nil_ne_cons q f) hpq
    | @cons d a q f =>
        have hnot : ¬ ((⟨a, b, e⟩ : Quiver.Total
            (Symmetrify (graphCoverVertex root))) ≠
            ⟨a, d, Quiver.reverse f⟩) := by
          intro hne
          apply hnb
          apply symPathNoBacktrack.cons (q.cons f) e hp
          intro d' q' f' hpq' hcancel'
          have hdd : d = d' :=
            Quiver.Path.obj_eq_of_cons_eq_cons hpq'
          cases hdd
          have hff : HEq f f' :=
            Quiver.Path.hom_heq_of_cons_eq_cons hpq'
          have hff' : f = f' := eq_of_heq hff
          cases hff'
          exact hne hcancel'
        have htotal : (⟨a, b, e⟩ : Quiver.Total
            (Symmetrify (graphCoverVertex root))) =
            ⟨a, d, Quiver.reverse f⟩ := Classical.not_not.mp hnot
        right
        have hbd : b = d := (Quiver.Total.ext_iff.mp htotal).2.1
        cases hbd
        have hef : e = Quiver.reverse f :=
          eq_of_heq (Quiver.Total.ext_iff.mp htotal).2.2
        change ∃ r : @Quiver.Path (Symmetrify (graphCoverVertex root))
          (Quiver.symmetrifyQuiver (graphCoverVertex root))
          (graphCoverRootVertex root) b,
          @shortestPath (Symmetrify (graphCoverVertex root))
            (Quiver.symmetrifyQuiver (graphCoverVertex root))
            (graphCoverRootVertex root) _ a =
            r.cons (Quiver.reverse e)
        have hfmem : f ∈ @geodesicSubtree (Symmetrify (graphCoverVertex root))
            (Quiver.symmetrifyQuiver (graphCoverVertex root))
            (graphCoverRootVertex root) _ b a := by
          change ∃ r : @Quiver.Path (Symmetrify (graphCoverVertex root))
            (Quiver.symmetrifyQuiver (graphCoverVertex root))
            (graphCoverRootVertex root) b,
            @shortestPath (Symmetrify (graphCoverVertex root))
              (Quiver.symmetrifyQuiver (graphCoverVertex root))
              (graphCoverRootVertex root) _ a = r.cons f
          exact ⟨q, hP⟩
        change ∃ r : @Quiver.Path (Symmetrify (graphCoverVertex root))
          (Quiver.symmetrifyQuiver (graphCoverVertex root))
          (graphCoverRootVertex root) b,
          @shortestPath (Symmetrify (graphCoverVertex root))
            (Quiver.symmetrifyQuiver (graphCoverVertex root))
            (graphCoverRootVertex root) _ a = r.cons f at hfmem
        rw [hef, Quiver.reverse_reverse]
        exact hfmem

/-- The representative-level realization map induced by a signed edge map. -/
def graphRealizationSignedPreMap {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I)) :
    graphRealizationPre U → graphRealizationPre W :=
  Sum.elim
    (fun v => Sum.inl (graphDiscreteVertex (f (graphVertexUnderlying v))))
    (fun z =>
      let e := graphEdgeUnderlying z.1
      Sum.inr ⟨graphDiscreteEdge (g e), r e z.2⟩)

/--
@isnad1 id=continuo.0h5v.s8.ae9132e22a7a from=translated src=- shape=bb4ea56f vocab=0dfc2108
-/
theorem graphRealizationSignedPreMap_continuous
    {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I)) :
    Continuous (graphRealizationSignedPreMap f g r) := by
  apply continuous_sumElim.2
  constructor
  · exact continuous_inl.comp continuous_of_discreteTopology
  · apply continuous_inr.comp
    apply continuous_sigma
    intro e
    change Continuous (fun t : I =>
      (⟨graphDiscreteEdge (g (graphEdgeUnderlying e)),
        r (graphEdgeUnderlying e) t⟩ :
        Σ _e : WithDiscreteTopology (Quiver.Total W), I))
    exact (continuous_sigmaMk (i :=
      graphDiscreteEdge (g (graphEdgeUnderlying e)))).comp
      (r (graphEdgeUnderlying e)).continuous

/-- The continuous realization map induced by a signed edge map. -/
def graphRealizationSignedMap {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I))
    (h0 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 0⟩) =
        graphVertex (f e.left))
    (h1 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 1⟩) =
        graphVertex (f e.right)) :
    graphRealization U → graphRealization W := by
  let F : graphRealizationPre U → graphRealization W := fun x =>
    graphRealizationQuotient (graphRealizationSignedPreMap f g r x)
  refine Quotient.lift F ?_
  intro x y h
  induction h with
  | rel x y h =>
      cases h with
      | source e => simpa [F, graphRealizationSignedPreMap] using h0 e
      | target e => simpa [F, graphRealizationSignedPreMap] using h1 e
  | refl x => rfl
  | symm x y h ih => exact ih.symm
  | trans x y z hxy hyz ihxy ihyz => exact ihxy.trans ihyz

/--
@isnad1 id=continuo.2h5v.s9.6dcd718e7cd6 from=translated src=- shape=36fb0abb vocab=d771e649
-/
theorem continuous_graphRealizationSignedMap
    {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I))
    (h0 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 0⟩) =
        graphVertex (f e.left))
    (h1 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 1⟩) =
        graphVertex (f e.right)) :
    Continuous (graphRealizationSignedMap f g r h0 h1) := by
  let F : graphRealizationPre U → graphRealization W := fun x =>
    graphRealizationQuotient (graphRealizationSignedPreMap f g r x)
  have hcont : Continuous F :=
    continuous_quotient_mk'.comp (graphRealizationSignedPreMap_continuous f g r)
  change Continuous (Quotient.lift F _)
  exact hcont.quotient_lift _

/--
@isnad1 id=eq.2h6v.s8.0642840d5de0 from=translated src=- shape=17180def vocab=2bf562c5
-/
@[simp]
theorem graphRealizationSignedMap_vertex
    {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I))
    (h0 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 0⟩) =
        graphVertex (f e.left))
    (h1 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 1⟩) =
        graphVertex (f e.right))
    (v : U) :
    graphRealizationSignedMap f g r h0 h1 (graphVertex v) = graphVertex (f v) := rfl

/--
@isnad1 id=eq.2h7v.s10.b66993553d58 from=translated src=- shape=702c9f1c vocab=614a2fc6
-/
@[simp]
theorem graphRealizationSignedMap_edgePath
    {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (f : U → W) (g : Quiver.Total U → Quiver.Total W)
    (r : Quiver.Total U → C(I, I))
    (h0 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 0⟩) =
        graphVertex (f e.left))
    (h1 : ∀ e : Quiver.Total U,
      graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (g e), r e 1⟩) =
        graphVertex (f e.right))
    (e : Quiver.Total U) (t : I) :
    graphRealizationSignedMap f g r h0 h1 (graphEdgePath e t) =
      graphEdgePath (g e) (r e t) := rfl

/-- The underlying cover edge represented by an edge of the symmetric cover tree. -/
def graphCoverTreeEdgeBase {V : Type u} [Quiver.{u} V]
    (root : V)
    (d : Quiver.Total (graphCoverSymmetricTree root)) :
    Quiver.Total (graphCoverVertex root) := by
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f using Sum.casesOn with
  | inl e => exact ⟨a, b, e⟩
  | inr e => exact ⟨b, a, e⟩

/-- The orientation of a symmetric cover-tree edge relative to its underlying cover edge. -/
def graphCoverTreeEdgeSign {V : Type u} [Quiver.{u} V]
    (root : V)
    (d : Quiver.Total (graphCoverSymmetricTree root)) : Bool := by
  cases d.hom.1 using Sum.casesOn with
  | inl _ => exact true
  | inr _ => exact false

/-- The specification for choosing the symmetric tree edge above an underlying cover edge. -/
def graphCoverTreeEdgeChoiceProperty {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root))
    (d : Quiver.Total (graphCoverSymmetricTree root)) : Prop :=
  graphCoverTreeEdgeBase root d = e

/--
@isnad1 id=nonempty.0h3v.s6.ed489ba6b8e3 from=translated src=- shape=5c458fc2 vocab=7c125ca7
-/
theorem graphCoverTreeEdgeChoice_exists {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) :
    Nonempty {d : Quiver.Total (graphCoverSymmetricTree root) //
      graphCoverTreeEdgeChoiceProperty root e d} := by
  have hr := graphCoverSymmetric_edge_or_reverse_mem_tree root (Sum.inl e.hom)
  rcases hr with hpos | hneg
  · exact ⟨⟨⟨(show Symmetrify (graphCoverVertex root) from e.left),
        (show Symmetrify (graphCoverVertex root) from e.right),
        ⟨Sum.inl e.hom, hpos⟩⟩, by
      change (⟨e.left, e.right, e.hom⟩ : Quiver.Total (graphCoverVertex root)) = e
      rfl⟩⟩
  · exact ⟨⟨⟨(show Symmetrify (graphCoverVertex root) from e.right),
        (show Symmetrify (graphCoverVertex root) from e.left),
        ⟨Sum.inr e.hom, hneg⟩⟩, by
      change (⟨e.left, e.right, e.hom⟩ : Quiver.Total (graphCoverVertex root)) = e
      rfl⟩⟩

/-- Chooses a symmetric tree edge above an underlying cover edge. -/
noncomputable def graphCoverTreeEdgeChoice {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) :
    Quiver.Total (graphCoverSymmetricTree root) :=
  (Classical.choice (graphCoverTreeEdgeChoice_exists root e)).1

/--
@isnad1 id=eq.0h3v.s5.77bc47d5e4ef from=translated src=- shape=6955162d vocab=a6a483b3
-/
theorem graphCoverTreeEdgeChoice_base {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) :
    graphCoverTreeEdgeBase root (graphCoverTreeEdgeChoice root e) = e :=
  (Classical.choice (graphCoverTreeEdgeChoice_exists root e)).2

/-- Forgets membership in the symmetric cover tree from a tree vertex. -/
def graphCoverTreeVertexForget {V : Type u} [Quiver.{u} V]
    (root : V)
    (v : graphCoverSymmetricTree root) : graphCoverVertex root := by
  change graphCoverVertex root at v
  exact v

/-- The continuous orientation-reversing involution of the unit interval. -/
def graphRealizationIntervalSymm : C(I, I) where
  toFun := σ
  continuous_toFun := by fun_prop

/--
@isnad1 id=eq.0h1v.s6.9b0ff8dd34b9 from=translated src=- shape=c12b8144 vocab=765de4c3
-/
@[simp]
theorem graphRealizationIntervalSymm_apply (t : I) :
    graphRealizationIntervalSymm t = σ t := rfl

/--
@isnad1 id=eq.0h0v.s6.2cf9051d21f8 from=translated src=- shape=ada2fd0c vocab=f344d120
-/
theorem graphRealizationIntervalSymm_zero :
    graphRealizationIntervalSymm 0 = 1 := by simp [graphRealizationIntervalSymm]

/--
@isnad1 id=eq.0h0v.s6.6208ace7738e from=translated src=- shape=ada2fd0c vocab=f344d120
-/
theorem graphRealizationIntervalSymm_one :
    graphRealizationIntervalSymm 1 = 0 := by simp [graphRealizationIntervalSymm]

/--
@isnad1 id=eq.0h1v.s7.2037a3a92051 from=translated src=- shape=087868fb vocab=f344d120
-/
theorem graphRealizationIntervalSymm_symm (t : I) :
    graphRealizationIntervalSymm (graphRealizationIntervalSymm t) = t := by
  apply Subtype.ext
  simp [graphRealizationIntervalSymm]

/-- The interval coordinate used when folding the symmetric cover tree into the cover. -/
def graphCoverTreeFoldCoordinate {V : Type u} [Quiver.{u} V]
    (root : V)
    (d : Quiver.Total (graphCoverSymmetricTree root)) : C(I, I) := by
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f using Sum.casesOn with
  | inl _ => exact ContinuousMap.id I
  | inr _ => exact graphRealizationIntervalSymm

/--
@isnad1 id=eq.1h5v.s8.535f584e3646 from=translated src=- shape=ed0e7233 vocab=3a0f83d7
-/
theorem graphCoverTreeFoldCoordinate_positive {V : Type u} [Quiver.{u} V]
    (root : V) {a b : graphCoverVertex root}
    (e : a ⟶ b) (h : Sum.inl e ∈ graphCoverSymmetricTree root a b) :
    graphCoverTreeFoldCoordinate root
        ⟨a, b, ⟨Sum.inl e, h⟩⟩ = ContinuousMap.id I := by
  rfl

/--
@isnad1 id=eq.1h5v.s8.7e8254a1401d from=translated src=- shape=838ac285 vocab=009bfea0
-/
theorem graphCoverTreeFoldCoordinate_negative {V : Type u} [Quiver.{u} V]
    (root : V) {a b : graphCoverVertex root}
    (e : a ⟶ b) (h : Sum.inr e ∈ graphCoverSymmetricTree root b a) :
    graphCoverTreeFoldCoordinate root
        ⟨b, a, ⟨Sum.inr e, h⟩⟩ = graphRealizationIntervalSymm := by
  rfl

/--
@isnad1 id=eq.0h3v.s8.8067344eb493 from=translated src=- shape=7a5ad1c5 vocab=27b98830
-/
theorem graphCoverTreeFold_h0 {V : Type u} [Quiver.{u} V]
    (root : V) (d : Quiver.Total (graphCoverSymmetricTree root)) :
    graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (graphCoverTreeEdgeBase root d),
            graphCoverTreeFoldCoordinate root d 0⟩) =
        graphVertex (graphCoverTreeVertexForget root d.left) := by
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f using Sum.casesOn with
  | inl e =>
      change graphEdgePath (⟨a, b, e⟩ : Quiver.Total (graphCoverVertex root)) 0 =
        graphVertex (graphCoverTreeVertexForget root a)
      rw [graphEdgePath_zero]
      rfl
  | inr e =>
      dsimp [graphCoverTreeEdgeBase, graphCoverTreeFoldCoordinate,
        graphRealizationIntervalSymm]
      rw [show σ (0 : I) = 1 by simp]
      change graphEdgePath (⟨b, a, e⟩ : Quiver.Total (graphCoverVertex root)) 1 =
        graphVertex (graphCoverTreeVertexForget root a)
      rw [graphEdgePath_one]
      rfl

/--
@isnad1 id=eq.0h3v.s8.8c7572ea7037 from=translated src=- shape=7a5ad1c5 vocab=47fa4ad7
-/
theorem graphCoverTreeFold_h1 {V : Type u} [Quiver.{u} V]
    (root : V) (d : Quiver.Total (graphCoverSymmetricTree root)) :
    graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (graphCoverTreeEdgeBase root d),
            graphCoverTreeFoldCoordinate root d 1⟩) =
        graphVertex (graphCoverTreeVertexForget root d.right) := by
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f using Sum.casesOn with
  | inl e =>
      change graphEdgePath (⟨a, b, e⟩ : Quiver.Total (graphCoverVertex root)) 1 =
        graphVertex (graphCoverTreeVertexForget root b)
      rw [graphEdgePath_one]
      rfl
  | inr e =>
      dsimp [graphCoverTreeEdgeBase, graphCoverTreeFoldCoordinate,
        graphRealizationIntervalSymm]
      rw [show σ (1 : I) = 0 by simp]
      change graphEdgePath (⟨b, a, e⟩ : Quiver.Total (graphCoverVertex root)) 0 =
        graphVertex (graphCoverTreeVertexForget root b)
      rw [graphEdgePath_zero]
      rfl

/-- The realization map folding the symmetric cover tree onto the canonical cover. -/
noncomputable def graphCoverTreeToCover {V : Type u} [Quiver.{u} V]
    (root : V) :
    graphRealization (graphCoverSymmetricTree root) →
      graphRealization (graphCoverVertex root) :=
  graphRealizationSignedMap
    (graphCoverTreeVertexForget root)
    (graphCoverTreeEdgeBase root)
    (graphCoverTreeFoldCoordinate root)
    (graphCoverTreeFold_h0 root)
    (graphCoverTreeFold_h1 root)

/--
@isnad1 id=continuo.0h2v.s9.ba577f60fb8b from=translated src=- shape=af163c0a vocab=c0e83289
-/
theorem continuous_graphCoverTreeToCover {V : Type u} [Quiver.{u} V]
    (root : V) :
    Continuous (graphCoverTreeToCover root) :=
  continuous_graphRealizationSignedMap _ _ _ _ _

/--
@isnad1 id=eq.0h3v.s6.8b577e1a2d0f from=translated src=- shape=7354432e vocab=b7f41613
-/
@[simp]
theorem graphCoverTreeToCover_vertex {V : Type u} [Quiver.{u} V]
    (root : V) (v : graphCoverSymmetricTree root) :
    graphCoverTreeToCover root (graphVertex v) =
      graphVertex (graphCoverTreeVertexForget root v) := rfl

/--
@isnad1 id=eq.0h4v.s11.18f4a5c2ed98 from=translated src=- shape=4b7044ff vocab=3b2eca14
-/
@[simp]
theorem graphCoverTreeToCover_edgePath {V : Type u} [Quiver.{u} V]
    (root : V)
    (e : Quiver.Total (graphCoverSymmetricTree root)) (t : I) :
    graphCoverTreeToCover root (graphEdgePath e t) =
      graphEdgePath (graphCoverTreeEdgeBase root e)
        (graphCoverTreeFoldCoordinate root e t) := rfl

/-- Embeds a canonical-cover vertex into the symmetric cover tree. -/
def graphCoverVertexEmbed {V : Type u} [Quiver.{u} V]
    (root : V) (v : graphCoverVertex root) :
    graphCoverSymmetricTree root := by
  change graphCoverVertex root at v
  exact v

/-- The signed interval coordinate used by the section from the cover to its tree model. -/
noncomputable def graphCoverSectionCoordinate {V : Type u} [Quiver.{u} V]
    (root : V)
    (e : Quiver.Total (graphCoverVertex root)) : C(I, I) :=
  match graphCoverTreeEdgeSign root (graphCoverTreeEdgeChoice root e) with
  | true => ContinuousMap.id I
  | false => graphRealizationIntervalSymm

/--
@isnad1 id=eq.1h3v.s6.d2ff0fa75dd6 from=translated src=- shape=e28ef0a7 vocab=0ed139be
-/
theorem graphCoverSectionCoordinate_positive {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root))
    (h : graphCoverTreeEdgeSign root (graphCoverTreeEdgeChoice root e) = true) :
    graphCoverSectionCoordinate root e = ContinuousMap.id I := by
  simp [graphCoverSectionCoordinate, h]

/--
@isnad1 id=eq.1h3v.s6.b3954d68c989 from=translated src=- shape=d10efce5 vocab=c08c9962
-/
theorem graphCoverSectionCoordinate_negative {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root))
    (h : graphCoverTreeEdgeSign root (graphCoverTreeEdgeChoice root e) = false) :
    graphCoverSectionCoordinate root e = graphRealizationIntervalSymm := by
  simp [graphCoverSectionCoordinate, h]

/--
@isnad1 id=eq.0h3v.s8.59a81ba7656f from=translated src=- shape=3c5e53c4 vocab=512a6b55
-/
theorem graphCoverSection_h0 {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) :
    graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (graphCoverTreeEdgeChoice root e),
            graphCoverSectionCoordinate root e 0⟩) =
        graphVertex (graphCoverVertexEmbed root e.left) := by
  classical
  let d := graphCoverTreeEdgeChoice root e
  have hbase : graphCoverTreeEdgeBase root d = e :=
    graphCoverTreeEdgeChoice_base root e
  have hd : graphCoverTreeEdgeChoice root e = d := rfl
  dsimp [graphCoverSectionCoordinate]
  rw [hd]
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f using Sum.casesOn with
  | inl f =>
      change graphEdgePath
          (⟨a, b, ⟨Sum.inl f, hf⟩⟩ :
            Quiver.Total (graphCoverSymmetricTree root)) 0 =
        graphVertex (graphCoverVertexEmbed root e.left)
      rw [graphEdgePath_zero]
      have he : (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
        simpa [graphCoverTreeEdgeBase] using hbase
      cases he
      rfl
  | inr f =>
      have hs : graphCoverTreeEdgeSign root
          ⟨(show Symmetrify (graphCoverVertex root) from a),
            (show Symmetrify (graphCoverVertex root) from b),
            ⟨Sum.inr f, hf⟩⟩ = false := rfl
      rw [hs]
      rw [show graphRealizationIntervalSymm 0 = 1 by simp]
      change graphEdgePath
          (⟨(show Symmetrify (graphCoverVertex root) from a),
            (show Symmetrify (graphCoverVertex root) from b),
            ⟨Sum.inr f, hf⟩⟩ :
            Quiver.Total (graphCoverSymmetricTree root)) 1 =
        graphVertex (graphCoverVertexEmbed root e.left)
      rw [graphEdgePath_one]
      have he : (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
        simpa [graphCoverTreeEdgeBase] using hbase
      cases he
      rfl

/--
@isnad1 id=eq.0h3v.s8.af6fe1453e6f from=translated src=- shape=3c5e53c4 vocab=957de0fb
-/
theorem graphCoverSection_h1 {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root)) :
    graphRealizationQuotient
          (Sum.inr ⟨graphDiscreteEdge (graphCoverTreeEdgeChoice root e),
            graphCoverSectionCoordinate root e 1⟩) =
        graphVertex (graphCoverVertexEmbed root e.right) := by
  classical
  let d := graphCoverTreeEdgeChoice root e
  have hbase : graphCoverTreeEdgeBase root d = e :=
    graphCoverTreeEdgeChoice_base root e
  have hd : graphCoverTreeEdgeChoice root e = d := rfl
  dsimp [graphCoverSectionCoordinate]
  rw [hd]
  rcases d with ⟨a, b, ⟨f, hf⟩⟩
  change graphCoverVertex root at a b
  cases f using Sum.casesOn with
  | inl f =>
      change graphEdgePath
          (⟨a, b, ⟨Sum.inl f, hf⟩⟩ :
            Quiver.Total (graphCoverSymmetricTree root)) 1 =
        graphVertex (graphCoverVertexEmbed root e.right)
      rw [graphEdgePath_one]
      have he : (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
        simpa [graphCoverTreeEdgeBase] using hbase
      cases he
      rfl
  | inr f =>
      have hs : graphCoverTreeEdgeSign root
          ⟨(show Symmetrify (graphCoverVertex root) from a),
            (show Symmetrify (graphCoverVertex root) from b),
            ⟨Sum.inr f, hf⟩⟩ = false := rfl
      rw [hs]
      rw [show graphRealizationIntervalSymm 1 = 0 by simp]
      change graphEdgePath
          (⟨(show Symmetrify (graphCoverVertex root) from a),
            (show Symmetrify (graphCoverVertex root) from b),
            ⟨Sum.inr f, hf⟩⟩ :
            Quiver.Total (graphCoverSymmetricTree root)) 0 =
        graphVertex (graphCoverVertexEmbed root e.right)
      rw [graphEdgePath_zero]
      have he : (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
        simpa [graphCoverTreeEdgeBase] using hbase
      cases he
      rfl

/-- A continuous section from the canonical cover realization to its symmetric tree model. -/
noncomputable def graphCoverToTree {V : Type u} [Quiver.{u} V]
    (root : V) :
    graphRealization (graphCoverVertex root) →
      graphRealization (graphCoverSymmetricTree root) :=
  graphRealizationSignedMap
    (graphCoverVertexEmbed root)
    (graphCoverTreeEdgeChoice root)
    (graphCoverSectionCoordinate root)
    (graphCoverSection_h0 root)
    (graphCoverSection_h1 root)

/--
@isnad1 id=continuo.0h2v.s9.848c74795500 from=translated src=- shape=bd095431 vocab=23e2340d
-/
theorem continuous_graphCoverToTree {V : Type u} [Quiver.{u} V]
    (root : V) :
    Continuous (graphCoverToTree root) :=
  continuous_graphRealizationSignedMap _ _ _ _ _

/--
@isnad1 id=eq.0h3v.s6.38386544ed75 from=translated src=- shape=26518680 vocab=08fd392e
-/
@[simp]
theorem graphCoverToTree_vertex {V : Type u} [Quiver.{u} V]
    (root : V) (v : graphCoverVertex root) :
    graphCoverToTree root (graphVertex v) =
      graphVertex (graphCoverVertexEmbed root v) := rfl

/--
@isnad1 id=eq.0h4v.s11.72ff8e3e1991 from=translated src=- shape=9d2028b7 vocab=34d68c36
-/
@[simp]
theorem graphCoverToTree_edgePath {V : Type u} [Quiver.{u} V]
    (root : V) (e : Quiver.Total (graphCoverVertex root))
    (t : I) :
    graphCoverToTree root (graphEdgePath e t) =
      graphEdgePath (graphCoverTreeEdgeChoice root e)
        (graphCoverSectionCoordinate root e t) := rfl

/--
@isnad1 id=eq.2h4v.s9.6ee9503c1b37 from=translated src=- shape=45ed43e7 vocab=29c761fe
-/
theorem graphRealization_map_ext {U W : Type u} [Quiver.{u} U] [Quiver.{u} W]
    (F G : graphRealization U → graphRealization W)
    (hv : ∀ v : U, F (graphVertex v) = G (graphVertex v))
    (he : ∀ (e : Quiver.Total U) (t : I),
      F (graphEdgePath e t) = G (graphEdgePath e t)) :
    F = G := by
  funext x
  refine Quotient.inductionOn x ?_
  intro x
  cases x using Sum.casesOn with
  | inl v => exact hv (graphVertexUnderlying v)
  | inr z =>
      rcases z with ⟨e, t⟩
      exact he (graphEdgeUnderlying e) t

/--
@isnad1 id=eq.0h3v.s4.6d242182699b from=translated src=- shape=25c58e3b vocab=18d19423
-/
theorem graphCoverTreeVertexForget_embed {V : Type u} [Quiver.{u} V]
    (root : V) (v : graphCoverVertex root) :
    graphCoverTreeVertexForget root (graphCoverVertexEmbed root v) = v := by
  rfl

/--
@isnad1 id=eq.0h2v.s6.466c2f182c00 from=translated src=- shape=ff4642c2 vocab=616b94e1
-/
theorem graphCoverTreeToCover_comp_graphCoverToTree
    {V : Type u} [Quiver.{u} V] (root : V) :
    (graphCoverTreeToCover root) ∘ (graphCoverToTree root) =
      (id : graphRealization (graphCoverVertex root) →
        graphRealization (graphCoverVertex root)) := by
  apply graphRealization_map_ext
  · intro v
    change graphCoverTreeToCover root (graphCoverToTree root (graphVertex v)) =
      graphVertex v
    rw [graphCoverToTree_vertex, graphCoverTreeToCover_vertex,
      graphCoverTreeVertexForget_embed]
  · intro e t
    change graphCoverTreeToCover root (graphCoverToTree root (graphEdgePath e t)) =
      graphEdgePath e t
    rw [graphCoverToTree_edgePath, graphCoverTreeToCover_edgePath]
    let d := graphCoverTreeEdgeChoice root e
    have hbase : graphCoverTreeEdgeBase root d = e :=
      graphCoverTreeEdgeChoice_base root e
    have hd : graphCoverTreeEdgeChoice root e = d := rfl
    dsimp [graphCoverSectionCoordinate]
    rw [hd]
    rcases d with ⟨a, b, ⟨f, hf⟩⟩
    change graphCoverVertex root at a b
    cases f using Sum.casesOn with
    | inl f =>
        change graphEdgePath
            (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root))
            ((ContinuousMap.id I) ((ContinuousMap.id I) t)) =
          graphEdgePath e t
        rw [ContinuousMap.id_apply, ContinuousMap.id_apply]
        have he : (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
          simpa [graphCoverTreeEdgeBase] using hbase
        rw [he]
    | inr f =>
        have hs : graphCoverTreeEdgeSign root
            ⟨(show Symmetrify (graphCoverVertex root) from a),
              (show Symmetrify (graphCoverVertex root) from b),
              ⟨Sum.inr f, hf⟩⟩ = false := rfl
        rw [hs]
        change graphEdgePath
            (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root))
            (graphRealizationIntervalSymm
              (graphRealizationIntervalSymm t)) =
          graphEdgePath e t
        rw [graphRealizationIntervalSymm_symm]
        have he : (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root)) = e := by
          simpa [graphCoverTreeEdgeBase] using hbase
        rw [he]

/--
@isnad1 id=eq.1h4v.s7.5cbfe9b39ff8 from=translated src=- shape=a3beee82 vocab=0a4ae7e6
-/
theorem graphCoverTreeEdgeBase_injective
    {V : Type u} [Quiver.{u} V] (root : V)
    (d₁ d₂ : Quiver.Total (graphCoverSymmetricTree root))
    (h : graphCoverTreeEdgeBase root d₁ =
      graphCoverTreeEdgeBase root d₂) : d₁ = d₂ := by
  classical
  rcases d₁ with ⟨a, b, ⟨f, hf⟩⟩
  rcases d₂ with ⟨c, d, ⟨g, hg⟩⟩
  change graphCoverVertex root at a b c d
  cases f using Sum.casesOn with
  | inl f =>
      cases g using Sum.casesOn with
      | inl g =>
          have htotal : (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root)) =
              ⟨c, d, g⟩ := by
            simpa [graphCoverTreeEdgeBase] using h
          cases htotal
          rfl
      | inr g =>
          have htotal : (⟨a, b, f⟩ : Quiver.Total (graphCoverVertex root)) =
              ⟨d, c, g⟩ := by
            simpa [graphCoverTreeEdgeBase] using h
          have hsrc : a = d := congrArg Quiver.Total.left htotal
          have htgt : b = c := congrArg Quiver.Total.right htotal
          have hhom : HEq f g := (Quiver.Total.ext_iff.mp htotal).2.2
          cases hsrc
          cases htgt
          have hhom' : f = g := eq_of_heq hhom
          cases hhom'
          exact False.elim (no_reverse_edges (graphCoverSymmetricTree root)
            f hf hg)
  | inr f =>
      cases g using Sum.casesOn with
      | inl g =>
          have htotal : (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root)) =
              ⟨c, d, g⟩ := by
            simpa [graphCoverTreeEdgeBase] using h
          have hsrc : b = c := congrArg Quiver.Total.left htotal
          have htgt : a = d := congrArg Quiver.Total.right htotal
          have hhom : HEq f g := (Quiver.Total.ext_iff.mp htotal).2.2
          cases hsrc
          cases htgt
          have hhom' : f = g := eq_of_heq hhom
          cases hhom'
          exact False.elim (no_reverse_edges (graphCoverSymmetricTree root)
            f hg hf)
      | inr g =>
          have htotal : (⟨b, a, f⟩ : Quiver.Total (graphCoverVertex root)) =
              ⟨d, c, g⟩ := by
            simpa [graphCoverTreeEdgeBase] using h
          cases htotal
          rfl

/--
@isnad1 id=eq.0h2v.s7.ebfbd7b0ca0d from=translated src=- shape=244990d9 vocab=616b94e1
-/
theorem graphCoverToTree_comp_graphCoverTreeToCover
    {V : Type u} [Quiver.{u} V] (root : V) :
    (graphCoverToTree root) ∘ (graphCoverTreeToCover root) =
      (id : graphRealization (graphCoverSymmetricTree root) →
        graphRealization (graphCoverSymmetricTree root)) := by
  apply graphRealization_map_ext
  · intro v
    change graphCoverToTree root (graphCoverTreeToCover root (graphVertex v)) =
      graphVertex v
    rw [graphCoverTreeToCover_vertex, graphCoverToTree_vertex]
    rfl
  · intro d t
    change graphCoverToTree root
        (graphCoverTreeToCover root (graphEdgePath d t)) =
      graphEdgePath d t
    rw [graphCoverTreeToCover_edgePath, graphCoverToTree_edgePath]
    have hchoice : graphCoverTreeEdgeChoice root
          (graphCoverTreeEdgeBase root d) = d := by
      apply graphCoverTreeEdgeBase_injective root
      exact graphCoverTreeEdgeChoice_base root
        (graphCoverTreeEdgeBase root d)
    dsimp [graphCoverSectionCoordinate]
    rw [hchoice]
    rcases d with ⟨a, b, ⟨f, hf⟩⟩
    change graphCoverVertex root at a b
    cases f using Sum.casesOn with
    | inl f =>
        dsimp [graphCoverSectionCoordinate, graphCoverTreeFoldCoordinate]
        change graphEdgePath
            (⟨(show Symmetrify (graphCoverVertex root) from a),
              (show Symmetrify (graphCoverVertex root) from b),
              ⟨Sum.inl f, hf⟩⟩ :
              Quiver.Total (graphCoverSymmetricTree root))
            ((ContinuousMap.id I) ((ContinuousMap.id I) t)) =
          graphEdgePath
            (⟨a, b, ⟨Sum.inl f, hf⟩⟩ :
              Quiver.Total (graphCoverSymmetricTree root)) t
        rw [ContinuousMap.id_apply, ContinuousMap.id_apply]
    | inr f =>
        dsimp [graphCoverSectionCoordinate, graphCoverTreeFoldCoordinate]
        have hs : graphCoverTreeEdgeSign root
            ⟨(show Symmetrify (graphCoverVertex root) from a),
              (show Symmetrify (graphCoverVertex root) from b),
              ⟨Sum.inr f, hf⟩⟩ = false := rfl
        rw [hs]
        change graphEdgePath
            (⟨(show Symmetrify (graphCoverVertex root) from a),
              (show Symmetrify (graphCoverVertex root) from b),
              ⟨Sum.inr f, hf⟩⟩ :
              Quiver.Total (graphCoverSymmetricTree root))
            (graphRealizationIntervalSymm
              (graphRealizationIntervalSymm t)) =
          graphEdgePath
            (⟨(show Symmetrify (graphCoverVertex root) from a),
              (show Symmetrify (graphCoverVertex root) from b),
              ⟨Sum.inr f, hf⟩⟩ :
              Quiver.Total (graphCoverSymmetricTree root)) t
        rw [graphRealizationIntervalSymm_symm]

/-- The homotopy equivalence between the canonical cover and its symmetric spanning tree. -/
noncomputable def graphCoverRealizationHomotopyEquiv
    {V : Type u} [Quiver.{u} V] (root : V) :
    graphRealization (graphCoverVertex root) ≃ₕ
      graphRealization (graphCoverSymmetricTree root) := by
  let f : C(graphRealization (graphCoverVertex root),
      graphRealization (graphCoverSymmetricTree root)) :=
    ⟨graphCoverToTree root, continuous_graphCoverToTree root⟩
  let g : C(graphRealization (graphCoverSymmetricTree root),
      graphRealization (graphCoverVertex root)) :=
    ⟨graphCoverTreeToCover root, continuous_graphCoverTreeToCover root⟩
  refine { toFun := f, invFun := g, left_inv := ?_, right_inv := ?_ }
  · have hcomp : g.comp f = ContinuousMap.id _ := by
      ext x
      exact congrFun (graphCoverTreeToCover_comp_graphCoverToTree root) x
    rw [hcomp]
  · have hcomp : f.comp g = ContinuousMap.id _ := by
      ext x
      exact congrFun (graphCoverToTree_comp_graphCoverTreeToCover root) x
    rw [hcomp]

/--
@isnad1 id=contract.0h2v.s7.84f3afc8fd99 from=translated src=- shape=bcb18a3f vocab=be9a43c5
-/
noncomputable instance graphCoverRealization_contractible
    {V : Type u} [Quiver.{u} V] (root : V) :
    ContractibleSpace (graphRealization (graphCoverVertex root)) := by
  exact (graphCoverRealizationHomotopyEquiv root).contractibleSpace

/-- Evaluates a symmetric base-graph path in the free graph groupoid. -/
abbrev graphBaseSymPathValue {V : Type u} [Quiver.{u} V]
    {a b : V}
    (p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b) :
    (Quiver.FreeGroupoid.of V).obj a ⟶ (Quiver.FreeGroupoid.of V).obj b :=
  @baseSymPathValue V _ (show Symmetrify V from a)
    (show Symmetrify V from b) p

/--
@isnad1 id=eq.0h4v.s9.231e94a07d76 from=translated src=- shape=cfd64177 vocab=c146db71
-/
theorem graphFreeGroupoidToTopological_map_path {V : Type u} [Quiver.{u} V]
    {a b : V}
    (p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b) :
    (graphFreeGroupoidToTopological (V := V)).map (graphBaseSymPathValue p) =
      FundamentalGroupoid.fromPath
        (Path.Homotopic.Quotient.mk
          (@graphRealizationQuiverPath V _ a b p)) := by
  induction p with
  | nil =>
      rfl
  | cons p e ih =>
      change (CategoryTheory.Paths.lift
        (Quiver.Symmetrify.lift (graphRealizationQuiverMap (V := V)))).map
          (@Quiver.Path.cons (Symmetrify V) (Quiver.symmetrifyQuiver V)
            _ _ _ p e) = _
      rw [CategoryTheory.Paths.lift_cons]
      have ih' :
          (CategoryTheory.Paths.lift
            (Quiver.Symmetrify.lift (graphRealizationQuiverMap (V := V)))).map p =
          FundamentalGroupoid.fromPath
            (Path.Homotopic.Quotient.mk
              (@graphRealizationQuiverPath V _ _ _ p)) := by
        exact ih
      rw [ih']
      cases e using Sum.casesOn with
      | inl e =>
          rfl
      | inr e =>
          rfl
variable {V : Type u} [Quiver.{u} V] [WeaklyConnected V]

omit [WeaklyConnected V] in
/--
@isnad1 id=ex.1h3v.s6.28febd814711 from=translated src=- shape=3fbbed11 vocab=00cc15ed
-/
theorem graphCoverRealization_fiber_vertex
    (root : V) {z : graphCoverRealization root}
    (hz : graphCoverRealizationProjection root z = graphVertex root) :
    ∃ x : graphCoverVertex root, z = graphVertex x ∧ x.1 = root := by
  revert hz
  refine Quotient.inductionOn z ?_
  intro z hz
  cases z using Sum.casesOn with
  | inl v =>
      let x : graphCoverVertex root := graphVertexUnderlying v
      have hzx : graphRealizationQuotient (Sum.inl v) = graphVertex x := by
        rfl
      have hproj : graphVertex x.1 = graphVertex root := by
        dsimp [graphCoverRealizationProjection] at hz
        change graphRealizationMap (graphCoverProjection root)
            (graphRealizationQuotient (Sum.inl v)) = graphVertex root at hz
        rw [hzx] at hz
        rw [graphRealizationMap_vertex] at hz
        exact hz
      refine ⟨x, hzx, ?_⟩
      exact graphVertex_injective hproj
  | inr z =>
      rcases z with ⟨ze, t⟩
      let e : Quiver.Total (graphCoverVertex root) := graphEdgeUnderlying ze
      have hze : ze = graphDiscreteEdge e := by
        simp [e, graphDiscreteEdge, graphEdgeUnderlying]
      have hzedge : graphRealizationQuotient
          (Sum.inr ⟨ze, t⟩) = graphEdgePath e t := by
        rw [hze]
        rfl
      have hzproj : graphEdgePath
          ⟨(graphCoverProjection root).obj e.left,
            (graphCoverProjection root).obj e.right,
            (graphCoverProjection root).map e.hom⟩ t =
          graphVertex root := by
        rw [← graphRealizationMap_edgePath (graphCoverProjection root) e t]
        rw [← hzedge]
        dsimp [graphCoverRealizationProjection] at hz
        exact hz
      have ht : t = 0 ∨ t = 1 := by
        exact graphRealization_vertex_edge_endpoint (V := V) (v := root)
          (e := ⟨(graphCoverProjection root).obj e.left,
            (graphCoverProjection root).obj e.right,
            (graphCoverProjection root).map e.hom⟩) (t := t) hzproj.symm
      rcases ht with rfl | rfl
      · refine ⟨e.left, ?_, ?_⟩
        · exact hzedge.trans (graphEdgePath_zero e)
        · exact graphVertex_injective (by
            simpa [graphCoverProjection] using hzproj)
      · refine ⟨e.right, ?_, ?_⟩
        · exact hzedge.trans (graphEdgePath_one e)
        · exact graphVertex_injective (by
            simpa [graphCoverProjection] using hzproj)

omit [WeaklyConnected V] in
/--
@isnad1 id=eq.0h5v.s9.b73304381351 from=translated src=- shape=76ebc4e4 vocab=3133e17c
-/
theorem graphCoverRealizationQuiverPath_map
    (root : V) {a b : graphCoverVertex root}
    (p : @Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root)) a b) :
    (@graphRealizationQuiverPath (graphCoverVertex root)
      (graphCoverQuiver root) a b p).map
        (continuous_graphCoverRealizationProjection root) =
      @graphRealizationQuiverPath V (inferInstance : Quiver V) a.1 b.1
        ((graphCoverProjection root).symmetrify.mapPath p) := by
  induction p with
  | nil =>
      rfl
  | cons p e ih =>
      change ((@graphRealizationQuiverPath (graphCoverVertex root)
          (graphCoverQuiver root) _ _ p).trans
          (graphRealizationSymmetricEdgePath e)).map
          (continuous_graphCoverRealizationProjection root) =
        @graphRealizationQuiverPath V (inferInstance : Quiver V) _ _
          ((graphCoverProjection root).symmetrify.mapPath
            (@Quiver.Path.cons (Symmetrify (graphCoverVertex root))
              (Quiver.symmetrifyQuiver (graphCoverVertex root)) _ _ _ p e))
      rw [Prefunctor.mapPath_cons, Path.map_trans, ih]
      cases e using Sum.casesOn with
      | inl e =>
          rfl
      | inr e =>
          rfl

/-- The distinguished point in the covering fiber over the realized root vertex. -/
def graphCoverRootFiberPoint (root : V) :
    (graphCoverRealizationProjection root) ⁻¹' {graphVertex root} :=
  ⟨graphVertex (graphCoverRootVertex root), by
    change graphVertex ((graphCoverProjection root).obj
      (graphCoverRootVertex root)) = graphVertex root
    rfl
  ⟩

/--
@isnad1 id=eq.2h6v.s8.63f31ced43b7 from=translated src=- shape=a3f7b395 vocab=fd634f36
-/
theorem graphRealizationQuiverPath_cast
    {W : Type u} [Quiver.{u} W]
    {a b a' b' : W} (ha : a = a') (hb : b = b')
    (p : @Quiver.Path (Symmetrify W) (Quiver.symmetrifyQuiver W) a b) :
    @graphRealizationQuiverPath W _ a' b' (Quiver.Path.cast ha hb p) =
      (@graphRealizationQuiverPath W _ a b p).cast
        (congrArg graphVertex ha).symm (congrArg graphVertex hb).symm := by
  cases ha
  cases hb
  rfl

/--
@isnad1 id=ex.0h3v.s10.9bd3de3a6e06 from=translated src=- shape=4e18dc4b vocab=ea33c8c4
-/
theorem graphCombinatorialToTopological_surjective_of_path
    (root : V) (γ : Path (graphVertex root) (graphVertex root)) :
    ∃ p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V)
        (show Symmetrify V from root) root,
      graphCombinatorialToTopological root (graphBaseSymPathValue p) =
        FundamentalGroup.fromPath (Path.Homotopic.Quotient.mk γ) := by
  let P := graphCoverRealizationProjection root
  let cov := graphCoverRealizationProjection_isCovering root
  let e₀ := graphCoverRootFiberPoint root
  have h₀ : γ 0 = P (e₀ : graphCoverRealization root) := by
    exact γ.source.trans e₀.2.symm
  let L := cov.liftPath γ.toContinuousMap (e₀ : graphCoverRealization root) h₀
  let z : graphCoverRealization root := L 1
  have hz : P z = graphVertex root := by
    have hL := congr_fun (cov.liftPath_lifts γ.toContinuousMap
      (e₀ : graphCoverRealization root) h₀) 1
    exact hL.trans γ.target
  obtain ⟨x, hzx, hx⟩ := graphCoverRealization_fiber_vertex root hz
  have : @RootedConnected (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (graphCoverRootVertex root) := graphCoverSymmetric_rootedConnected root
  obtain ⟨q⟩ := (inferInstance : Nonempty
    (@Quiver.Path (Symmetrify (graphCoverVertex root))
      (Quiver.symmetrifyQuiver (graphCoverVertex root))
      (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root) x))
  have hpstart : (graphCoverProjection root).symmetrify.obj
        (graphCoverRootVertex root) = (show Symmetrify V from root) := by
    rfl
  have hpend : (graphCoverProjection root).symmetrify.obj x =
        (show Symmetrify V from root) := by
    change x.1 = root
    exact hx
  let p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V)
      (show Symmetrify V from root) root :=
    Quiver.Path.cast hpstart hpend
      ((graphCoverProjection root).symmetrify.mapPath q)
  let qtop : Path (graphVertex (graphCoverRootVertex root)) (graphVertex x) :=
    @graphRealizationQuiverPath (graphCoverVertex root)
      (graphCoverQuiver root) _ _ q
  let Lpath : Path (graphVertex (graphCoverRootVertex root)) (graphVertex x) := {
    toContinuousMap := L
    source' := by
      exact cov.liftPath_zero γ.toContinuousMap (e₀ : graphCoverRealization root) h₀
    target' := hzx }
  have hpaths : Lpath.Homotopic qtop :=
    SimplyConnectedSpace.paths_homotopic Lpath qtop
  have hclasses : Path.Homotopic.Quotient.mk Lpath =
      Path.Homotopic.Quotient.mk qtop := Quotient.sound hpaths
  have hstart : graphVertex root = P (graphVertex (graphCoverRootVertex root)) :=
    e₀.2.symm
  have hxP : P (graphVertex x) = graphVertex root := by
    calc
      P (graphVertex x) = P z := congrArg P hzx.symm
      _ = graphVertex root := hz
  have htarget : graphVertex root = P (graphVertex x) := hxP.symm
  let qbase : Path (graphVertex root) (graphVertex root) :=
    (qtop.map cov.continuous).cast hstart htarget
  let Lbase : Path (graphVertex root) (graphVertex root) :=
    (Lpath.map cov.continuous).cast hstart htarget
  have hmap : Path.Homotopic.Quotient.mk γ =
      Path.Homotopic.Quotient.mk qbase := by
    have hmap' := congrArg (fun r => r.map ⟨P, cov.continuous⟩) hclasses
    rw [← Path.Homotopic.Quotient.mk_map] at hmap'
    have hcast := congrArg
      (fun r : Path.Homotopic.Quotient
          (P (graphVertex (graphCoverRootVertex root))) (P (graphVertex x)) =>
        r.cast hstart htarget) hmap'
    rw [← Path.Homotopic.Quotient.mk_map,
      ← Path.Homotopic.Quotient.mk_cast] at hcast
    have hLmap : Lbase = γ := by
      ext t
      exact congr_fun (cov.liftPath_lifts γ.toContinuousMap
        (e₀ : graphCoverRealization root) h₀) t
    rw [← hLmap]
    exact hcast
  refine ⟨p, ?_⟩
  change (graphFreeGroupoidToTopological (V := V)).map
      (graphBaseSymPathValue p) = _
  rw [graphFreeGroupoidToTopological_map_path]
  apply congrArg FundamentalGroup.fromPath
  have hqmap₀ := graphCoverRealizationQuiverPath_map root q
  have hqcast := graphRealizationQuiverPath_cast (W := V) hpstart hpend
    ((graphCoverProjection root).symmetrify.mapPath q)
  have hqmap : qbase =
      @graphRealizationQuiverPath V (inferInstance : Quiver V) root root p := by
    ext t
    calc
      qbase t = (qtop.map cov.continuous) t := rfl
      _ = (@graphRealizationQuiverPath V (inferInstance : Quiver V)
          ((graphCoverProjection root).symmetrify.obj
            (graphCoverRootVertex root))
          ((graphCoverProjection root).symmetrify.obj x)
          ((graphCoverProjection root).symmetrify.mapPath q)) t := by
        exact congrArg (fun r => r t) hqmap₀
      _ = (@graphRealizationQuiverPath V (inferInstance : Quiver V) root root p) t :=
        (congrArg (fun r => r t) hqcast).symm
  rw [← hqmap, ← hmap]

/--
@isnad1 id=surjecti.0h2v.s10.cdbad26dfa60 from=translated src=- shape=a681150a vocab=432edd42
-/
theorem graphCombinatorialToTopological_surjective
    (root : V) :
    Function.Surjective (graphCombinatorialToTopological root) := by
  intro g
  refine Quotient.inductionOn g ?_
  intro γ
  obtain ⟨p, hp⟩ := graphCombinatorialToTopological_surjective_of_path root γ
  refine ⟨graphBaseSymPathValue p, ?_⟩
  simpa [graphCombinatorialToTopological, graphFreeGroupoidToTopological] using hp

/--
@isnad1 id=heq.2h6v.s7.aa05b6d6f9fc from=translated src=- shape=cd7a1fe6 vocab=e59bebd7
-/
theorem baseSymPathValue_cast_heq
    {V : Type u} [Quiver.{u} V]
    {a b a' b' : Symmetrify V} (ha : a = a') (hb : b = b')
    (p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) a b) :
    HEq (baseSymPathValue (Quiver.Path.cast ha hb p))
      (baseSymPathValue p) := by
  cases ha
  cases hb
  rfl

private def graphCoverEndpointFiber (root : V) (x : graphCoverVertex root)
    (hx : x.1 = root) :
    graphCoverRealizationProjection root ⁻¹' {graphVertex root} :=
  ⟨graphVertex x, congrArg graphVertex hx⟩

private structure GraphLoopLiftData (root : V)
    (p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) root root) where
  endpoint : graphCoverVertex root
  lift : @Quiver.Path (Symmetrify (graphCoverVertex root))
    (Quiver.symmetrifyQuiver (graphCoverVertex root))
    (graphCoverRootVertex root) endpoint
  endpoint_base : endpoint.1 = root
  projection_value :
    HEq (baseSymPathValue ((graphCoverProjection root).symmetrify.mapPath lift))
      (baseSymPathValue p)
  monodromy_endpoint :
    (graphCoverRealizationProjection_isCovering root).monodromy
        (Path.Homotopic.Quotient.mk
          (@graphRealizationQuiverPath V _ _ _ p))
        (graphCoverRootFiberPoint root) =
      graphCoverEndpointFiber root endpoint endpoint_base

private theorem graphLoopLiftData_exists (root : V)
    (p : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) root root) :
    Nonempty (GraphLoopLiftData root p) := by
  have hpstart : (graphCoverProjection root).symmetrify.obj
        (graphCoverRootVertex root) = (show Symmetrify V from root) := by
    rfl
  let p' := Quiver.Path.cast hpstart.symm (rfl : root = root) p
  obtain ⟨⟨x, r⟩, hstar⟩ :=
    ((graphCoverProjection_isCovering root).symmetrify.pathStar_bijective
      (graphCoverRootVertex root)).2 ⟨root, p'⟩
  obtain ⟨hx, hr⟩ := Sigma.mk.inj_iff.mp hstar
  change x.1 = root at hx
  have hx' : (show Symmetrify V from root) =
      (graphCoverProjection root).symmetrify.obj x := by
    change root = x.1
    exact hx.symm
  have hr_cast : (graphCoverProjection root).symmetrify.mapPath r =
      p'.cast rfl hx' := by
    exact (Quiver.Path.eq_cast_iff_heq rfl hx' p'
      ((graphCoverProjection root).symmetrify.mapPath r)).2 hr
  let P := graphCoverRealizationProjection root
  let cov := graphCoverRealizationProjection_isCovering root
  let e₀ := graphCoverRootFiberPoint root
  let ptop : Path (graphVertex root) (graphVertex root) :=
    @graphRealizationQuiverPath V _ _ _ p
  let lift : Path (graphVertex (graphCoverRootVertex root))
      (graphVertex x) :=
    @graphRealizationQuiverPath (graphCoverVertex root)
      (graphCoverQuiver root) _ _ r
  let base : Path
      (graphVertex (V := V) ((graphCoverProjection root).symmetrify.obj
        (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root)))
      (graphVertex (V := V) ((graphCoverProjection root).symmetrify.obj x)) :=
    @graphRealizationQuiverPath V _ _ _
      ((graphCoverProjection root).symmetrify.mapPath r)
  have hmap : lift.map cov.continuous = base :=
    graphCoverRealizationQuiverPath_map root r
  have hendpoint : P (graphVertex x) = graphVertex root := by
    change graphVertex x.1 = graphVertex root
    exact congrArg graphVertex hx
  have hbase_cast : base = ptop.cast e₀.2 hendpoint := by
    dsimp [base, ptop]
    rw [hr_cast]
    have h1 := graphRealizationQuiverPath_cast (W := V)
      (rfl : (graphCoverProjection root).symmetrify.obj
        (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root) =
        (graphCoverProjection root).symmetrify.obj
          (show Symmetrify (graphCoverVertex root) from graphCoverRootVertex root))
      hx' p'
    have h2 := graphRealizationQuiverPath_cast (W := V)
      hpstart.symm (rfl : root = root) p
    rw [h1, h2]
    ext t
    rfl
  have hclass :
      (Path.Homotopic.Quotient.mk lift).map ⟨P, cov.continuous⟩ =
        (Path.Homotopic.Quotient.mk ptop).cast e₀.2 hendpoint := by
    rw [← Path.Homotopic.Quotient.mk_map, hmap, hbase_cast]
    rfl
  have hmonodromy :
      cov.monodromy (Path.Homotopic.Quotient.mk ptop) e₀ =
        graphCoverEndpointFiber root x hx := by
    exact cov.monodromy_eq_of_map_eq
      (Path.Homotopic.Quotient.mk lift) hclass
  have hpathcast : Quiver.Path.cast rfl hx' p' =
      Quiver.Path.cast hpstart.symm hx' p := by
    dsimp [p']
    rw [Quiver.Path.cast_cast]
  have hvalueeq :
      baseSymPathValue (Quiver.Path.cast rfl hx' p') =
        baseSymPathValue (Quiver.Path.cast hpstart.symm hx' p) := by
    rw [hpathcast]
  have hprojection :
      baseSymPathValue ((graphCoverProjection root).symmetrify.mapPath r) =
        baseSymPathValue (Quiver.Path.cast rfl hx' p') := by
    exact congrArg baseSymPathValue hr_cast
  have hprojection_value :
      HEq (baseSymPathValue ((graphCoverProjection root).symmetrify.mapPath r))
        (baseSymPathValue p) :=
    (heq_of_eq (hprojection.trans hvalueeq)).trans
      (baseSymPathValue_cast_heq hpstart.symm hx' p)
  exact ⟨⟨x, r, hx, hprojection_value, hmonodromy⟩⟩

private theorem graphCombinatorialToTopological_injective_of_paths
    (root : V)
    (p q : @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) root root)
    (htop : Path.Homotopic.Quotient.mk
      (@graphRealizationQuiverPath V _ _ _ p) =
      Path.Homotopic.Quotient.mk
        (@graphRealizationQuiverPath V _ _ _ q)) :
    baseSymPathValue p = baseSymPathValue q := by
  obtain ⟨pData⟩ := graphLoopLiftData_exists root p
  obtain ⟨qData⟩ := graphLoopLiftData_exists root q
  obtain ⟨xp, rp, hxp, hpvalue, hpmonodromy⟩ := pData
  obtain ⟨xq, rq, hxq, hqvalue, hqmonodromy⟩ := qData
  let P := graphCoverRealizationProjection root
  let cov := graphCoverRealizationProjection_isCovering root
  let e₀ := graphCoverRootFiberPoint root
  have hfiber :
      graphCoverEndpointFiber root xp hxp =
        graphCoverEndpointFiber root xq hxq := by
    calc
      _ = cov.monodromy
          (Path.Homotopic.Quotient.mk
            (@graphRealizationQuiverPath V _ _ _ p)) e₀ :=
        hpmonodromy.symm
      _ = cov.monodromy
          (Path.Homotopic.Quotient.mk
            (@graphRealizationQuiverPath V _ _ _ q)) e₀ := by
        rw [htop]
      _ = _ := hqmonodromy
  have hvertex :
      graphVertex (V := graphCoverVertex root) xp =
        graphVertex (V := graphCoverVertex root) xq := by
    exact congrArg (fun z : P ⁻¹' {graphVertex root} =>
      (z : graphCoverRealization root)) hfiber
  have hendpoint : xp = xq := by
    exact graphVertex_injective hvertex
  cases hendpoint
  have hlift :
      coverSymPathValue rp = coverSymPathValue rq := by
    exact (coverSymPathValue_endpoint xp rp).symm.trans
      (coverSymPathValue_endpoint xp rq)
  have hprojection :
      baseSymPathValue
          ((graphCoverProjection root).symmetrify.mapPath rp) =
        baseSymPathValue
          ((graphCoverProjection root).symmetrify.mapPath rq) := by
    rw [← coverSymPathValue_eq_baseSymPathValue rp,
      ← coverSymPathValue_eq_baseSymPathValue rq]
    exact hlift
  have hmid : HEq (baseSymPathValue p)
      (baseSymPathValue
        ((graphCoverProjection root).symmetrify.mapPath rq)) :=
    hpvalue.symm.trans (heq_of_eq hprojection)
  exact eq_of_heq (hmid.trans hqvalue)

/--
@isnad1 id=injectiv.0h2v.s10.2ced4b903a84 from=translated src=- shape=a681150a vocab=17790418
-/
theorem graphCombinatorialToTopological_injective
    (root : V) :
    Function.Injective (graphCombinatorialToTopological root) := by
  intro g h heq
  revert h
  refine Quot.inductionOn g ?_
  intro p h heq
  revert heq
  refine Quot.inductionOn h ?_
  intro q heq
  change @Quiver.Path (Symmetrify V) (Quiver.symmetrifyQuiver V) root root at p q
  apply graphCombinatorialToTopological_injective_of_paths root p q
  change (graphFreeGroupoidToTopological (V := V)).map
      (Quot.mk _ p) =
    (graphFreeGroupoidToTopological (V := V)).map (Quot.mk _ q) at heq
  change (graphFreeGroupoidToTopological (V := V)).map (graphBaseSymPathValue p) =
    (graphFreeGroupoidToTopological (V := V)).map (graphBaseSymPathValue q) at heq
  rw [graphFreeGroupoidToTopological_map_path,
    graphFreeGroupoidToTopological_map_path] at heq
  exact heq

/-- The explicit isomorphism between combinatorial and topological graph fundamental groups. -/
noncomputable def graphCombinatorialToTopologicalEquiv
    {V : Type u} [Quiver.{u} V] [WeaklyConnected V] (root : V) :
    graphFundamentalGroup root ≃*
      FundamentalGroup (graphRealization V) (graphVertex root) :=
  MulEquiv.ofBijective (graphCombinatorialToTopological root)
    ⟨graphCombinatorialToTopological_injective root,
      graphCombinatorialToTopological_surjective root⟩

/-- Identifies a finite connected graph's topological fundamental group with a free group. -/
noncomputable def graphTopologicalFundamentalGroupEquiv
    {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V]
    [WeaklyConnected V] (root : V) :
    FundamentalGroup (graphRealization V) (graphVertex root) ≃*
      FreeGroup (Fin (cycleRank (V := V))) :=
  (graphCombinatorialToTopologicalEquiv root).symm.trans
    (graphFundamentalGroupEquiv root)

/--
@isnad1 id=nonempty.0h2v.s8.899564de1c27 from=translated src=- shape=ebdfbab7 vocab=d82a70ca
-/
theorem proved_topological_fundamental_group_free_rank
    {V : Type u} [Quiver.{u} V] [Fintype V] [FiniteQuiver V]
    [WeaklyConnected V] (root : V) :
    Nonempty (FundamentalGroup (graphRealization V) (graphVertex root) ≃*
      FreeGroup (Fin (edgeCount (V := V) + 1 - vertexCount (V := V)))) := by
  exact ⟨graphTopologicalFundamentalGroupEquiv root⟩

end FiniteGraphFreeGroup
