/-
Copyright (c) 2023 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Tengoku.Seed.Algebra.Homology.HomotopyCategory.SingleFunctors

/-!
# Cochains from or to single complexes

We introduce constructors `Cochain.fromSingleMk` and `Cocycle.fromSingleMk`
for cochains and cocycles from a single complex. We also introduce similar
definitions for cochains and cocycles to a single complex.

-/

@[expose] public section

assert_not_exists TwoSidedIdeal

open CategoryTheory Category Limits Preadditive

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

namespace CochainComplex

namespace HomComplex

variable {X : C} {K : CochainComplex C ℤ}

namespace Cochain

/-- Constructor for cochains from a single complex. -/
@[nolint unusedArguments]
noncomputable def fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (_ : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n :=
  Cochain.single ((HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f) n

set_option backward.isDefEq.respectTransparency false in
variable (X K) in
/--
@isnad1 id=eq.1h6v.s9.2b1472b8944b from=seed src=0 shape=884e8e9b vocab=d8d9abef
-/
@[simp]
lemma fromSingleMk_zero (p q n : ℤ) (h : p + n = q) :
    fromSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [fromSingleMk]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h7v.s9.131c6f052bd5 from=seed src=0 shape=997fe6ce vocab=f49f9057
-/
@[simp]
lemma fromSingleMk_v {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    (fromSingleMk f h).v p q h =
      (HomologicalComplex.singleObjXSelf (.up ℤ) p X).hom ≫ f := by
  simp [fromSingleMk]

/--
@isnad1 id=eq.3h9v.s9.d1fc09984086 from=seed src=0 shape=572f045c vocab=edf3b172
-/
lemma fromSingleMk_v_eq_zero {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (p' q' : ℤ) (hpq' : p' + n = q') (hp' : p' ≠ p) :
    (fromSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.2h9v.s8.592610f851ea from=seed src=0 shape=e61ceb65 vocab=eb28f9d3
-/
lemma δ_fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (n' q' : ℤ) (h' : p + n' = q') :
    δ n n' (fromSingleMk f h) = fromSingleMk (f ≫ K.d q q') h' := by
  by_cases hq : q + 1 = q'
  · dsimp only [fromSingleMk]
    rw [δ_single _ n n' (by lia) (p - 1) q' (by lia) hq]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K q q' (by simp; lia),
      fromSingleMk]

set_option backward.isDefEq.respectTransparency false in
/-- Cochains of degree `n` from `(singleFunctor C p).obj X` to `K` identify
to `X ⟶ K.X q` when `p + n = q`. -/
noncomputable def fromSingleEquiv {p q n : ℤ} (h : p + n = q) :
    Cochain ((singleFunctor C p).obj X) K n ≃+ (X ⟶ K.X q) where
  toFun α := (HomologicalComplex.singleObjXSelf (.up ℤ) p X).inv ≫ α.v p q h
  invFun f := fromSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hp : p' = p
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hp).eq_of_src _ _
  right_inv f := by simp
  map_add' := by simp

/--
@isnad1 id=eq.1h7v.s11.c83bd9c86a3a from=seed src=0 shape=de0919c7 vocab=896cf5e3
-/
@[simp]
lemma fromSingleEquiv_fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleEquiv h (fromSingleMk f h) = f := by
  simp [fromSingleEquiv]

/--
@isnad1 id=eq.1h8v.s10.6dfdd1d7ca01 from=seed src=0 shape=29c99e03 vocab=d8d9abef
-/
@[simp]
lemma fromSingleMk_add {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (f + g) h = fromSingleMk f h + fromSingleMk g h :=
  (fromSingleEquiv h).symm.map_add _ _

/--
@isnad1 id=eq.1h8v.s10.42338f317980 from=seed src=0 shape=61b71f75 vocab=817710a3
-/
@[simp]
lemma fromSingleMk_sub {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (f - g) h = fromSingleMk f h - fromSingleMk g h :=
  (fromSingleEquiv h).symm.map_sub _ _

/--
@isnad1 id=eq.1h7v.s9.7374295bce1b from=seed src=0 shape=275efdca vocab=c8ff07b4
-/
@[simp]
lemma fromSingleMk_neg {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (-f) h = -fromSingleMk f h :=
  (fromSingleEquiv h).symm.map_neg _

/--
@isnad1 id=ex.1h7v.s8.25445c84eef4 from=seed src=0 shape=979c2eda vocab=d8d9abef
-/
lemma fromSingleMk_surjective {p n : ℤ} (α : Cochain ((singleFunctor C p).obj X) K n)
    (q : ℤ) (h : p + n = q) :
    ∃ (f : X ⟶ K.X q), fromSingleMk f h = α :=
  (fromSingleEquiv h).symm.surjective α

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h9v.s9.ab7277ae84a9 from=seed src=0 shape=67c6e1ce vocab=f2f955b2
-/
lemma fromSingleMk_precomp
    {X' : C} (g : X' ⟶ X) {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q) :
    fromSingleMk (g ≫ f) h =
      (Cochain.ofHom ((singleFunctor C p).map g)).comp (fromSingleMk f h) (zero_add n) := by
  apply (fromSingleEquiv h).injective
  simp [fromSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h9v.s8.8d95228e2071 from=seed src=0 shape=47c82daf vocab=b9883f7e
-/
lemma fromSingleMk_postcomp {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    {L : CochainComplex C ℤ} (g : K ⟶ L) :
    fromSingleMk (f ≫ g.f q) h =
      (fromSingleMk f h).comp (.ofHom g) (add_zero n) :=
  (fromSingleEquiv h).injective (by simp [fromSingleEquiv, singleFunctor, singleFunctors])

/-- Constructor for cochains to a single complex. -/
@[nolint unusedArguments]
noncomputable def toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (_ : p + n = q) :
    Cochain K ((singleFunctor C q).obj X) n :=
  Cochain.single (f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv) n

set_option backward.isDefEq.respectTransparency false in
variable (X K) in
/--
@isnad1 id=eq.1h6v.s9.7b4e9c0f60c3 from=seed src=0 shape=b16f35cf vocab=c2008aeb
-/
@[simp]
lemma toSingleMk_zero (p q n : ℤ) (h : p + n = q) :
    toSingleMk (X := X) (K := K) 0 h = 0 := by
  simp [toSingleMk]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h7v.s9.82bae12ce461 from=seed src=0 shape=9cb1eb9a vocab=52a0076a
-/
@[simp]
lemma toSingleMk_v {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    (toSingleMk f h).v p q h =
      f ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv := by
  simp [toSingleMk]

/--
@isnad1 id=eq.3h9v.s9.3eb679d44a30 from=seed src=0 shape=9b09c7bd vocab=8ff59461
-/
lemma toSingleMk_v_eq_zero {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' q' : ℤ) (hpq' : p' + n = q') (hp' : p' ≠ p) :
    (toSingleMk f h).v p' q' hpq' = 0 :=
  single_v_eq_zero _ _ _ _ _ hp'

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.2h9v.s9.9dd3edf2a248 from=seed src=0 shape=d4c65c1f vocab=384c720d
-/
lemma δ_toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (n' p' : ℤ) (h' : p' + n' = q) :
    δ n n' (toSingleMk f h) = n'.negOnePow • toSingleMk (K.d p' p ≫ f) h' := by
  by_cases hp : p' + 1 = p
  · dsimp only [toSingleMk]
    rw [δ_single _ n n' (by lia) p' (q + 1) (by lia) rfl]
    simp
  · simp [δ_shape n n' (by lia), HomologicalComplex.shape K p' p (by simp; lia)]

set_option backward.isDefEq.respectTransparency false in
/-- Cochains of degree `n` from `(singleFunctor C q).obj X` to `K` identify
to `K.X p ⟶ X` when `p + n = q`. -/
noncomputable def toSingleEquiv {p q n : ℤ} (h : p + n = q) :
    Cochain K ((singleFunctor C q).obj X) n ≃+ (K.X p ⟶ X) where
  toFun α := α.v p q h ≫ (HomologicalComplex.singleObjXSelf (.up ℤ) q X).hom
  invFun f := toSingleMk f h
  left_inv α := by
    ext p' q' hpq'
    by_cases hq : q' = q
    · aesop
    · exact (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq).eq_of_tgt _ _
  right_inv f := by simp
  map_add' := by simp

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h7v.s11.38e80bec1f4c from=seed src=0 shape=d7d4788f vocab=bd268703
-/
@[simp]
lemma toSingleEquiv_toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleEquiv h (toSingleMk f h) = f := by
  simp [toSingleEquiv]

/--
@isnad1 id=eq.1h8v.s10.058e7caac878 from=seed src=0 shape=2ff11257 vocab=c2008aeb
-/
@[simp]
lemma toSingleMk_add {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleMk (f + g) h = toSingleMk f h + toSingleMk g h :=
  (toSingleEquiv h).symm.map_add _ _

/--
@isnad1 id=eq.1h8v.s10.f76cd2a8e709 from=seed src=0 shape=6dce7226 vocab=4f713836
-/
@[simp]
lemma toSingleMk_sub {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleMk (f - g) h = toSingleMk f h - toSingleMk g h :=
  (toSingleEquiv h).symm.map_sub _ _

/--
@isnad1 id=eq.1h7v.s9.93e65e9604d1 from=seed src=0 shape=852cce52 vocab=aa8e6f80
-/
@[simp]
lemma toSingleMk_neg {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) :
    toSingleMk (-f) h = -toSingleMk f h :=
  (toSingleEquiv h).symm.map_neg _

/--
@isnad1 id=ex.1h7v.s8.6bdde4b3f834 from=seed src=0 shape=812a9376 vocab=c2008aeb
-/
lemma toSingleMk_surjective {q n : ℤ} (α : Cochain K ((singleFunctor C q).obj X) n)
    (p : ℤ) (h : p + n = q) :
    ∃ (f : K.X p ⟶ X), toSingleMk f h = α :=
  (toSingleEquiv h).symm.surjective α

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h9v.s9.278f8e822b5d from=seed src=0 shape=6b5929b0 vocab=a105067e
-/
lemma toSingleMk_postcomp
    {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q) {X' : C} (g : X ⟶ X') :
    toSingleMk (f ≫ g) h =
      (toSingleMk f h).comp (.ofHom ((singleFunctor C q).map g)) (add_zero n) := by
  apply (toSingleEquiv h).injective
  simp [toSingleEquiv, singleFunctor, singleFunctors, HomologicalComplex.single_map_f_self]

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.1h9v.s8.6f4bd827e20c from=seed src=0 shape=e3bb1bdc vocab=12d643cd
-/
lemma toSingleMk_precomp
    {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    {L : CochainComplex C ℤ} (g : L ⟶ K) :
    toSingleMk (g.f p ≫ f) h =
      (Cochain.ofHom g).comp (toSingleMk f h) (zero_add n) :=
  (toSingleEquiv h).injective (by simp [toSingleEquiv, singleFunctor, singleFunctors])

end Cochain

namespace Cocycle

/-- Constructor for cocycles from a single complex. -/
@[simps!]
noncomputable def fromSingleMk {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    Cocycle ((singleFunctor C p).obj X) K n :=
  Cocycle.mk (Cochain.fromSingleMk f h) _ rfl (by
    rw [Cochain.δ_fromSingleMk _ _ _ q' (by lia), hf]
    simp)

/--
@isnad1 id=eq.3h10v.s9.044826affeb8 from=seed src=0 shape=1d5b7d20 vocab=bf684437
-/
lemma fromSingleMk_precomp {X' : C} (g : X' ⟶ X) {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (g ≫ f) h q' hq' (by simp [hf]) =
      (fromSingleMk f h q' hq' hf).precomp ((singleFunctor C p).map g) := by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_precomp])

/--
@isnad1 id=eq.3h10v.s9.b103dc1955c4 from=seed src=0 shape=6a47abe3 vocab=dfd6f62d
-/
lemma fromSingleMk_postcomp {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) {L : CochainComplex C ℤ}
    (g : K ⟶ L) :
    fromSingleMk (f ≫ g.f q) h q' hq' (by simp [reassoc_of% hf]) =
      (fromSingleMk f h q' hq' hf).postcomp g := by
  ext : 1
  exact (Cochain.fromSingleEquiv h).injective (by simp [Cochain.fromSingleMk_postcomp])

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=ex.2h8v.s9.0dc411c229d9 from=seed src=0 shape=263233ac vocab=4758d508
-/
lemma fromSingleMk_surjective {p n : ℤ} (α : Cocycle ((singleFunctor C p).obj X) K n)
    (q : ℤ) (h : p + n = q) (q' : ℤ) (hq' : q + 1 = q') :
    ∃ (f : X ⟶ K.X q) (hf : f ≫ K.d q q' = 0), fromSingleMk f h q' hq' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.fromSingleMk_surjective α.1 q h
  have hα := α.δ_eq_zero (n + 1)
  rw [← hf, Cochain.δ_fromSingleMk _ _ _ q' (by lia)] at hα
  replace hα := Cochain.congr_v hα p q' (by lia)
  exact ⟨f, by simpa using hα, by ext : 1; assumption⟩

/--
@isnad1 id=eq.4h9v.s10.47ac3467fe25 from=seed src=0 shape=36fca3fc vocab=a752e277
-/
lemma fromSingleMk_add {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    fromSingleMk (f + g) h q' hq' (by simp [hf, hg]) =
      fromSingleMk f h q' hq' hf + fromSingleMk g h q' hq' hg := by
  cat_disch

/--
@isnad1 id=eq.4h9v.s10.0b2cfa79263b from=seed src=0 shape=ee716998 vocab=788348d2
-/
lemma fromSingleMk_sub {p q : ℤ} (f g : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) (hg : g ≫ K.d q q' = 0) :
    fromSingleMk (f - g) h q' hq' (by simp [hf, hg]) =
      fromSingleMk f h q' hq' hf - fromSingleMk g h q' hq' hg := by
  cat_disch

/--
@isnad1 id=eq.3h8v.s10.3e3966e09396 from=seed src=0 shape=e93e83ff vocab=1453123d
-/
lemma fromSingleMk_neg {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0) :
    fromSingleMk (-f) h q' hq' (by simp [hf]) = - fromSingleMk f h q' hq' hf := by
  cat_disch

variable (X K) in
/--
@isnad1 id=eq.2h7v.s9.5f147b011baa from=seed src=0 shape=84f95591 vocab=8691a924
-/
@[simp]
lemma fromSingleMk_zero {p q : ℤ} {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') :
    fromSingleMk (0 : X ⟶ K.X q) h q' hq' (by simp) = 0 := by
  cat_disch

/--
@isnad1 id=iff.4h9v.s10.ef7f8d1b4803 from=seed src=0 shape=d9773f62 vocab=f5b15e0a
-/
lemma fromSingleMk_mem_coboundaries_iff {p q : ℤ} (f : X ⟶ K.X q) {n : ℤ} (h : p + n = q)
    (q' : ℤ) (hq' : q + 1 = q') (hf : f ≫ K.d q q' = 0)
    (q'' : ℤ) (hq'' : q'' + 1 = q) :
    fromSingleMk f h q' hq' hf ∈ coboundaries _ _ _ ↔
      ∃ (g : X ⟶ K.X q''), g ≫ K.d q'' q = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.fromSingleMk_surjective α q'' (by lia)
    refine ⟨g, ?_⟩
    rw [← hg, fromSingleMk_coe, Cochain.δ_fromSingleMk _ _ _ _ h] at hα
    exact (Cochain.fromSingleEquiv h).symm.injective hα
  · rintro ⟨g, rfl⟩
    exact ⟨Cochain.fromSingleMk g (by lia), Cochain.δ_fromSingleMk _ _ _ _ h⟩

/-- Constructor for cocycles to a single complex. -/
@[simps!]
noncomputable def toSingleMk {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    Cocycle K ((singleFunctor C q).obj X) n :=
  Cocycle.mk (Cochain.toSingleMk f h) _ rfl (by
    rw [Cochain.δ_toSingleMk _ _ _ p' (by lia), hf]
    simp)

/--
@isnad1 id=eq.3h10v.s9.4d37d3bfc7f9 from=seed src=0 shape=0e080c89 vocab=8f08b4db
-/
lemma toSingleMk_postcomp {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) {X' : C} (g : X ⟶ X') :
    toSingleMk (f ≫ g) h p' hp' (by simp [reassoc_of% hf]) =
      (toSingleMk f h p' hp' hf).postcomp ((singleFunctor C q).map g) := by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_postcomp])

/--
@isnad1 id=eq.3h10v.s9.78f39465dbe1 from=seed src=0 shape=abaf2fca vocab=53388a9e
-/
lemma toSingleMk_precomp
    {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    {L : CochainComplex C ℤ} (g : L ⟶ K) :
    toSingleMk (g.f p ≫ f) h p' hp' (by simp [← g.comm_assoc, hf]) =
      (toSingleMk f h p' hp' hf).precomp g := by
  ext : 1
  exact (Cochain.toSingleEquiv h).injective (by simp [Cochain.toSingleMk_precomp])

/--
@isnad1 id=ex.2h8v.s9.2f4df046162f from=seed src=0 shape=16545569 vocab=76b858c4
-/
lemma toSingleMk_surjective {q n : ℤ} (α : Cocycle K ((singleFunctor C q).obj X) n)
    (p : ℤ) (h : p + n = q) (p' : ℤ) (hp' : p' + 1 = p) :
    ∃ (f : K.X p ⟶ X) (hf : K.d p' p ≫ f = 0), toSingleMk f h p' hp' hf = α := by
  obtain ⟨f, hf⟩ := Cochain.toSingleMk_surjective α.1 p h
  have hα := ((n + 1).negOnePow • α).δ_eq_zero (n + 1)
  rw [coe_units_smul, δ_units_smul, ← hf, Cochain.δ_toSingleMk _ _ _ p' (by lia),
    smul_smul, Int.units_mul_self, one_smul] at hα
  refine ⟨f, ?_, ?_⟩
  · simpa [← cancel_mono (HomologicalComplex.singleObjXSelf (.up ℤ) q X).inv] using!
    Cochain.congr_v hα p' q (by lia)
  · ext : 1; assumption

/--
@isnad1 id=eq.4h9v.s10.0e29c7a3a9f9 from=seed src=0 shape=2b90dfc2 vocab=f29ca03b
-/
lemma toSingleMk_add {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) :
    toSingleMk (f + g) h p' hp' (by simp [hf, hg]) =
      toSingleMk f h p' hp' hf + toSingleMk g h p' hp' hg := by
  cat_disch

/--
@isnad1 id=eq.4h9v.s10.d55a8a8cd56f from=seed src=0 shape=17073623 vocab=c81b4fab
-/
lemma toSingleMk_sub {p q : ℤ} (f g : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) (hg : K.d p' p ≫ g = 0) :
    toSingleMk (f - g) h p' hp' (by simp [hf, hg]) =
      toSingleMk f h p' hp' hf - toSingleMk g h p' hp' hg := by
  cat_disch

/--
@isnad1 id=eq.3h8v.s10.0a38a8600dbe from=seed src=0 shape=2087b76a vocab=1afbdb84
-/
lemma toSingleMk_neg {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0) :
    toSingleMk (-f) h p' hp' (by simp [hf]) =
      - toSingleMk f h p' hp' hf := by
  cat_disch

variable (X K) in
/--
@isnad1 id=eq.2h7v.s9.7da643445f65 from=seed src=0 shape=a1cbb5dd vocab=bb59bb3a
-/
@[simp]
lemma toSingleMk_zero {p q : ℤ} {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) :
    toSingleMk (0 : K.X p ⟶ X) h p' hp' (by simp) = 0 := by
  cat_disch

/--
@isnad1 id=iff.4h9v.s10.bc0cb51fc65c from=seed src=0 shape=5914f666 vocab=2efea3a4
-/
lemma toSingleMk_mem_coboundaries_iff {p q : ℤ} (f : K.X p ⟶ X) {n : ℤ} (h : p + n = q)
    (p' : ℤ) (hp' : p' + 1 = p) (hf : K.d p' p ≫ f = 0)
    (p'' : ℤ) (hp'' : p + 1 = p'') :
    toSingleMk f h p' hp' hf ∈ coboundaries _ _ _ ↔
      ∃ (g : K.X p'' ⟶ X), K.d p p'' ≫ g = f := by
  rw [mem_coboundaries_iff _ (n - 1) (by simp)]
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨g, hg⟩ := Cochain.toSingleMk_surjective α p'' (by lia)
    refine ⟨n.negOnePow • g, ?_⟩
    rw [← hg, toSingleMk_coe, Cochain.δ_toSingleMk _ _ _ _ h] at hα
    exact (Cochain.toSingleEquiv h).symm.injective (by simpa)
  · rintro ⟨g, rfl⟩
    exact ⟨n.negOnePow • Cochain.toSingleMk g (by lia),
      by simp [Cochain.δ_toSingleMk _ _ _ _ h, smul_smul]⟩

end Cocycle

end HomComplex

end CochainComplex
