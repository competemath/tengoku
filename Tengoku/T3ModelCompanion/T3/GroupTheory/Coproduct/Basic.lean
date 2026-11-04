/-
Copyright (c) 2026 Yawara Ishida. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yawara Ishida
-/
module

public import Tengoku.T3ModelCompanion.T3.GroupTheory.Free.Basic
public import Tengoku.Seed.GroupTheory.Coprod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coproducts of exponent-three groups

The coproduct is the ordinary free product modulo cubes, exactly as in the paper.
The construction allows arbitrary factors; the retraction to a factor assumes its exponent
divides three.
No finite presentation is chosen.

Paper-ID: preliminaries.notation, preliminaries.free_coproduct,
preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.1(8), Fact 2.16, and Lemma 2.17.
-/

@[expose] public section

namespace T3

/-- The ordinary free product modulo the normal closure of cubes.

Paper-ID: preliminaries.notation
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.1, item 8.-/
abbrev Coproduct (G H : Type*) [Group G] [Group H] :=
  PowerQuotient (Monoid.Coprod G H) 3

namespace Coproduct

variable {G H K : Type*} [Group G] [Group H] [Group K]

/-- The left factor map into the coproduct.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.17.-/
def inl : G →* Coproduct G H := powerQuotientMk.comp Monoid.Coprod.inl

/-- The right factor map into the coproduct.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.17.-/
def inr : H →* Coproduct G H := powerQuotientMk.comp Monoid.Coprod.inr

/-- The coproduct satisfies the exponent-three law.

Paper-ID: preliminaries.notation
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.1, item 8.
@isnad1 id=eq.0h3v.s7.a20bc2dcca8e from=translated src=- shape=a30a1938 vocab=ffdb0961
-/
theorem pow_three (g : Coproduct G H) : g ^ 3 = 1 := powerQuotient_hasExponent g

/-- Every coproduct in the exponent-three variety satisfies the defining law.
@isnad1 id=fact.0h2v.s6.e9a127da0367 from=translated src=- shape=8b7eecf4 vocab=4360f40c
-/
instance hasExponentThree : Fact (HasExponentThree (Coproduct G H)) := ⟨pow_three⟩

/-- A pair of homomorphisms to an exponent-three group descends from the free product.

Paper-ID: preliminaries.notation
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.1, item 8.-/
def lift (hK : HasExponentThree K) (f : G →* K) (g : H →* K) :
    Coproduct G H →* K :=
  powerQuotientLift (Monoid.Coprod.lift f g) fun _ => hK _

/--
@isnad1 id=eq.1h6v.s9.a53b323933b8 from=translated src=- shape=b40221c2 vocab=6704008c
-/
@[simp]
theorem lift_inl (hK : HasExponentThree K) (f : G →* K) (g : H →* K) (x : G) :
    lift hK f g (inl x) = f x := rfl

/--
@isnad1 id=eq.1h6v.s9.332f676cd400 from=translated src=- shape=0a3239d5 vocab=d55de6f6
-/
@[simp]
theorem lift_inr (hK : HasExponentThree K) (f : G →* K) (g : H →* K) (x : H) :
    lift hK f g (inr x) = g x := rfl

/-- Homomorphisms out of the coproduct are determined by their restrictions to both factors.

Paper-ID: preliminaries.notation
TeX: T3_modelcompanion_v9.tex, v9 Notation 2.1, item 8.
@isnad1 id=eq.2h5v.s10.51f32ca5a2c1 from=translated src=- shape=28c22bb8 vocab=b6c53736
-/
theorem hom_ext {f g : Coproduct G H →* K}
    (hl : ∀ x, f (inl x) = g (inl x)) (hr : ∀ x, f (inr x) = g (inr x)) : f = g := by
  have heq : f.comp powerQuotientMk = g.comp powerQuotientMk :=
    Monoid.Coprod.hom_ext (MonoidHom.ext hl) (MonoidHom.ext hr)
  refine MonoidHom.ext fun x => ?_
  obtain ⟨x, rfl⟩ := powerQuotientMk_surjective x
  exact DFunLike.congr_fun heq x

/-- The retraction to the left factor used in the paper's injectivity proof.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.17 and its proof.-/
def fst (hG : HasExponentThree G) : Coproduct G H →* G := lift hG (.id G) 1

/-- The retraction to the right factor.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.17 and its proof.-/
def snd (hH : HasExponentThree H) : Coproduct G H →* H := lift hH 1 (.id H)

/--
@isnad1 id=eq.1h3v.s8.e4015ce9ff8b from=translated src=- shape=94a5cc4a vocab=1f261dd0
-/
@[simp]
theorem fst_inl (hG : HasExponentThree G) (x : G) : fst hG (inl (H := H) x) = x := rfl

/--
@isnad1 id=eq.1h3v.s8.c48cdf634086 from=translated src=- shape=5270935b vocab=3cb2d55b
-/
@[simp]
theorem snd_inr (hH : HasExponentThree H) (x : H) : snd hH (inr (G := G) x) = x := rfl

/--
@isnad1 id=eq.1h3v.s8.08e62bfc1951 from=translated src=- shape=e492db0f vocab=58dace0c
-/
@[simp]
theorem fst_inr (hG : HasExponentThree G) (x : H) : fst hG (inr x) = 1 := rfl

/--
@isnad1 id=eq.1h3v.s8.b12b715e995a from=translated src=- shape=2b1e47d2 vocab=50dd3ddd
-/
@[simp]
theorem snd_inl (hH : HasExponentThree H) (x : G) : snd hH (inl x) = 1 := rfl

/--
@isnad1 id=eq.1h2v.s7.6a8bd06ad285 from=translated src=- shape=84290239 vocab=7630b298
-/
@[simp]
theorem fst_comp_inl (hG : HasExponentThree G) :
    (fst (H := H) hG).comp inl = MonoidHom.id G := rfl

/--
@isnad1 id=eq.1h2v.s7.cf27bf67ee31 from=translated src=- shape=c2f289f4 vocab=b658020d
-/
@[simp]
theorem fst_comp_inr (hG : HasExponentThree G) : (fst hG).comp (inr (H := H)) = 1 := rfl

/--
@isnad1 id=eq.1h2v.s7.dc3abebab945 from=translated src=- shape=88a8d928 vocab=730adc6d
-/
@[simp]
theorem snd_comp_inl (hH : HasExponentThree H) : (snd hH).comp (inl (G := G)) = 1 := rfl

/--
@isnad1 id=eq.1h2v.s7.40e46364e3b2 from=translated src=- shape=6dd1274c vocab=ba460861
-/
@[simp]
theorem snd_comp_inr (hH : HasExponentThree H) :
    (snd (G := G) hH).comp inr = MonoidHom.id H := rfl

variable {G' H' G'' H'' : Type*} [Group G'] [Group H'] [Group G''] [Group H'']

/-- The homomorphism of coproducts induced by homomorphisms of both factors.

Paper-ID: structure.graded_coproduct
TeX: T3_modelcompanion_v9.tex, `proposition:gr of free product`, naturality of the factor maps.-/
def map (f : G →* G') (g : H →* H') : Coproduct G H →* Coproduct G' H' :=
  lift pow_three (inl.comp f) (inr.comp g)

/--
@isnad1 id=eq.0h7v.s9.d0e5c121c8d3 from=translated src=- shape=f8f4ba04 vocab=64808b94
-/
@[simp]
theorem map_inl (f : G →* G') (g : H →* H') (x : G) : map f g (inl x) = inl (f x) := rfl

/--
@isnad1 id=eq.0h7v.s9.ec4e444c20e2 from=translated src=- shape=3367a8b3 vocab=9debf645
-/
@[simp]
theorem map_inr (f : G →* G') (g : H →* H') (x : H) : map f g (inr x) = inr (g x) := rfl

/--
@isnad1 id=eq.0h6v.s8.3a41434e9128 from=translated src=- shape=7e82a23d vocab=d332c3f6
-/
@[simp]
theorem map_comp_inl (f : G →* G') (g : H →* H') :
    (map f g).comp inl = inl.comp f := rfl

/--
@isnad1 id=eq.0h6v.s8.c7ecc5893964 from=translated src=- shape=482d2286 vocab=b3c3f711
-/
@[simp]
theorem map_comp_inr (f : G →* G') (g : H →* H') :
    (map f g).comp inr = inr.comp g := rfl

/--
@isnad1 id=eq.0h2v.s8.e2cafbc7f3ac from=translated src=- shape=e11be116 vocab=58e71b5c
-/
@[simp]
theorem map_id : map (MonoidHom.id G) (MonoidHom.id H) = MonoidHom.id (Coproduct G H) :=
  hom_ext (fun _ => rfl) (fun _ => rfl)

/--
@isnad1 id=eq.0h10v.s9.91a51bb44191 from=translated src=- shape=e0161abe vocab=0d90897f
-/
@[simp]
theorem map_comp (f : G →* G') (g : H →* H') (f' : G' →* G'') (g' : H' →* H'') :
    map (f'.comp f) (g'.comp g) = (map f' g').comp (map f g) :=
  hom_ext (fun _ => rfl) (fun _ => rfl)

/-- The left factor of exponent three embeds in the coproduct.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.17.
@isnad1 id=injectiv.1h2v.s7.f5d72718bb04 from=translated src=- shape=46f874a8 vocab=757d204f
-/
theorem inl_injective (hG : HasExponentThree G) :
    Function.Injective (inl : G → Coproduct G H) :=
  (show Function.LeftInverse (fst hG) inl from fst_inl hG).injective

/-- The right factor of exponent three embeds in the coproduct.

Paper-ID: preliminaries.coproduct_factor_injective
TeX: T3_modelcompanion_v9.tex, v9 Lemma 2.17.
@isnad1 id=injectiv.1h2v.s7.e1723fb0191d from=translated src=- shape=ef4ccd78 vocab=ff4b300b
-/
theorem inr_injective (hH : HasExponentThree H) :
    Function.Injective (inr : H → Coproduct G H) :=
  (show Function.LeftInverse (snd hH) inr from snd_inr hH).injective

end Coproduct

namespace Free

variable {X Y : Type*}

/-- The map from the free group on a disjoint union to the coproduct of its free factors.

Paper-ID: preliminaries.free_coproduct
TeX: T3_modelcompanion_v9.tex, v9 Fact 2.16.-/
def sumToCoproduct : Free (X ⊕ Y) →* Coproduct (Free X) (Free Y) :=
  lift Coproduct.pow_three (Sum.elim (fun x => Coproduct.inl (of x))
    (fun y => Coproduct.inr (of y)))

/--
@isnad1 id=eq.0h3v.s10.6562d9607e77 from=translated src=- shape=82fce6cd vocab=903d3140
-/
@[simp]
theorem sumToCoproduct_of_inl (x : X) :
    sumToCoproduct (of (Sum.inl x : X ⊕ Y)) = Coproduct.inl (of x) := lift_of _ _ _

/--
@isnad1 id=eq.0h3v.s10.801b280e9caf from=translated src=- shape=fa138031 vocab=5b3c9855
-/
@[simp]
theorem sumToCoproduct_of_inr (y : Y) :
    sumToCoproduct (of (Sum.inr y : X ⊕ Y)) = Coproduct.inr (of y) := lift_of _ _ _

/-- The inverse map induced by the two inclusions of generating sets.

Paper-ID: preliminaries.free_coproduct
TeX: T3_modelcompanion_v9.tex, v9 Fact 2.16.-/
def coproductToSum : Coproduct (Free X) (Free Y) →* Free (X ⊕ Y) :=
  Coproduct.lift pow_three (map Sum.inl) (map Sum.inr)

/-- The free exponent-three group on a disjoint union is the coproduct of the free factors.

Paper-ID: preliminaries.free_coproduct
TeX: T3_modelcompanion_v9.tex, v9 Fact 2.16.-/
def sumEquivCoproduct : Free (X ⊕ Y) ≃* Coproduct (Free X) (Free Y) :=
  MonoidHom.toMulEquiv sumToCoproduct coproductToSum
    (hom_ext fun x => by cases x <;> rfl)
    (Coproduct.hom_ext
      (fun x => DFunLike.congr_fun
        (show sumToCoproduct.comp (map Sum.inl) = Coproduct.inl from
          hom_ext fun x => by simp) x)
      (fun y => DFunLike.congr_fun
        (show sumToCoproduct.comp (map Sum.inr) = Coproduct.inr from
          hom_ext fun y => by simp) y))

end Free

end T3
