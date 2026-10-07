/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Homology.ExactSequence
public import Tengoku.Seed.CategoryTheory.ComposableArrows.One
public import Tengoku.Seed.CategoryTheory.ComposableArrows.Two

/-!
# Spectral objects in abelian categories

In this file, we introduce the category `SpectralObject C ι` of spectral
objects in an abelian category `C` indexed by the category `ι`.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits

namespace Abelian

variable (C ι : Type*) [Category C] [Category ι] [Abelian C]

open ComposableArrows

/-- A spectral object in an abelian category category `C` indexed by a category `ι`
consists of a family of functors `H n : ComposableArrows ι 1 ⥤ C` for all `n : ℤ`, and a
functorial long exact sequence
`⋯ ⟶ (H n₀).obj (mk₁ f) ⟶ (H n₀).obj (mk₁ (f ≫ g)) ⟶ (H n₀).obj (mk₁ g) ⟶ (H n₁).obj (mk₁ f) ⟶ ⋯`
when `n₀ + 1 = n₁` and `f` and `g` are composable morphisms in `ι`. (This will be
shortened as `H^n₀(f) ⟶ H^n₀(f ≫ g) ⟶ H^n₀(g) ⟶ H^n₁(f)` in the documentation.) -/
structure SpectralObject where
  /-- A sequence of functors from `ComposableArrows ι 1` to the abelian category.
  The image of `mk₁ f` will be referred to as `H^n(f)` in the documentation. -/
  H (n : ℤ) : ComposableArrows ι 1 ⥤ C
  /-- The connecting homomorphism of the spectral object. (Use `δ` instead.) -/
  δ' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) :
    functorArrows ι 1 2 2 ⋙ H n₀ ⟶ functorArrows ι 0 1 2 ⋙ H n₁
  exact₁' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((δ' n₀ n₁ h).app D) ((H n₁).map ((mapFunctorArrows ι 0 1 0 2 2).app D))).Exact
  exact₂' (n : ℤ) (D : ComposableArrows ι 2) :
    (mk₂ ((H n).map ((mapFunctorArrows ι 0 1 0 2 2).app D))
      ((H n).map ((mapFunctorArrows ι 0 2 1 2 2).app D))).Exact
  exact₃' (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁) (D : ComposableArrows ι 2) :
    (mk₂ ((H n₀).map ((mapFunctorArrows ι 0 2 1 2 2).app D)) ((δ' n₀ n₁ h).app D)).Exact

namespace SpectralObject

variable {C ι} (X : SpectralObject C ι)

section

/-- The connecting homomorphism of the spectral object. -/
def δ {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).obj (mk₁ g) ⟶ (X.H n₁).obj (mk₁ f) :=
  (X.δ' n₀ n₁ hn₁).app (mk₂ f g)

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=eq.0h19v.s10.bd5d0d5d3285 from=seed src=0 shape=992a3985 vocab=fb9afe8f
-/
@[reassoc]
lemma δ_naturality {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
    {i' j' k' : ι} (f' : i' ⟶ j') (g' : j' ⟶ k')
    (α : mk₁ f ⟶ mk₁ f') (β : mk₁ g ⟶ mk₁ g')
    (n₀ n₁ : ℤ) (hαβ : α.app 1 = β.app 0 := by cat_disch) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).map β ≫ X.δ f' g' n₀ n₁ hn₁ = X.δ f g n₀ n₁ hn₁ ≫ (X.H n₁).map α := by
  have h := (X.δ' n₀ n₁ hn₁).naturality
    (homMk₂ (α.app 0) (α.app 1) (β.app 1) (naturality' α 0 1)
      (by simpa only [hαβ] using! naturality' β 0 1) : mk₂ f g ⟶ mk₂ f' g')
  dsimp at h
  convert! h <;> cat_disch

end

section

variable {i j k : ι} (f : i ⟶ j) (g : j ⟶ k)
  (fg : i ⟶ k) (h : f ≫ g = fg)

/--
@isnad1 id=eq.1h12v.s10.88061919f141 from=seed src=0 shape=7640be62 vocab=56db7d84
-/
@[reassoc (attr := simp)]
lemma zero₁ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    X.δ f g n₀ n₁ hn₁ ≫ (X.H n₁).map (twoδ₂Toδ₁ f g fg h) = 0 := by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).zero 0

/--
@isnad1 id=eq.1h10v.s10.7af687da9081 from=seed src=0 shape=da33d439 vocab=d45cc394
-/
@[reassoc (attr := simp)]
lemma zero₂ (fg : i ⟶ k) (h : f ≫ g = fg) (n₀ : ℤ) :
    (X.H n₀).map (twoδ₂Toδ₁ f g fg h) ≫ (X.H n₀).map (twoδ₁Toδ₀ f g fg h) = 0 := by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).zero 0

/--
@isnad1 id=eq.1h12v.s10.4a780c315ff2 from=seed src=0 shape=62c6a83e vocab=c957247e
-/
@[reassoc (attr := simp)]
lemma zero₃ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.H n₀).map (twoδ₁Toδ₀ f g fg h) ≫ X.δ f g n₀ n₁ hn₁ = 0 := by
  subst h
  exact (X.exact₃' n₀ n₁ hn₁ (mk₂ f g)).zero 0

/-- The (exact) short complex `H^n₀(g) ⟶ H^n₁(f) ⟶ H^n₁(fg)` of a
spectral object, when `f ≫ g = fg` and `n₀ + 1 = n₁`. -/
@[simps]
def sc₁ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₁ f g fg h n₀ n₁ hn₁)

/-- The (exact) short complex `H^n₀(f) ⟶ H^n₀(fg) ⟶ H^n₀(g)` of a
spectral object, when `f ≫ g = fg`. -/
@[simps]
def sc₂ (n₀ : ℤ) : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₂ f g fg h n₀)

/-- The (exact) short complex `H^n₀(fg) ⟶ H^n₀(g) ⟶ H^n₁(f)`
of a spectral object, when `f ≫ g = fg` and `n₀ + 1 = n₁`. -/
@[simps]
def sc₃ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) : ShortComplex C :=
  ShortComplex.mk _ _ (X.zero₃ f g fg h n₀ n₁ hn₁)

/--
@isnad1 id=exact.1h12v.s7.9b5476474ae0 from=seed src=0 shape=2f5962a7 vocab=fc156a6b
-/
lemma exact₁ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.sc₁ f g fg h n₀ n₁ hn₁).Exact := by
  subst h
  exact (X.exact₁' n₀ n₁ hn₁ (mk₂ f g)).exact 0

/--
@isnad1 id=exact.1h10v.s6.f997a46b56ed from=seed src=0 shape=622cd143 vocab=7aef15d7
-/
lemma exact₂ (n₀ : ℤ) :
    (X.sc₂ f g fg h n₀).Exact := by
  subst h
  exact (X.exact₂' n₀ (mk₂ f g)).exact 0

/--
@isnad1 id=exact.1h12v.s7.907266a08fb7 from=seed src=0 shape=2f5962a7 vocab=0c3ccc33
-/
lemma exact₃ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.sc₃ f g fg h n₀ n₁ hn₁).Exact := by
  subst h
  exact ((X.exact₃' n₀ n₁ hn₁ (mk₂ f g))).exact 0

/-- The (exact) sequence
`H^n₀(f) ⟶ H^n₀(fg) ⟶ H^n₀(g) ⟶ H^n₁(f) ⟶ H^n₁(fg) ⟶ H^n₁(g)`
of a spectral object, when `f ≫ g = fg` and `n₀ + 1 = n₁`. -/
abbrev composableArrows₅ (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    ComposableArrows C 5 :=
  mk₅ ((X.H n₀).map (twoδ₂Toδ₁ f g fg h)) ((X.H n₀).map (twoδ₁Toδ₀ f g fg h))
    (X.δ f g n₀ n₁ hn₁) ((X.H n₁).map (twoδ₂Toδ₁ f g fg h))
    ((X.H n₁).map (twoδ₁Toδ₀ f g fg h))

/--
@isnad1 id=exact.1h12v.s7.3d3c14a253cf from=seed src=0 shape=6533f273 vocab=f101bdde
-/
lemma composableArrows₅_exact (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) :
    (X.composableArrows₅ f g fg h n₀ n₁ hn₁).Exact :=
  exact_of_δ₀ (X.exact₂ _ _ _ h n₀).exact_toComposableArrows
    (exact_of_δ₀ (X.exact₃ _ _ _ h n₀ n₁ hn₁).exact_toComposableArrows
      (exact_of_δ₀ (X.exact₁ _ _ _ h n₀ n₁ hn₁).exact_toComposableArrows
        ((X.exact₂ _ _ _ h n₁).exact_toComposableArrows)))

end

/--
@isnad1 id=eq.0h15v.s10.5bec7d9f4c4c from=seed src=0 shape=3da6c6b3 vocab=c57d7381
-/
@[reassoc (attr := simp)]
lemma δ_δ {i j k l : ι} (f : i ⟶ j) (g : j ⟶ k) (h : k ⟶ l)
    (n₀ n₁ n₂ : ℤ) (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X.δ g h n₀ n₁ hn₁ ≫ X.δ f g n₁ n₂ hn₂ = 0 := by
  have eq := X.δ_naturality f g f (g ≫ h) (𝟙 _) (twoδ₂Toδ₁ g h _ rfl) n₁ n₂
  rw [Functor.map_id, comp_id] at eq
  rw [← eq, X.zero₁_assoc g h _ rfl n₀ n₁ hn₁, zero_comp]

/-- The type of morphisms between spectral objects in abelian categories. -/
@[ext]
structure Hom (X' : SpectralObject C ι) where
  /-- The natural transformation that is part of a morphism between spectral objects. -/
  hom (n : ℤ) : X.H n ⟶ X'.H n
  comm (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i j k : ι} (f : i ⟶ j) (g : j ⟶ k) :
    X.δ f g n₀ n₁ hn₁ ≫ (hom n₁).app (mk₁ f) =
    (hom n₀).app (mk₁ g) ≫ X'.δ f g n₀ n₁ hn₁ := by cat_disch

attribute [reassoc (attr := simp)] Hom.comm

@[simps]
instance : Category (SpectralObject C ι) where
  Hom := Hom
  id X := { hom _ := 𝟙 _ }
  comp f g := { hom n := f.hom n ≫ g.hom n }

attribute [simp] id_hom
attribute [reassoc, simp] comp_hom

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=iszero.0h7v.s7.96c98d91c267 from=seed src=0 shape=5020b11a vocab=97a381b4
-/
lemma isZero_H_map_mk₁_of_isIso (n : ℤ) {i₀ i₁ : ι} (f : i₀ ⟶ i₁) [IsIso f] :
    IsZero ((X.H n).obj (mk₁ f)) := by
  let φ := twoδ₂Toδ₁ f (inv f) (𝟙 i₀) (by simp) ≫ twoδ₁Toδ₀ f (inv f) (𝟙 i₀)
  have : IsIso φ := by
    rw [isIso_iff₁]
    constructor <;> dsimp [φ] <;> infer_instance
  rw [IsZero.iff_id_eq_zero]
  rw [← cancel_mono ((X.H n).map φ), Category.id_comp, zero_comp,
    ← X.zero₂ f (inv f) (𝟙 _) (by simp), ← Functor.map_comp]

section

variable (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) {i₀ i₁ i₂ : ι}
  (f : i₀ ⟶ i₁) (g : i₁ ⟶ i₂) (fg : i₀ ⟶ i₂) (hfg : f ≫ g = fg)
  (h₁ : IsZero ((X.H n₀).obj (mk₁ f))) (h₂ : IsZero ((X.H n₁).obj (mk₁ f)))

include h₁ in
/--
@isnad1 id=mono.2h10v.s9.5e2360eff126 from=seed src=0 shape=5794bb40 vocab=832fd3d0
-/
lemma mono_H_map_twoδ₁Toδ₀ : Mono ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg)) :=
  (X.exact₂ f g fg hfg n₀).mono_g (h₁.eq_of_src _ _)

include h₂ hn₁ in
/--
@isnad1 id=epi.3h11v.s9.9e7f225709c6 from=seed src=0 shape=298915ff vocab=5794640e
-/
lemma epi_H_map_twoδ₁Toδ₀ : Epi ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg)) :=
  (X.exact₃ f g fg hfg n₀ n₁ hn₁).epi_f (h₂.eq_of_tgt _ _)

include h₁ h₂ hn₁ in
/--
@isnad1 id=isiso.4h11v.s9.3a242e7b59b9 from=seed src=0 shape=1ee012a2 vocab=ada2e274
-/
lemma isIso_H_map_twoδ₁Toδ₀ : IsIso ((X.H n₀).map (twoδ₁Toδ₀ f g fg hfg)) := by
  have := X.mono_H_map_twoδ₁Toδ₀ n₀ f g fg hfg h₁
  have := X.epi_H_map_twoδ₁Toδ₀ n₀ n₁ hn₁ f g fg hfg h₂
  apply isIso_of_mono_of_epi

end

section

variable {ι' : Type*} [Preorder ι'] (X' : SpectralObject C ι')
  (n₀ n₁ : ℤ) (hn₁ : n₀ + 1 = n₁) (i₀ i₁ i₂ : ι') (h₀₁ : i₀ ≤ i₁) (h₁₂ : i₁ ≤ i₂)
  (h₁ : IsZero ((X'.H n₀).obj (mk₁ (homOfLE h₀₁))))
  (h₂ : IsZero ((X'.H n₁).obj (mk₁ (homOfLE h₀₁))))

include h₁ in
/--
@isnad1 id=mono.3h7v.s9.a2a4e7fb0e53 from=seed src=0 shape=bb835207 vocab=b4cc5d3b
-/
lemma mono_H_map_twoδ₁Toδ₀' : Mono ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂)) :=
  X'.mono_H_map_twoδ₁Toδ₀ _ _ _ _ _ h₁

include h₂ hn₁ in
/--
@isnad1 id=epi.4h8v.s9.b8206f42e233 from=seed src=0 shape=df1fadc6 vocab=fa101dc2
-/
lemma epi_H_map_twoδ₁Toδ₀' : Epi ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂)) :=
  X'.epi_H_map_twoδ₁Toδ₀ _ _ hn₁ _ _ _ _ h₂

include h₁ h₂ hn₁ in
/--
@isnad1 id=isiso.5h8v.s9.154e2d9987f1 from=seed src=0 shape=aff020f4 vocab=381175aa
-/
lemma isIso_H_map_twoδ₁Toδ₀' : IsIso ((X'.H n₀).map (twoδ₁Toδ₀' i₀ i₁ i₂ h₀₁ h₁₂)) :=
  X'.isIso_H_map_twoδ₁Toδ₀ _ _ hn₁ _ _ _ _ h₁ h₂

end

end SpectralObject

end Abelian

end CategoryTheory
