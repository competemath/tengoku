/-
Copyright (c) 2026 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Homology.SpectralObject.Differentials
public import Tengoku.Seed.CategoryTheory.ComposableArrows.Four

/-!
# Induced morphisms that are epi or mono

Given a spectral object in an abelian category, we show that certain
morphisms `E^n(f₁, f₂, f₃) ⟶ E^n(f₁', f₂', f₃')` are monomorphisms,
epimorphisms or isomorphisms.

## References
* [Jean-Louis Verdier, *Des catégories dérivées des catégories abéliennes*, II.4][verdier1996]

-/

@[expose] public section

namespace CategoryTheory

open Category Limits ComposableArrows

namespace Abelian

namespace SpectralObject

variable {C ι ι' : Type*} [Category* C] [Abelian C] [Category* ι] [Preorder ι']
  (X : SpectralObject C ι) (X' : SpectralObject C ι')

section

variable
  {i₀' i₀ i₁ i₂ i₃ i₃' : ι} (f₁ : i₀ ⟶ i₁)
  (f₁' : i₀' ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃) (f₃' : i₂ ⟶ i₃')
  (n₀ n₁ n₂ n₃ : ℤ)

/--
@isnad1 id=epi.0h23v.s10.8bda3bb9ed94 from=seed src=0 shape=38b12bfd vocab=3256a1c0
-/
lemma epi_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁ f₂ f₃') (n₀ n₁ n₂ n₃ : ℤ)
    (hα₀ : α.app 0 = 𝟙 _ := by cat_disch) (hα₁ : α.app 1 = 𝟙 _ := by cat_disch)
    (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Epi (X.map f₁ f₂ f₃ f₁ f₂ f₃' α n₀ n₁ n₂ hn₁ hn₂) :=
  have : Epi (X.cyclesMap f₁ f₂ f₁ f₂ (𝟙 (mk₂ f₁ f₂)) n₁) := by rw [X.cyclesMap_id]; infer_instance
  epi_of_epi_fac (X.πE_map _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂ (by cat_disch) _ _)

/--
@isnad1 id=mono.0h23v.s10.f288b6eadc5d from=seed src=0 shape=2b78cc67 vocab=c473ebbc
-/
lemma mono_map (α : mk₃ f₁ f₂ f₃ ⟶ mk₃ f₁' f₂ f₃) (n₀ n₁ n₂ n₃ : ℤ)
    (hα₁ : α.app 1 = 𝟙 _ := by cat_disch) (hα₂ : α.app 2 = 𝟙 _ := by cat_disch)
    (hα₃ : α.app 3 = 𝟙 _ := by cat_disch) (hn₁ : n₀ + 1 = n₁ := by lia)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    Mono (X.map f₁ f₂ f₃ f₁' f₂ f₃ α n₀ n₁ n₂ hn₁ hn₂) := by
  have := X.map_ιE _ _ _ _ _ _ α (𝟙 _) n₀ n₁ n₂
  rw [opcyclesMap_id, comp_id] at this
  exact mono_of_mono_fac this

end

section

variable {i₀ i₁ i₂ i₃ i₄ i₅ : ι} (f₁ : i₀ ⟶ i₁) (f₂ : i₁ ⟶ i₂) (f₃ : i₂ ⟶ i₃)
  (f₄ : i₃ ⟶ i₄) (f₅ : i₄ ⟶ i₅)
  (f₂₃ : i₁ ⟶ i₃) (h₂₃ : f₂ ≫ f₃ = f₂₃)
  (f₃₄ : i₂ ⟶ i₄) (h₃₄ : f₃ ≫ f₄ = f₃₄)
  (n₀ n₁ n₂ n₃ : ℤ)

/--
@isnad1 id=eq.1h22v.s8.a0aef60a3eca from=seed src=0 shape=898a174b vocab=120f6425
-/
@[reassoc (attr := simp)]
lemma d_map_fourδ₄Toδ₃ (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ ≫
      X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃ = 0 := by
  simp [← cancel_epi (X.πE f₃ f₄ f₅ n₀ n₁ n₂), ← cancel_epi (X.toCycles f₃ f₄ f₃₄ h₃₄ n₁),
    X.toCycles_πE_d_assoc f₁ f₂ f₃ f₄ f₅ _ rfl f₃₄ h₃₄ n₀ n₁ n₂ n₃,
    X.πE_map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) (𝟙 _) n₁ n₂ n₃]

instance (hn₂ : n₁ + 1 = n₂) (hn₃ : n₂ + 1 = n₃) :
    Epi (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) :=
  X.epi_map _ _ _ _ _ _ _ _ _ rfl rfl rfl hn₂ hn₃ rfl

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=isiso.1h19v.s10.a02a0f652b77 from=seed src=0 shape=128e7b37 vocab=e827a710
-/
lemma isIso_map_fourδ₄Toδ₃ (h : (X.H n₁).map (twoδ₁Toδ₀ f₃ f₄ f₃₄ h₃₄) = 0 := by cat_disch)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    IsIso (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · exact (X.exact₂ f₃ f₄ f₃₄ h₃₄ _).epi_f h
  · dsimp
    convert! (inferInstance : IsIso ((X.H n₂).map (𝟙 _)))
    cat_disch
  · dsimp
    convert! (inferInstance : Mono ((X.H n₃).map (𝟙 (mk₁ f₁))))
    cat_disch

/--
@isnad1 id=isiso.1h19v.s8.51bf3d44dbe1 from=seed src=0 shape=69cfd547 vocab=2bd44d95
-/
lemma isIso_map_fourδ₄Toδ₃_of_isZero (h : IsZero ((X.H n₁).obj (mk₁ f₄)) := by cat_disch)
    (hn₂ : n₁ + 1 = n₂ := by lia) (hn₃ : n₂ + 1 = n₃ := by lia) :
    IsIso (X.map f₁ f₂ f₃ f₁ f₂ f₃₄ (fourδ₄Toδ₃ f₁ f₂ f₃ f₄ f₃₄ h₃₄) n₁ n₂ n₃ hn₂ hn₃) :=
  X.isIso_map_fourδ₄Toδ₃ _ _ _ _ _ _ _ _ _ (h.eq_of_tgt _ _)

/--
@isnad1 id=eq.1h22v.s8.6e98fe3de8e8 from=seed src=0 shape=9cab54ca vocab=e28bf958
-/
@[reassoc (attr := simp)]
lemma map_fourδ₁Toδ₀_d (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia)
    (hn₃ : n₂ + 1 = n₃ := by lia) :
    X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂ ≫
      X.d f₁ f₂ f₃ f₄ f₅ n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃ = 0 := by
  simp [← cancel_mono (X.ιE f₁ f₂ f₃ n₁ n₂ n₃ hn₂ hn₃),
    ← cancel_mono (X.fromOpcycles f₂ f₃ f₂₃ h₂₃ n₂),
    X.d_ιE_fromOpcycles f₁ f₂ f₃ f₄ f₅ f₂₃ h₂₃ _ rfl _ rfl n₀ n₁ n₂ n₃ hn₁ hn₂ hn₃, X.map_ιE_assoc
    f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) (𝟙 _) n₀ n₁ n₂ (by cat_disch) hn₁ hn₂]

instance (hn₁ : n₀ + 1 = n₁) (hn₂ : n₁ + 1 = n₂) :
    Mono (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) :=
  X.mono_map _ _ _ _ _ _ _ _ _ rfl rfl rfl _ _ rfl

set_option backward.defeqAttrib.useBackward true in
/--
@isnad1 id=isiso.1h19v.s10.1713388d7ceb from=seed src=0 shape=b19e0bf1 vocab=6bc61d8b
-/
lemma isIso_map_fourδ₁Toδ₀ (h : (X.H n₂).map (twoδ₂Toδ₁ f₂ f₃ f₂₃ h₂₃) = 0 := by cat_disch)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) := by
  apply ShortComplex.isIso_homologyMap_of_epi_of_isIso_of_mono'
  · dsimp
    convert! (inferInstance : Epi ((X.H n₀).map (𝟙 _)))
    cat_disch
  · dsimp
    convert! (inferInstance : IsIso ((X.H n₁).map (𝟙 _)))
    cat_disch
  · exact (X.exact₂ f₂ f₃ f₂₃ h₂₃ n₂).mono_g h

/--
@isnad1 id=isiso.2h18v.s8.022b8f4dc5fe from=seed src=0 shape=335b948d vocab=bbd3582d
-/
lemma isIso_map_fourδ₁Toδ₀_of_isZero (h : IsZero ((X.H n₂).obj (mk₁ f₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X.map f₂₃ f₄ f₅ f₃ f₄ f₅ (fourδ₁Toδ₀ f₂ f₃ f₄ f₅ f₂₃ h₂₃) n₀ n₁ n₂ hn₁ hn₂) :=
  X.isIso_map_fourδ₁Toδ₀ _ _ _ _ _ _ _ _ _ (h.eq_of_src _ _)

end

section

variable (i₀ i₁ i₂ i₃ i₄ i₅ : ι') (hi₀₁ : i₀ ≤ i₁)
  (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄) (hi₄₅ : i₄ ≤ i₅)

/-- For a spectral object indexed by a preorder, this is the map
`E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄) ⟶ E^{n₁}(i₁ ≤ i₂ ≤ i₃ ≤ i₄)`. -/
noncomputable abbrev mapFourδ₁Toδ₀' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.map _ _ _ _ _ _ (fourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

/-- For a spectral object indexed by a preorder, this is the map
`E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ⟶ E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₄)`. -/
noncomputable abbrev mapFourδ₄Toδ₃' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.map _ _ _ _ _ _ (fourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

/--
@isnad1 id=eq.5h14v.s8.ccb2463cc795 from=seed src=0 shape=e1f3bbf4 vocab=f6ae93b5
-/
@[reassoc]
lemma mapFourδ₁Toδ₀'_comp (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₃ i₄ i₅ hi₀₁ (hi₁₂.trans hi₂₃) hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₁Toδ₀' i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.mapFourδ₁Toδ₀' i₀ i₂ i₃ i₄ i₅ (hi₀₁.trans hi₁₂) hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ :=
  (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

/--
@isnad1 id=eq.5h14v.s8.3fc59ecd3fe1 from=seed src=0 shape=7697cd83 vocab=b2699646
-/
@[reassoc]
lemma mapFourδ₄Toδ₃'_comp (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₄ i₅ hi₀₁ hi₁₂ (hi₂₃.trans hi₃₄) hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₅ hi₀₁ hi₁₂ hi₂₃ (hi₃₄.trans hi₄₅) n₀ n₁ n₂ hn₁ hn₂ :=
  (X'.map_comp (hn₁ := hn₁) (hn₂ := hn₂) ..).symm

/--
@isnad1 id=eq.5h14v.s8.ceb22b753252 from=seed src=0 shape=8eaa99bb vocab=075ab13d
-/
@[reassoc]
lemma mapFourδ₁Toδ₀'_mapFourδ₃Toδ₃' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₄Toδ₃' i₁ i₂ i₃ i₄ i₅ hi₁₂ hi₂₃ hi₃₄ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ =
    X'.mapFourδ₄Toδ₃' i₀ i₂ i₃ i₄ i₅ _ _ _ hi₄₅ n₀ n₁ n₂ hn₁ hn₂ ≫
      X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₅ hi₀₁ _ _ _ n₀ n₁ n₂ hn₁ hn₂ := by
  rw [← map_comp .., ← map_comp ..]
  rfl

section

variable (n₀ n₁ n₂ : ℤ) (h : IsZero ((X'.H n₂).obj (mk₁ (homOfLE hi₀₁))))

include h in
/--
@isnad1 id=isiso.5h13v.s8.21f894fb23b9 from=seed src=0 shape=150cdc5a vocab=84360838
-/
lemma isIso_mapFourδ₁Toδ₀' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_map_fourδ₁Toδ₀_of_isZero _ _ _ _ _ _ _ _ _ h

/-- For a spectral object indexed by a preorder, this is the isomorphism
`E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄) ≅ E^{n₁}(i₁ ≤ i₂ ≤ i₃ ≤ i₄)`
when `H^{n₁ + 1}(i₀ ≤ i₁)` is a zero object. -/
@[simps! hom]
noncomputable def isoMapFourδ₁Toδ₀' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.E (homOfLE (hi₀₁.trans hi₁₂)) (homOfLE hi₂₃) (homOfLE hi₃₄) n₀ n₁ n₂ hn₁ hn₂ ≅
      X'.E (homOfLE hi₁₂) (homOfLE hi₂₃) (homOfLE hi₃₄) n₀ n₁ n₂ hn₁ hn₂ :=
  have := X'.isIso_mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

/--
@isnad1 id=eq.5h13v.s9.643e8f7336cf from=seed src=0 shape=60c2b476 vocab=fa3b28bc
-/
@[reassoc (attr := simp)]
lemma isoMapFourδ₁Toδ₀'_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv = 𝟙 _ :=
  (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

/--
@isnad1 id=eq.5h13v.s9.26e21e37adfd from=seed src=0 shape=45dcf8d7 vocab=20be3f46
-/
@[reassoc (attr := simp)]
lemma isoMapFourδ₁Toδ₀'_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
      X'.mapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ :=
  (X'.isoMapFourδ₁Toδ₀' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id

end

section

variable (n₀ n₁ n₂ : ℤ) (h : IsZero ((X'.H n₀).obj (mk₁ (homOfLE hi₃₄))))

include h in
/--
@isnad1 id=isiso.5h13v.s8.a3760214a438 from=seed src=0 shape=78cb9dec vocab=744efd59
-/
lemma isIso_mapFourδ₄Toδ₃' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_map_fourδ₄Toδ₃_of_isZero (h := h) ..

/-- For a spectral object indexed by a preorder, this is the isomorphism
`E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₃) ≅ E^{n₁}(i₀ ≤ i₁ ≤ i₂ ≤ i₄)`
when `H^{n₁-1}(i₃ ≤ i₄)` is a zero object. -/
@[simps! hom]
noncomputable def isoMapFourδ₄Toδ₃' (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE hi₂₃) n₀ n₁ n₂ hn₁ hn₂ ≅
      X'.E (homOfLE hi₀₁) (homOfLE hi₁₂) (homOfLE (hi₂₃.trans hi₃₄)) n₀ n₁ n₂ hn₁ hn₂ :=
  have := X'.isIso_mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂
  asIso (X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂)

/--
@isnad1 id=eq.5h13v.s9.30151aafd301 from=seed src=0 shape=d181d96a vocab=42cee80a
-/
@[reassoc (attr := simp)]
lemma isoMapFourδ₄Toδ₄'_hom_inv_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ ≫
      (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv = 𝟙 _ :=
  (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).hom_inv_id

/--
@isnad1 id=eq.5h13v.s9.67c7712d3291 from=seed src=0 shape=b3fa630f vocab=ea2770f0
-/
@[reassoc (attr := simp)]
lemma isoMapFourδ₄Toδ₄'_inv_hom_id (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv ≫
      X'.mapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂ = 𝟙 _ :=
  (X'.isoMapFourδ₄Toδ₃' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ h hn₁ hn₂).inv_hom_id

end

section

variable (i₀ i₁ i₂ i₃ i₄ : ι') (hi₀₁ : i₀ ≤ i₁)
  (hi₁₂ : i₁ ≤ i₂) (hi₂₃ : i₂ ≤ i₃) (hi₃₄ : i₃ ≤ i₄)

/-- For a spectral object indexed by a preorder, this is the map
`E^{n₁}(i₀ ≤ i₁ ≤ i₃ ≤ i₄) ⟶ E^{n₁}(i₀ ≤ i₂ ≤ i₃ ≤ i₄)`. -/
noncomputable abbrev mapFourδ₂Toδ₁' (n₀ n₁ n₂ : ℤ)
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :=
  X'.map _ _ _ _ _ _ (fourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄) n₀ n₁ n₂ hn₁ hn₂

/--
@isnad1 id=isiso.6h13v.s9.5fbda4be1d4f from=seed src=0 shape=3bea8725 vocab=123cb047
-/
lemma isIso_mapFourδ₂Toδ₁' (n₀ n₁ n₂ : ℤ)
    (h₁ : IsIso ((X'.H n₁).map (twoδ₁Toδ₀' i₁ i₂ i₃ hi₁₂ hi₂₃)))
    (h₂ : IsIso ((X'.H n₂).map (twoδ₂Toδ₁' i₀ i₁ i₂ hi₀₁ hi₁₂)))
    (hn₁ : n₀ + 1 = n₁ := by lia) (hn₂ : n₁ + 1 = n₂ := by lia) :
    IsIso (X'.mapFourδ₂Toδ₁' i₀ i₁ i₂ i₃ i₄ hi₀₁ hi₁₂ hi₂₃ hi₃₄ n₀ n₁ n₂ hn₁ hn₂) :=
  X'.isIso_map _ _ _ _ _ _ _ _ _ _
    (by exact (inferInstanceAs (IsIso ((X'.H n₀).map (𝟙 _))))) h₁ h₂

end

end

end SpectralObject

end Abelian

end CategoryTheory
