import Tengoku.Seed.CategoryTheory.Preadditive.Biproducts
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.CategoryTheory.IyamaTauSequence
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.CategoryTheory.NilpotentCategoricalRadical

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite biproducts of Iyama tau-approximation complexes

This file constructs the explicit componentwise finite biproduct of short
complexes.  Weak kernels, weak cokernels, and Iyama's radical approximation
conditions are preserved.  When the categorical radical is represented by a
two-sided additive Hom ideal, minimality is also preserved, so both right and
left tau-sequences are closed under finite biproducts.  The current interface
supplies that ideal through `NilpotentRadicalData`; its nilpotence field is not
used by the results in this file.
-/

open scoped QuotientSubmoduleEquidistribution.CategoricalIdeal.HomIdeal

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace QuotientSubmoduleEquidistribution.Iyama

universe v u w

open CategoricalIdeal CategoricalRadical

variable {C : Type u} [Category.{v} C] [Preadditive C]
  [HasFiniteBiproducts C]

/-- The componentwise finite biproduct of short complexes.-/
def shortComplexBiproduct {J : Type w} [Fintype J]
    (S : J → ShortComplex C) : ShortComplex C :=
  ShortComplex.mk
    (biproduct.map fun j ↦ (S j).f)
    (biproduct.map fun j ↦ (S j).g)
    (by
      ext i j
      by_cases hij : i = j
      · subst j
        simp
      · simp)

/--
@isnad1 id=eq.0h3v.s7.f6c8aaebce20 from=translated src=- shape=9f658f3b vocab=a390204c
-/
@[simp]
theorem shortComplexBiproduct_f {J : Type w} [Fintype J]
    (S : J → ShortComplex C) :
    (shortComplexBiproduct S).f = biproduct.map fun j ↦ (S j).f :=
  rfl

/--
@isnad1 id=eq.0h3v.s7.147d97e7e675 from=translated src=- shape=9f658f3b vocab=2472807a
-/
@[simp]
theorem shortComplexBiproduct_g {J : Type w} [Fintype J]
    (S : J → ShortComplex C) :
    (shortComplexBiproduct S).g = biproduct.map fun j ↦ (S j).g :=
  rfl

/-- Finite componentwise biproducts preserve weak kernels.
@isnad1 id=isweakke.1h3v.s5.e0bf10d779ac from=translated src=- shape=9b4740fc vocab=58da3d23
-/
theorem isWeakKernel_shortComplexBiproduct
    {J : Type w} [Fintype J]
    (S : J → ShortComplex C)
    (hS : ∀ j, ShortComplex.IsWeakKernel (S j)) :
    ShortComplex.IsWeakKernel (shortComplexBiproduct S) := by
  rw [ShortComplex.isWeakKernel_iff]
  intro W k hk
  change W ⟶ (⨁ fun j ↦ (S j).X₂) at k
  change k ≫ (biproduct.map fun j ↦ (S j).g) = 0 at hk
  have hk_component (j : J) :
      (k ≫ biproduct.π (fun j ↦ (S j).X₂) j) ≫ (S j).g = 0 := by
    have h := congrArg
      (fun q ↦ q ≫ biproduct.π (fun j ↦ (S j).X₃) j) hk
    rw [Category.assoc] at h
    rw [biproduct.map_π] at h
    simpa [Category.assoc] using h
  choose l hl using fun j ↦
    (ShortComplex.isWeakKernel_iff (S j)).mp
      (hS j) (k ≫ biproduct.π (fun j ↦ (S j).X₂) j)
        (hk_component j)
  refine ⟨biproduct.lift l, ?_⟩
  change biproduct.lift l ≫
      (biproduct.map fun j ↦ (S j).f) = k
  apply biproduct.hom_ext
  intro j
  rw [Category.assoc, biproduct.map_π,
    biproduct.lift_π_assoc, hl j]

/-- Finite componentwise biproducts preserve weak cokernels.
@isnad1 id=isweakco.1h3v.s5.0b618ce17f8b from=translated src=- shape=9b4740fc vocab=093bcf3e
-/
theorem isWeakCokernel_shortComplexBiproduct
    {J : Type w} [Fintype J]
    (S : J → ShortComplex C)
    (hS : ∀ j, ShortComplex.IsWeakCokernel (S j)) :
    ShortComplex.IsWeakCokernel (shortComplexBiproduct S) := by
  rw [ShortComplex.isWeakCokernel_iff]
  intro W k hk
  change (⨁ fun j ↦ (S j).X₂) ⟶ W at k
  change (biproduct.map fun j ↦ (S j).f) ≫ k = 0 at hk
  have hk_component (j : J) :
      (S j).f ≫
        (biproduct.ι (fun j ↦ (S j).X₂) j ≫ k) = 0 := by
    have h := congrArg
      (fun q ↦ biproduct.ι (fun j ↦ (S j).X₁) j ≫ q) hk
    simpa [Category.assoc, biproduct.ι_map] using h
  choose l hl using fun j ↦
    (ShortComplex.isWeakCokernel_iff (S j)).mp
      (hS j) (biproduct.ι (fun j ↦ (S j).X₂) j ≫ k)
        (hk_component j)
  refine ⟨biproduct.desc l, ?_⟩
  change (biproduct.map fun j ↦ (S j).g) ≫
      biproduct.desc l = k
  apply biproduct.hom_ext'
  intro j
  rw [← Category.assoc, biproduct.ι_map,
    Category.assoc, biproduct.ι_desc, hl j]

/-- A componentwise finite biproduct of radical morphisms is radical once
the categorical radical is available as a two-sided additive Hom ideal.
@isnad1 id=isradica.1h6v.s6.40a62cc90735 from=translated src=- shape=4c9e9a0a vocab=b359d43e
-/
theorem isRadicalMorphism_biproduct_map
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    {X Y : J → C} (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, IsRadicalMorphism (f j)) :
    IsRadicalMorphism (biproduct.map f) := by
  classical
  rw [← R.mem_ideal_iff]
  have hmap :
      biproduct.map f =
        ∑ j : J,
          biproduct.π X j ≫ f j ≫ biproduct.ι Y j := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc]
    rw [Finset.sum_eq_single i]
    · by_cases hij : i = j
      · subst j
        simp
      · simp [hij]
    · intro k _ hki
      simp [Ne.symm hki]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hmap]
  apply (R.ideal.hom (⨁ X) (⨁ Y)).sum_mem
  intro j hj
  change
    biproduct.π X j ≫ f j ≫ biproduct.ι Y j ∈
      R.ideal.hom (⨁ X) (⨁ Y)
  simpa only [Category.assoc] using
    R.ideal.postcomp (biproduct.ι Y j)
      (R.ideal.precomp (biproduct.π X j)
        ((R.mem_ideal_iff (f j)).2 (hf j)))

/-- Tau-approximation conditions are preserved by finite componentwise
biproducts.  Minimality is deliberately not part of this statement.
@isnad1 id=tauappro.1h4v.s5.a6005f19f348 from=translated src=- shape=2fa57707 vocab=b756716e
-/
theorem tauApproximation_shortComplexBiproduct
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    (S : J → ShortComplex C)
    (hS : ∀ j, TauApproximation (S j)) :
    TauApproximation (shortComplexBiproduct S) where
  f_radical :=
    isRadicalMorphism_biproduct_map R (fun j ↦ (S j).f)
      (fun j ↦ (hS j).f_radical)
  g_radical :=
    isRadicalMorphism_biproduct_map R (fun j ↦ (S j).g)
      (fun j ↦ (hS j).g_radical)
  factors_from_left := by
    intro W a ha
    change (⨁ fun j ↦ (S j).X₁) ⟶ W at a
    have ha_component (j : J) :
        IsRadicalMorphism
          (biproduct.ι (fun j ↦ (S j).X₁) j ≫ a) :=
      (R.mem_ideal_iff _).1
        (R.ideal.precomp (biproduct.ι (fun j ↦ (S j).X₁) j)
          ((R.mem_ideal_iff a).2 ha))
    choose b hb using fun j ↦
      (hS j).factors_from_left
        (biproduct.ι (fun j ↦ (S j).X₁) j ≫ a)
        (ha_component j)
    refine ⟨biproduct.desc b, ?_⟩
    change (biproduct.map fun j ↦ (S j).f) ≫
        biproduct.desc b = a
    apply biproduct.hom_ext'
    intro j
    rw [← Category.assoc, biproduct.ι_map,
      Category.assoc, biproduct.ι_desc, hb j]
  factors_into_right := by
    intro W a ha
    change W ⟶ (⨁ fun j ↦ (S j).X₃) at a
    have ha_component (j : J) :
        IsRadicalMorphism
          (a ≫ biproduct.π (fun j ↦ (S j).X₃) j) :=
      (R.mem_ideal_iff _).1
        (R.ideal.postcomp (biproduct.π (fun j ↦ (S j).X₃) j)
          ((R.mem_ideal_iff a).2 ha))
    choose b hb using fun j ↦
      (hS j).factors_into_right
        (a ≫ biproduct.π (fun j ↦ (S j).X₃) j)
        (ha_component j)
    refine ⟨biproduct.lift b, ?_⟩
    change biproduct.lift b ≫
        (biproduct.map fun j ↦ (S j).g) = a
    apply biproduct.hom_ext
    intro j
    rw [Category.assoc, biproduct.map_π,
      biproduct.lift_π_assoc, hb j]

omit [HasFiniteBiproducts C] in
/-- Any morphism annihilated on the right by a right-minimal morphism is
categorically radical.
@isnad1 id=isradica.2h6v.s6.0e891135861b from=translated src=- shape=49e81371 vocab=25a59919
-/
theorem isRadicalMorphism_of_comp_eq_zero_of_isRightMinimal
    {W X Y : C} {a : W ⟶ X} {f : X ⟶ Y}
    (hf : IsRightMinimal f) (ha : a ≫ f = 0) :
    IsRadicalMorphism a := by
  intro b
  have hfix : (𝟙 X - b ≫ a) ≫ f = f := by
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      ha, comp_zero, sub_zero]
  letI : IsIso (𝟙 X - b ≫ a) := hf _ hfix
  exact isIso_one_sub_comp b a

omit [HasFiniteBiproducts C] in
/-- Any morphism annihilated on the left by a left-minimal morphism is
categorically radical.
@isnad1 id=isradica.2h6v.s6.a1ef624f45fb from=translated src=- shape=8c4ab696 vocab=68d4d1b9
-/
theorem isRadicalMorphism_of_comp_eq_zero_of_isLeftMinimal
    {X Y W : C} {f : X ⟶ Y} {a : Y ⟶ W}
    (hf : IsLeftMinimal f) (ha : f ≫ a = 0) :
    IsRadicalMorphism a := by
  intro b
  apply hf
  rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc,
    ha, zero_comp, sub_zero]

/-- A matrix whose every component belongs to the chosen radical Hom ideal
belongs to that ideal.
@isnad1 id=mem.1h7v.s9.1e6c0b8760d2 from=translated src=- shape=080b2b41 vocab=7bd2cc2c
-/
theorem mem_radicalIdeal_of_biproduct_components
    (R : NilpotentRadicalData C)
    {J K : Type w} [Fintype J] [Fintype K]
    {X : J → C} {Y : K → C}
    (q : (⨁ X) ⟶ (⨁ Y))
    (hq : ∀ i j,
      (biproduct.ι X i ≫ q ≫ biproduct.π Y j) ∈
        R.ideal.hom (X i) (Y j)) :
    q ∈ R.ideal.hom (⨁ X) (⨁ Y) := by
  classical
  have hmatrix :
      q = ∑ i : J, ∑ j : K,
        biproduct.π X i ≫
          (biproduct.ι X i ≫ q ≫ biproduct.π Y j) ≫
          biproduct.ι Y j := by
    apply biproduct.hom_ext'
    intro i
    apply biproduct.hom_ext
    intro j
    simp only [Preadditive.comp_sum, Preadditive.sum_comp,
      Category.assoc]
    rw [Finset.sum_eq_single i]
    · rw [Finset.sum_eq_single j]
      · simp
      · intro k _ hkj
        simp [hkj]
      · intro hj
        exact (hj (Finset.mem_univ j)).elim
    · intro k _ hki
      simp [Ne.symm hki]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hmatrix]
  apply (R.ideal.hom (⨁ X) (⨁ Y)).sum_mem
  intro i hi
  apply (R.ideal.hom (⨁ X) (⨁ Y)).sum_mem
  intro j hj
  change
    biproduct.π X i ≫
        (biproduct.ι X i ≫ q ≫ biproduct.π Y j) ≫
        biproduct.ι Y j ∈
      R.ideal.hom (⨁ X) (⨁ Y)
  simpa only [Category.assoc] using
    R.ideal.postcomp (biproduct.ι Y j)
      (R.ideal.precomp (biproduct.π X i) (hq i j))

/-- A morphism out of a finite biproduct belongs to the radical ideal when
each restriction to a summand does.
@isnad1 id=mem.1h6v.s8.8da7e16f2326 from=translated src=- shape=d18c2b9c vocab=5baf7b6e
-/
theorem mem_radicalIdeal_of_biproduct_source_components
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    {X : J → C} {Y : C}
    (q : (⨁ X) ⟶ Y)
    (hq : ∀ i,
      biproduct.ι X i ≫ q ∈ R.ideal.hom (X i) Y) :
    q ∈ R.ideal.hom (⨁ X) Y := by
  classical
  have hsum :
      q = ∑ i : J,
        biproduct.π X i ≫ (biproduct.ι X i ≫ q) := by
    apply biproduct.hom_ext'
    intro i
    simp only [Preadditive.comp_sum]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      simp [Ne.symm hji]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  rw [hsum]
  apply (R.ideal.hom (⨁ X) Y).sum_mem
  intro i hi
  exact R.ideal.precomp (biproduct.π X i) (hq i)

/-- Finite componentwise biproducts preserve right-minimal morphisms whenever
the categorical radical is realized by a two-sided additive Hom ideal.
@isnad1 id=isrightm.1h6v.s6.4fd72109e0db from=translated src=- shape=4c9e9a0a vocab=018343cc
-/
theorem isRightMinimal_biproduct_map
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    {X Y : J → C} (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, IsRightMinimal (f j)) :
    IsRightMinimal (biproduct.map f) := by
  classical
  intro e he
  have hdiag (i : J) :
      (biproduct.ι X i ≫ e ≫ biproduct.π X i) ≫ f i = f i := by
    have h := congrArg
      (fun q ↦ biproduct.ι X i ≫ q ≫ biproduct.π Y i) he
    simpa [Category.assoc] using h
  have hoffdiag (i j : J) (hij : i ≠ j) :
      (biproduct.ι X i ≫ e ≫ biproduct.π X j) ≫ f j = 0 := by
    have h := congrArg
      (fun q ↦ biproduct.ι X i ≫ q ≫ biproduct.π Y j) he
    simpa [Category.assoc, hij] using h
  letI componentIso (i : J) :
      IsIso (biproduct.ι X i ≫ e ≫ biproduct.π X i) :=
    hf i _ (hdiag i)
  let d : (⨁ X) ≅ (⨁ X) :=
    biproduct.mapIso fun i ↦
      asIso (biproduct.ι X i ≫ e ≫ biproduct.π X i)
  have hrad : IsRadicalMorphism (d.hom - e) := by
    rw [← R.mem_ideal_iff]
    apply mem_radicalIdeal_of_biproduct_components R
    intro i j
    by_cases hij : i = j
    · subst j
      have hz :
          biproduct.ι X i ≫ (d.hom - e) ≫ biproduct.π X i = 0 := by
        simp [d]
      rw [hz]
      exact zero_mem _
    · have hc :
          biproduct.ι X i ≫ (d.hom - e) ≫ biproduct.π X j =
            -(biproduct.ι X i ≫ e ≫ biproduct.π X j) := by
        simp [d, hij]
      rw [hc]
      apply neg_mem
      rw [R.mem_ideal_iff]
      exact isRadicalMorphism_of_comp_eq_zero_of_isRightMinimal
        (hf j) (hoffdiag i j hij)
  haveI : IsIso (𝟙 (⨁ X) - (d.hom - e) ≫ d.inv) :=
    hrad d.inv
  have hfactor :
      (𝟙 (⨁ X) - (d.hom - e) ≫ d.inv) ≫ d.hom = e := by
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      d.inv_hom_id, Category.comp_id]
    abel
  rw [← hfactor]
  infer_instance

/-- Finite componentwise biproducts preserve left-minimal morphisms whenever
the categorical radical is realized by a two-sided additive Hom ideal.
@isnad1 id=isleftmi.1h6v.s6.d4c20e0bc4a8 from=translated src=- shape=4c9e9a0a vocab=8769d512
-/
theorem isLeftMinimal_biproduct_map
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    {X Y : J → C} (f : ∀ j, X j ⟶ Y j)
    (hf : ∀ j, IsLeftMinimal (f j)) :
    IsLeftMinimal (biproduct.map f) := by
  classical
  intro e he
  have hdiag (i : J) :
      f i ≫ (biproduct.ι Y i ≫ e ≫ biproduct.π Y i) = f i := by
    have h := congrArg
      (fun q ↦ biproduct.ι X i ≫ q ≫ biproduct.π Y i) he
    simpa [Category.assoc] using h
  have hoffdiag (i j : J) (hij : i ≠ j) :
      f i ≫ (biproduct.ι Y i ≫ e ≫ biproduct.π Y j) = 0 := by
    have h := congrArg
      (fun q ↦ biproduct.ι X i ≫ q ≫ biproduct.π Y j) he
    simpa [Category.assoc, hij] using h
  letI componentIso (i : J) :
      IsIso (biproduct.ι Y i ≫ e ≫ biproduct.π Y i) :=
    hf i _ (hdiag i)
  let d : (⨁ Y) ≅ (⨁ Y) :=
    biproduct.mapIso fun i ↦
      asIso (biproduct.ι Y i ≫ e ≫ biproduct.π Y i)
  have hrad : IsRadicalMorphism (d.hom - e) := by
    rw [← R.mem_ideal_iff]
    apply mem_radicalIdeal_of_biproduct_components R
    intro i j
    by_cases hij : i = j
    · subst j
      have hz :
          biproduct.ι Y i ≫ (d.hom - e) ≫ biproduct.π Y i = 0 := by
        simp [d]
      rw [hz]
      exact zero_mem _
    · have hc :
          biproduct.ι Y i ≫ (d.hom - e) ≫ biproduct.π Y j =
            -(biproduct.ι Y i ≫ e ≫ biproduct.π Y j) := by
        simp [d, hij]
      rw [hc]
      apply neg_mem
      rw [R.mem_ideal_iff]
      exact isRadicalMorphism_of_comp_eq_zero_of_isLeftMinimal
        (hf i) (hoffdiag i j hij)
  haveI : IsIso (𝟙 (⨁ Y) - (d.hom - e) ≫ d.inv) :=
    hrad d.inv
  have hfactor :
      (𝟙 (⨁ Y) - (d.hom - e) ≫ d.inv) ≫ d.hom = e := by
    simp only [Preadditive.sub_comp, Category.id_comp, Category.assoc,
      d.inv_hom_id, Category.comp_id]
    abel
  rw [← hfactor]
  infer_instance

/-- Right tau-sequences are closed under finite componentwise biproducts.
@isnad1 id=righttau.1h4v.s5.48cb5b3524e4 from=translated src=- shape=2fa57707 vocab=b4964a90
-/
theorem rightTauSequence_shortComplexBiproduct
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    (S : J → ShortComplex C)
    (hS : ∀ j, RightTauSequence (S j)) :
    RightTauSequence (shortComplexBiproduct S) where
  toTauApproximation :=
    tauApproximation_shortComplexBiproduct R S
      (fun j ↦ (hS j).toTauApproximation)
  minimalWeakKernel := ⟨
    isWeakKernel_shortComplexBiproduct S
      (fun j ↦ (hS j).minimalWeakKernel.1),
    isRightMinimal_biproduct_map R (fun j ↦ (S j).f)
      (fun j ↦ (hS j).minimalWeakKernel.2)⟩

/-- Left tau-sequences are closed under finite componentwise biproducts.
@isnad1 id=lefttaus.1h4v.s5.fe55594163aa from=translated src=- shape=2fa57707 vocab=e57a0d89
-/
theorem leftTauSequence_shortComplexBiproduct
    (R : NilpotentRadicalData C)
    {J : Type w} [Fintype J]
    (S : J → ShortComplex C)
    (hS : ∀ j, LeftTauSequence (S j)) :
    LeftTauSequence (shortComplexBiproduct S) where
  toTauApproximation :=
    tauApproximation_shortComplexBiproduct R S
      (fun j ↦ (hS j).toTauApproximation)
  minimalWeakCokernel := ⟨
    isWeakCokernel_shortComplexBiproduct S
      (fun j ↦ (hS j).minimalWeakCokernel.1),
    isLeftMinimal_biproduct_map R (fun j ↦ (S j).g)
      (fun j ↦ (hS j).minimalWeakCokernel.2)⟩

end QuotientSubmoduleEquidistribution.Iyama
