/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev
-/
module

public import Tengoku.LeanPool.LeanPool.HopfProblem.Prelude

/-!
# Hopf problem: homology of x · small chain biprod

Supporting definitions and proofs for this stage of the six-sphere construction.
-/

open Set Function Filter Manifold Topology

open scoped BigOperators CategoryTheory Complex.UnitDisc ComplexConjugate ContDiff ContinuousMap
  Convolution ENNReal EuclideanSpace Fin.NatCast InnerProductSpace Interval Matrix MatrixGroups
  Modular NNReal Pointwise RealInnerProductSpace TensorProduct UniformConvergence Uniformity
  UpperHalfPlane

universe u v

noncomputable section

namespace Mathoverflow1973

local infixr:80 " ≫ₚ " => Path.trans

local notation:100 f " ∣[" k "] " a:100 => SlashAction.map k a f

private theorem SmallChainBiprod.desc_inl_apply {A B S : ModuleCat.{0} ℤ} (u : A ⟶ S) (v : B ⟶ S)
    (x : A) :
    (CategoryTheory.Limits.biprod.desc u v).hom
        ((CategoryTheory.Limits.biprod.inl : A ⟶ A ⊞ B).hom x) =
      u.hom x := by
  exact congrArg (fun f : A ⟶ S => f.hom x) (CategoryTheory.Limits.biprod.inl_desc u v)

private theorem SmallChainBiprod.desc_inr_apply {A B S : ModuleCat.{0} ℤ} (u : A ⟶ S) (v : B ⟶ S)
    (y : B) :
    (CategoryTheory.Limits.biprod.desc u v).hom
        ((CategoryTheory.Limits.biprod.inr : B ⟶ A ⊞ B).hom y) =
      v.hom y := by
  exact congrArg (fun f : B ⟶ S => f.hom y) (CategoryTheory.Limits.biprod.inr_desc u v)

private def
    SmallChainBiprod.shortComplex {A B I S : ModuleCat.{0} ℤ} (a : I ⟶ A) (b : I ⟶ B) (u : A ⟶ S)
    (v : B ⟶ S) (w : a ≫ u = b ≫ v) : CategoryTheory.ShortComplex (ModuleCat.{0} ℤ) :=
  CategoryTheory.ShortComplex.mk (CategoryTheory.Limits.biprod.lift a (-b))
    (CategoryTheory.Limits.biprod.desc u v)
    (by
      rw [CategoryTheory.Limits.biprod.lift_desc, CategoryTheory.Preadditive.neg_comp, w,
        add_neg_cancel])

private theorem SmallChainBiprod.right_surjective {A B S : ModuleCat.{0} ℤ} (u : A ⟶ S) (v : B ⟶ S)
    (hjoint : ∀ s : S, ∃ x : A, ∃ y : B, u.hom x + v.hom y = s) :
    Function.Surjective (CategoryTheory.Limits.biprod.desc u v).hom := by
  intro s
  obtain ⟨x, y, hxy⟩ := hjoint s
  refine
    ⟨(CategoryTheory.Limits.biprod.inl : A ⟶ A ⊞ B).hom x +
        (CategoryTheory.Limits.biprod.inr : B ⟶ A ⊞ B).hom y,
      ?_⟩
  simpa only [map_add, desc_inl_apply, desc_inr_apply] using hxy

private theorem SmallChainBiprod.shortExact {A B I S : ModuleCat.{0} ℤ} (a : I ⟶ A) (b : I ⟶ B)
    (u : A ⟶ S) (v : B ⟶ S) (w : a ≫ u = b ≫ v) (ha : Function.Injective a.hom)
    (hjoint : ∀ s : S, ∃ x : A, ∃ y : B, u.hom x + v.hom y = s)
    (hoverlap : ∀ (x : A) (y : B), u.hom x = v.hom y → ∃ z : I, a.hom z = x ∧ b.hom z = y) :
    (shortComplex a b u v w).ShortExact
    where
  exact := exact a b u v w hoverlap
  mono_f := (ModuleCat.mono_iff_injective _).mpr (left_injective a b ha)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (right_surjective u v hjoint)

private theorem SmallChainBiprod.lift_f_biprodXIso_hom {K L J : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (a : J ⟶ K) (b : J ⟶ L) (n : ℕ) :
    (CategoryTheory.Limits.biprod.lift a b).f n ≫ (HomologicalComplex.biprodXIso K L n).hom =
      CategoryTheory.Limits.biprod.lift (a.f n) (b.f n) := by
  apply CategoryTheory.Limits.biprod.hom_ext
  · simp only [CategoryTheory.Category.assoc, HomologicalComplex.biprodXIso_hom_fst,
      HomologicalComplex.biprod_lift_fst_f, CategoryTheory.Limits.biprod.lift_fst]
  · simp only [CategoryTheory.Category.assoc, HomologicalComplex.biprodXIso_hom_snd,
      HomologicalComplex.biprod_lift_snd_f, CategoryTheory.Limits.biprod.lift_snd]

private theorem SmallChainBiprod.biprodXIso_inv_desc_f {K L T : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (u : K ⟶ T) (v : L ⟶ T) (n : ℕ) :
    (HomologicalComplex.biprodXIso K L n).inv ≫ (CategoryTheory.Limits.biprod.desc u v).f n =
      CategoryTheory.Limits.biprod.desc (u.f n) (v.f n) := by
  apply CategoryTheory.Limits.biprod.hom_ext'
  · simp only [← CategoryTheory.Category.assoc, HomologicalComplex.inl_biprodXIso_inv,
      HomologicalComplex.biprod_inl_desc_f, CategoryTheory.Limits.biprod.inl_desc]
  · simp only [← CategoryTheory.Category.assoc, HomologicalComplex.inr_biprodXIso_inv,
      HomologicalComplex.biprod_inr_desc_f, CategoryTheory.Limits.biprod.inr_desc]

private theorem SmallChainBiprod.biprodXIso_hom_desc_f {K L T : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (u : K ⟶ T) (v : L ⟶ T) (n : ℕ) :
    (HomologicalComplex.biprodXIso K L n).hom ≫
        CategoryTheory.Limits.biprod.desc (u.f n) (v.f n) =
      (CategoryTheory.Limits.biprod.desc u v).f n := by
  rw [← biprodXIso_inv_desc_f u v n, CategoryTheory.Iso.hom_inv_id_assoc]

private def SmallChainBiprod.shortComplexOfComplexes {K L J T : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (a : J ⟶ K) (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T) (w : a ≫ u = b ≫ v) :
    CategoryTheory.ShortComplex (ChainComplex (ModuleCat.{0} ℤ) ℕ) :=
  CategoryTheory.ShortComplex.mk (CategoryTheory.Limits.biprod.lift a (-b))
    (CategoryTheory.Limits.biprod.desc u v)
    (by
      rw [CategoryTheory.Limits.biprod.lift_desc, CategoryTheory.Preadditive.neg_comp, w,
        add_neg_cancel])

public

private def
    SmallChainBiprod.shortComplexOfComplexesEvalIso {K L J T : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (a : J ⟶ K) (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T) (w : a ≫ u = b ≫ v) (n : ℕ) :
    (shortComplexOfComplexes a b u v w).map
        (HomologicalComplex.eval (ModuleCat.{0} ℤ) (ComplexShape.down ℕ) n) ≅
      shortComplex (a.f n) (b.f n) (u.f n) (v.f n) (square_f a b u v w n) := by
  refine
    CategoryTheory.ShortComplex.isoMk (CategoryTheory.Iso.refl _)
      (HomologicalComplex.biprodXIso K L n) (CategoryTheory.Iso.refl _) ?_ ?_
  · change
      𝟙 _ ≫ CategoryTheory.Limits.biprod.lift (a.f n) (-(b.f n)) =
        (CategoryTheory.Limits.biprod.lift a (-b)).f n ≫ (HomologicalComplex.biprodXIso K L n).hom
    simpa only [CategoryTheory.Category.id_comp, HomologicalComplex.neg_f_apply] using
      (lift_f_biprodXIso_hom a (-b) n).symm
  · change
      (HomologicalComplex.biprodXIso K L n).hom ≫
          CategoryTheory.Limits.biprod.desc (u.f n) (v.f n) =
        (CategoryTheory.Limits.biprod.desc u v).f n ≫ 𝟙 _
    simpa only [CategoryTheory.Category.comp_id] using biprodXIso_hom_desc_f u v n

private theorem SmallChainBiprod.shortExactOfComplexes {K L J T : ChainComplex (ModuleCat.{0} ℤ) ℕ}
    (a : J ⟶ K) (b : J ⟶ L) (u : K ⟶ T) (v : L ⟶ T) (w : a ≫ u = b ≫ v)
    (ha : ∀ n : ℕ, Function.Injective (a.f n).hom)
    (hjoint : ∀ (n : ℕ) (s : T.X n), ∃ x : K.X n, ∃ y : L.X n, (u.f n).hom x + (v.f n).hom y = s)
    (hoverlap :
      ∀ (n : ℕ) (x : K.X n) (y : L.X n),
        (u.f n).hom x = (v.f n).hom y → ∃ z : J.X n, (a.f n).hom z = x ∧ (b.f n).hom z = y) :
    (shortComplexOfComplexes a b u v w).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  exact
    CategoryTheory.ShortComplex.shortExact_of_iso
      (shortComplexOfComplexesEvalIso a b u v w n).symm
      (shortExact (a.f n) (b.f n) (u.f n) (v.f n) (square_f a b u v w n) (ha n) (hjoint n)
        (hoverlap n))

end Mathoverflow1973

end
