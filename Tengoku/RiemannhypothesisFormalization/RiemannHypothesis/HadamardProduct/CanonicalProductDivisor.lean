/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Analysis.Analytic.Order
import Tengoku.Seed.Topology.Algebra.InfiniteSum.Group
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.LogDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Multiplicity of occurrence-indexed genus-one products

This module proves that the analytic order of an inverse-square genus-one
product is exactly the cardinality of the corresponding location fiber.
The theorem is independent of any particular completed L-function.
-/

open Set

namespace OverflowResidueRH

/-- A genus-one factor has a simple zero at its designated nonzero location.
@isnad1 id=eq.1h1v.s5.97d3c3742980 from=translated src=- shape=740dc023 vocab=a101c87a
-/
theorem hadamardGenus1Factor_analyticOrderAt_self
    {ρ : ℂ} (hρ : ρ ≠ 0) :
    analyticOrderAt (hadamardGenus1Factor ρ) ρ = 1 := by
  let left : ℂ → ℂ := fun z ↦ 1 - z / ρ
  let right : ℂ → ℂ := fun z ↦ Complex.exp (z / ρ)
  have hleft : AnalyticAt ℂ left ρ := by
    dsimp [left]
    fun_prop
  have hright : AnalyticAt ℂ right ρ := by
    dsimp [right]
    fun_prop
  have hleft_zero : left ρ = 0 := by
    simp [left, hρ]
  have hleft_deriv : deriv left ρ = -(1 / ρ) := by
    dsimp [left]
    simp
  have hleft_order : analyticOrderAt left ρ = 1 :=
    hleft.analyticOrderAt_eq_one_of_zero_deriv_ne_zero hleft_zero (by
      rw [hleft_deriv]
      exact neg_ne_zero.mpr (one_div_ne_zero hρ))
  have hright_order : analyticOrderAt right ρ = 0 :=
    hright.analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)
  change analyticOrderAt (left * right) ρ = 1
  rw [analyticOrderAt_mul hleft hright, hleft_order, hright_order, add_zero]

/-- A single genus-one factor is entire.
@isnad1 id=differen.0h1v.s6.62c8fcc4524d from=translated src=- shape=55d61ed8 vocab=90584126
-/
theorem hadamardGenus1Factor_differentiable (ρ : ℂ) :
    Differentiable ℂ (hadamardGenus1Factor ρ) :=
  fun z ↦ hadamardGenus1Factor_differentiableAt ρ z

/-- Inverse-square summability and norm properness make the full genus-one
product entire.
@isnad1 id=differen.2h2v.s6.53f6362c4ee7 from=translated src=- shape=10fffd03 vocab=feebe770
-/
theorem infiniteHadamardProduct_differentiable_of_invSq_normProper
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc) :
    Differentiable ℂ (infiniteHadamardProduct zeroLoc) := by
  let Hex : HadamardFiniteExhaustion zeroLoc :=
    HadamardFiniteExhaustion.of_invSq_mono_exhaustive Hinv
      Hproper.normExhaustion Hproper.normExhaustion_mono
      Hproper.normExhaustion_exhaustive
  let Hluc : HadamardProductLocallyUniformLimitData zeroLoc Hex :=
    HadamardProductLocallyUniformLimitData.of_invSq_univ Hinv Hex
      Hproper.normExhaustion_exhaustive
  rw [← differentiableOn_univ]
  exact Hluc.infinite_differentiableOn

/-- Norm properness is inherited by a subtype of the index set.
@isnad1 id=hadamard.1h3v.s4.0a58622b1818 from=translated src=- shape=240c37f0 vocab=edd5f3ed
-/
theorem HadamardZeroNormProper.subtype
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroNormProper zeroLoc) (p : ι → Prop) :
    HadamardZeroNormProper (fun i : Subtype p ↦ zeroLoc i.1) := by
  refine ⟨?_⟩
  intro R
  exact (H.finite_norm_le R).preimage Subtype.val_injective.injOn

/-- Inverse-square Hadamard data is inherited by a subtype when norm
properness supplies the eventual-escape field.
@isnad1 id=hadamard.2h3v.s5.8ba54a79f4b6 from=translated src=- shape=f446b717 vocab=eb4f62fb
-/
theorem HadamardZeroInvSqSummability.subtype_of_normProper
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc) (p : ι → Prop) :
    HadamardZeroInvSqSummability (fun i : Subtype p ↦ zeroLoc i.1) :=
  HadamardZeroInvSqSummability.of_invSqSummable_normProper
    (fun i ↦ Hinv.zero_ne i.1)
    (Hinv.inv_sq_summable.subtype p)
    (Hproper.subtype p)

/-- The fiber of a norm-proper location map over one point is finite.
@isnad1 id=finite.1h3v.s4.c4b8f1f1b8e5 from=translated src=- shape=9252627c vocab=3e56e3a9
-/
theorem HadamardZeroNormProper.finite_fiber
    {ι : Type*} {zeroLoc : ι → ℂ}
    (H : HadamardZeroNormProper zeroLoc) (ρ : ℂ) :
    {i : ι | zeroLoc i = ρ}.Finite := by
  apply (H.finite_norm_le ‖ρ‖).subset
  intro i hi
  change ‖zeroLoc i‖ ≤ ‖ρ‖
  rw [hi]

/-- The canonical genus-one product has analytic order equal to the number of
indices located at the point.  Repeated locations are therefore counted with
their full multiplicity.
@isnad1 id=eq.2h3v.s5.8b1770229b43 from=translated src=- shape=b9e23960 vocab=6b125eaf
-/
theorem infiniteHadamardProduct_analyticOrderAt_eq_fiber_natCard
    {ι : Type*} {zeroLoc : ι → ℂ}
    (Hinv : HadamardZeroInvSqSummability zeroLoc)
    (Hproper : HadamardZeroNormProper zeroLoc)
    (ρ : ℂ) :
    analyticOrderAt (infiniteHadamardProduct zeroLoc) ρ =
      (Nat.card {i : ι // zeroLoc i = ρ} : ENat) := by
  classical
  let s : Set ι := {i | zeroLoc i = ρ}
  change analyticOrderAt (infiniteHadamardProduct zeroLoc) ρ =
    (Nat.card s : ENat)
  have hs_finite : s.Finite := Hproper.finite_fiber ρ
  letI : Fintype s := hs_finite.fintype
  let fiberLoc : s → ℂ := fun i ↦ zeroLoc i.1
  let complementLoc : (sᶜ : Set ι) → ℂ := fun i ↦ zeroLoc i.1
  let fiberProduct : ℂ → ℂ := infiniteHadamardProduct fiberLoc
  let complementProduct : ℂ → ℂ := infiniteHadamardProduct complementLoc
  have HcompProper : HadamardZeroNormProper complementLoc :=
    Hproper.subtype (fun i ↦ i ∈ sᶜ)
  have HcompInv : HadamardZeroInvSqSummability complementLoc :=
    Hinv.subtype_of_normProper Hproper (fun i ↦ i ∈ sᶜ)
  have hfiber_eq :
      fiberProduct = fun z ↦ hadamardGenus1Factor ρ z ^ Fintype.card s := by
    funext z
    simp only [fiberProduct, infiniteHadamardProduct, fiberLoc, tprod_fintype]
    calc
      ∏ i : s, hadamardGenus1Factor (zeroLoc i.1) z =
          ∏ _i : s, hadamardGenus1Factor ρ z := by
        apply Fintype.prod_congr
        intro i
        rw [i.2]
      _ = hadamardGenus1Factor ρ z ^ Fintype.card s := by simp
  have hsplit : fiberProduct * complementProduct =
      infiniteHadamardProduct zeroLoc := by
    funext z
    change
      (∏' i : s, hadamardGenus1Factor (zeroLoc i.1) z) *
          (∏' i : (sᶜ : Set ι), hadamardGenus1Factor (zeroLoc i.1) z) =
        ∏' i, hadamardGenus1Factor (zeroLoc i) z
    refine Multipliable.tprod_mul_tprod_compl
      (f := fun i : ι ↦ hadamardGenus1Factor (zeroLoc i) z)
      (s := s) ?_ ?_
    · exact Multipliable.of_finite
    · exact HcompInv.product_multipliable z
  have hfiber_analytic : AnalyticAt ℂ fiberProduct ρ := by
    rw [hfiber_eq]
    exact (hadamardGenus1Factor_differentiable ρ).analyticAt ρ |>.pow _
  have hfiber_order :
      analyticOrderAt fiberProduct ρ = (Fintype.card s : ENat) := by
    rw [hfiber_eq]
    change analyticOrderAt ((hadamardGenus1Factor ρ) ^ Fintype.card s) ρ =
      (Fintype.card s : ENat)
    by_cases hsne : s.Nonempty
    · obtain ⟨i, hi⟩ := hsne
      have hρ : ρ ≠ 0 := by
        rw [← hi]
        exact Hinv.zero_ne i
      rw [analyticOrderAt_pow
        ((hadamardGenus1Factor_differentiable ρ).analyticAt ρ),
        hadamardGenus1Factor_analyticOrderAt_self hρ]
      simp
    · letI : IsEmpty s := ⟨fun i ↦ hsne ⟨i.1, i.2⟩⟩
      have hcard : Fintype.card s = 0 := Fintype.card_eq_zero
      simp [analyticOrderAt_eq_zero]
  have hcomp_diff : Differentiable ℂ complementProduct :=
    infiniteHadamardProduct_differentiable_of_invSq_normProper HcompInv HcompProper
  have hcomp_ne : complementProduct ρ ≠ 0 := by
    apply HcompInv.infiniteProduct_ne_zero
    intro i hi
    exact i.2 hi.symm
  have hcomp_order : analyticOrderAt complementProduct ρ = 0 :=
    (hcomp_diff.analyticAt ρ).analyticOrderAt_eq_zero.mpr hcomp_ne
  rw [← hsplit,
    analyticOrderAt_mul hfiber_analytic (hcomp_diff.analyticAt ρ),
    hfiber_order, hcomp_order, add_zero]
  rw [Nat.card_eq_fintype_card]

end OverflowResidueRH
