/-
Copyright (c) 2026 Jiyuan Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jiyuan Tan
-/

module
public import Tengoku.Causalean.Causalean.Mathlib.Optimization.Affine.SignCell.Closure
public import Tengoku

/-! # Preservation of bounded extrema

Continuous real objectives have the same bounded infima and suprema on a nonempty strict
affine cell and on its weak relaxation.
-/

public section

open Set

namespace Causalean.Mathlib.Optimization.Affine.SignCell

/-- Given [a nonempty strict cell](hyp:hΓ) and [a continuous real objective](hyp:hφ), [the
closures of its strict-cell and weak-cell image sets are equal](goal).
@isnad1 id=eq.2h3v.s6.53ab9b55519f from=translated src=- shape=06de4f30 vocab=66285966
-/
theorem closure_image_strictCell_eq_closure_image_weakCell {n : ℕ}
    {Γ : AffineSystem n} {φ : (Fin n → ℝ) → ℝ}
    (hΓ : (strictCell Γ).Nonempty) (hφ : Continuous φ) :
    closure (φ '' strictCell Γ) = closure (φ '' weakCell Γ) := by
  rw [← closure_strictCell_eq_weakCell hΓ, closure_image_closure hφ]

/-- Given [a nonempty strict cell](hyp:hΓ), [a continuous real objective](hyp:hφ), and [a
lower bound for its strict-cell image](hyp:hBdd), [the weak-cell image is bounded below](goal).
@isnad1 id=bddbelow.3h3v.s6.c5116d879e4a from=translated src=- shape=84977e11 vocab=9d355d29
-/
theorem bddBelow_image_weakCell_of_strictCell {n : ℕ}
    {Γ : AffineSystem n} {φ : (Fin n → ℝ) → ℝ}
    (hΓ : (strictCell Γ).Nonempty) (hφ : Continuous φ)
    (hBdd : BddBelow (φ '' strictCell Γ)) : BddBelow (φ '' weakCell Γ) := by
  have hcl := closure_image_strictCell_eq_closure_image_weakCell hΓ hφ
  rw [BddBelow, ← lowerBounds_closure (φ '' weakCell Γ), ← hcl, lowerBounds_closure]
  exact hBdd

/-- Given [a nonempty strict cell](hyp:hΓ), [a continuous real objective](hyp:hφ), and [an
upper bound for its strict-cell image](hyp:hBdd), [the weak-cell image is bounded above](goal).
@isnad1 id=bddabove.3h3v.s6.25a9376caf48 from=translated src=- shape=84977e11 vocab=0a2ffb0c
-/
theorem bddAbove_image_weakCell_of_strictCell {n : ℕ}
    {Γ : AffineSystem n} {φ : (Fin n → ℝ) → ℝ}
    (hΓ : (strictCell Γ).Nonempty) (hφ : Continuous φ)
    (hBdd : BddAbove (φ '' strictCell Γ)) : BddAbove (φ '' weakCell Γ) := by
  have hcl := closure_image_strictCell_eq_closure_image_weakCell hΓ hφ
  rw [BddAbove, ← upperBounds_closure (φ '' weakCell Γ), ← hcl, upperBounds_closure]
  exact hBdd

/-- Given [a nonempty strict cell](hyp:hΓ), [a continuous real objective](hyp:hφ), and [a
lower bound for its strict-cell image](hyp:hBdd), [the strict and weak image sets have the
same infimum](goal).
@isnad1 id=eq.3h3v.s6.d589fabbb6d9 from=translated src=- shape=133998f2 vocab=70efb5f8
-/
theorem sInf_image_strictCell_eq_weakCell {n : ℕ}
    {Γ : AffineSystem n} {φ : (Fin n → ℝ) → ℝ}
    (hΓ : (strictCell Γ).Nonempty) (hφ : Continuous φ)
    (hBdd : BddBelow (φ '' strictCell Γ)) :
    sInf (φ '' strictCell Γ) = sInf (φ '' weakCell Γ) := by
  have hcl := closure_image_strictCell_eq_closure_image_weakCell hΓ hφ
  have hlb : lowerBounds (φ '' strictCell Γ) = lowerBounds (φ '' weakCell Γ) := by
    rw [← lowerBounds_closure (φ '' strictCell Γ), hcl, lowerBounds_closure]
  have hBdd' := bddBelow_image_weakCell_of_strictCell hΓ hφ hBdd
  have hne : (φ '' strictCell Γ).Nonempty := hΓ.image φ
  have hne' : (φ '' weakCell Γ).Nonempty := hne.mono (image_mono (strictCell_subset_weakCell Γ))
  rw [← csSup_lowerBounds_eq_csInf hBdd hne,
    ← csSup_lowerBounds_eq_csInf hBdd' hne', hlb]

/-- Given [a nonempty strict cell](hyp:hΓ), [a continuous real objective](hyp:hφ), and [an
upper bound for its strict-cell image](hyp:hBdd), [the strict and weak image sets have the
same supremum](goal).
@isnad1 id=eq.3h3v.s6.2f925e1b77ab from=translated src=- shape=133998f2 vocab=7acc1837
-/
theorem sSup_image_strictCell_eq_weakCell {n : ℕ}
    {Γ : AffineSystem n} {φ : (Fin n → ℝ) → ℝ}
    (hΓ : (strictCell Γ).Nonempty) (hφ : Continuous φ)
    (hBdd : BddAbove (φ '' strictCell Γ)) :
    sSup (φ '' strictCell Γ) = sSup (φ '' weakCell Γ) := by
  have hcl := closure_image_strictCell_eq_closure_image_weakCell hΓ hφ
  have hub : upperBounds (φ '' strictCell Γ) = upperBounds (φ '' weakCell Γ) := by
    rw [← upperBounds_closure (φ '' strictCell Γ), hcl, upperBounds_closure]
  have hBdd' := bddAbove_image_weakCell_of_strictCell hΓ hφ hBdd
  have hne : (φ '' strictCell Γ).Nonempty := hΓ.image φ
  have hne' : (φ '' weakCell Γ).Nonempty := hne.mono (image_mono (strictCell_subset_weakCell Γ))
  rw [← csInf_upperBounds_eq_csSup hBdd hne,
    ← csInf_upperBounds_eq_csSup hBdd' hne', hub]

/-- Given [an affine objective](hyp:f), [a nonempty strict cell](hyp:hΓ), and [a lower bound
for the strict-cell objective image](hyp:hBdd), [the affine objective has the same infimum
on the strict cell and weak relaxation](goal).
@isnad1 id=eq.2h3v.s6.4dc674baa0b1 from=translated src=- shape=906a2650 vocab=6f2ab05b
-/
theorem sInf_affineEval_strictCell_eq_weakCell {n : ℕ}
    {Γ : AffineSystem n} (f : AffineFn n) (hΓ : (strictCell Γ).Nonempty)
    (hBdd : BddBelow (f.eval '' strictCell Γ)) :
    sInf (f.eval '' strictCell Γ) = sInf (f.eval '' weakCell Γ) := by
  exact sInf_image_strictCell_eq_weakCell hΓ f.continuous_eval hBdd

/-- Given [an affine objective](hyp:f), [a nonempty strict cell](hyp:hΓ), and [an upper bound
for the strict-cell objective image](hyp:hBdd), [the affine objective has the same supremum
on the strict cell and weak relaxation](goal).
@isnad1 id=eq.2h3v.s6.2cfb89ee0826 from=translated src=- shape=906a2650 vocab=a959a8e7
-/
theorem sSup_affineEval_strictCell_eq_weakCell {n : ℕ}
    {Γ : AffineSystem n} (f : AffineFn n) (hΓ : (strictCell Γ).Nonempty)
    (hBdd : BddAbove (f.eval '' strictCell Γ)) :
    sSup (f.eval '' strictCell Γ) = sSup (f.eval '' weakCell Γ) := by
  exact sSup_image_strictCell_eq_weakCell hΓ f.continuous_eval hBdd

end Causalean.Mathlib.Optimization.Affine.SignCell
