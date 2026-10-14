/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic

/-!
# Hölder bounds for the parabolic metric

This module names the seminorm used by the space-time regularity statements.
The measure-theoretic representative predicate records agreement on a set.
-/

@[expose] public section

open scoped ENNReal NNReal Topology

open MeasureTheory Set

noncomputable section

namespace CKN.Foundation.Parabolic

/-- Pointwise Hölder seminorm bound with respect to parabolic distance. -/
def ParabolicHolderSeminormLE
    (U : Set ParabolicPoint) (g : ParabolicPoint → ℝ)
    (α K : ℝ) : Prop :=
  ∀ x ∈ U, ∀ y ∈ U,
    |g x - g y| ≤ K * parabolicDist x y ^ α

/-- Existence of an a.e.-equal representative satisfying a parabolic Hölder bound. -/
def HasParabolicHolderRepresentativeOn
    (U : Set ParabolicPoint) (f : ParabolicPoint → ℝ)
    (α K : ℝ) : Prop :=
  ∃ g : ParabolicPoint → ℝ,
    g =ᵐ[volume.restrict U] f ∧
      ParabolicHolderSeminormLE U g α K

/--
@isnad1 id=le.0h2v.s4.a1bbd99c861c from=translated src=- shape=5ffe46ab vocab=8b9ca051
-/
lemma parabolicDist_nonneg (x y : ParabolicPoint) :
    0 ≤ parabolicDist x y := by
  exact (vec3EuclideanNorm_nonneg _).trans (le_max_left _ _)

namespace ParabolicHolderSeminormLE

/--
@isnad1 id=paraboli.2h5v.s5.fabe2dfb557f from=translated src=- shape=8261fadd vocab=9f5d8bba
-/
theorem mono_set {U V : Set ParabolicPoint} {g : ParabolicPoint → ℝ}
    {α K : ℝ} (h : ParabolicHolderSeminormLE U g α K) (hVU : V ⊆ U) :
    ParabolicHolderSeminormLE V g α K :=
  fun x hx y hy => h x (hVU hx) y (hVU hy)

end ParabolicHolderSeminormLE

/--
@isnad1 id=hasparab.1h4v.s4.68bcd427171c from=translated src=- shape=d0c213bb vocab=75d2b8c6
-/
theorem ParabolicHolderSeminormLE.hasRepresentative
    {U : Set ParabolicPoint} {f : ParabolicPoint → ℝ} {α K : ℝ}
    (h : ParabolicHolderSeminormLE U f α K) :
    HasParabolicHolderRepresentativeOn U f α K :=
  ⟨f, Filter.Eventually.of_forall fun _ => rfl, h⟩

end CKN.Foundation.Parabolic
