/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.BooleanAnalysis.HarmonicMean.Internal.Mean
public import Tengoku.Complexitylib.Complexitylib.BooleanAnalysis.Bernoulli.Internal
public import Tengoku

/-!
# Coordinate splitting for the harmonic mean transform

Finite product calculations used in the induction in Korten's Lemma 12.
-/

public section

namespace Complexity.BooleanAnalysis

open Finset
open scoped BigOperators

/--
@isnad1 id=eq.0h2v.s8.c1370bd4cc9c from=translated src=- shape=5cadfff0 vocab=7fda088f
-/
theorem expect_cons_internal {n : ℕ} (f : (Fin (n + 1) → Bool) → ℝ) :
    (𝔼 x, f x) = ((𝔼 x, f (Fin.cons false x)) + (𝔼 x, f (Fin.cons true x))) / 2 := by
  rw [← Fintype.expect_equiv (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))
    (fun x => f (Fin.cons x.1 x.2)) f (fun _ => rfl)]
  rw [expect_pair_internal, expect_bool_internal]

/--
@isnad1 id=le.1h4v.s5.6b2798c706ab from=translated src=- shape=5c57a1be vocab=3b771058
-/
theorem projectionAverage_nonneg_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (selected x : ι → Bool) :
    0 ≤ projectionAverage f selected x :=
  expect_nonneg fun _ _ => hf _

/--
@isnad1 id=le.1h3v.s5.a30b5c68d975 from=translated src=- shape=0b531906 vocab=0bd237b1
-/
theorem harmonicTransform_nonneg_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (selected : ι → Bool) :
    0 ≤ harmonicTransform f selected :=
  harmonicMean_nonneg_internal (projectionAverage_nonneg_internal hf selected)

/--
@isnad1 id=eq.0h3v.s4.57f48872a431 from=translated src=- shape=ebd2f44a vocab=3de0c738
-/
theorem harmonicTransform_const_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ℝ) (selected : ι → Bool) : harmonicTransform (fun _ => c) selected = c := by
  have he : projectionAverage (fun _ => c) selected = fun _ => c := by
    funext x
    simp [projectionAverage]
  rw [harmonicTransform, he, harmonicMean_const_internal]

/--
@isnad1 id=eq.0h5v.s6.abceafd29f30 from=translated src=- shape=3de13134 vocab=59f50a23
-/
theorem projectionAverage_midpoint_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f g : (ι → Bool) → ℝ) (selected x : ι → Bool) :
    projectionAverage (fun x => (f x + g x) / 2) selected x =
      (projectionAverage f selected x + projectionAverage g selected x) / 2 := by
  simp only [projectionAverage, ← expect_div, expect_add_distrib]

/--
@isnad1 id=eq.0h5v.s7.48e48b0ee8e8 from=translated src=- shape=f426d799 vocab=5c921be8
-/
theorem projectionAverage_cons_false_internal {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected x : Fin n → Bool) (b : Bool) :
    projectionAverage f (Fin.cons false selected) (Fin.cons b x) =
      projectionAverage (fun x => (f (Fin.cons false x) + f (Fin.cons true x)) / 2)
        selected x := by
  have hm (a : Bool) (y : Fin n → Bool) :
      (fun i : Fin (n + 1) => if (Fin.cons false selected : Fin (n + 1) → Bool) i then
        (Fin.cons b x : Fin (n + 1) → Bool) i else (Fin.cons a y : Fin (n + 1) → Bool) i) =
      Fin.cons a (fun i => if selected i then x i else y i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  unfold projectionAverage
  rw [expect_cons_internal]
  simp_rw [hm]
  rw [← expect_div, expect_add_distrib]

/--
@isnad1 id=eq.0h5v.s7.c31465146e67 from=translated src=- shape=465f40d5 vocab=8489f3a2
-/
theorem projectionAverage_cons_true_internal {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected x : Fin n → Bool) (b : Bool) :
    projectionAverage f (Fin.cons true selected) (Fin.cons b x) =
      projectionAverage (fun x => f (Fin.cons b x)) selected x := by
  have hm (a : Bool) (y : Fin n → Bool) :
      (fun i : Fin (n + 1) => if (Fin.cons true selected : Fin (n + 1) → Bool) i then
        (Fin.cons b x : Fin (n + 1) → Bool) i else (Fin.cons a y : Fin (n + 1) → Bool) i) =
      Fin.cons b (fun i => if selected i then x i else y i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  unfold projectionAverage
  rw [expect_cons_internal]
  simp_rw [hm]
  ring

/--
@isnad1 id=eq.0h3v.s7.00a216ac1b53 from=translated src=- shape=8be69bf1 vocab=b4e55916
-/
theorem harmonicTransform_cons_false_internal {n : ℕ}
    (f : (Fin (n + 1) → Bool) → ℝ) (selected : Fin n → Bool) :
    harmonicTransform f (Fin.cons false selected) =
      harmonicTransform
        (fun x => (f (Fin.cons false x) + f (Fin.cons true x)) / 2) selected := by
  classical
  unfold harmonicTransform
  rw [← harmonicMean_equiv_internal (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))]
  change harmonicMean (fun x : Bool × (Fin n → Bool) =>
    projectionAverage f (Fin.cons false selected) (Fin.cons x.1 x.2)) = _
  simp_rw [projectionAverage_cons_false_internal]
  simp [harmonicMean, expect_pair_internal]

/--
@isnad1 id=eq.1h3v.s8.9448ea4bb484 from=translated src=- shape=24627c9e vocab=9ae363e2
-/
theorem harmonicTransform_cons_true_internal {n : ℕ}
    {f : (Fin (n + 1) → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (selected : Fin n → Bool) :
    harmonicTransform f (Fin.cons true selected) =
      2 * harmonicTransform (fun x => f (Fin.cons false x)) selected *
        harmonicTransform (fun x => f (Fin.cons true x)) selected /
      (harmonicTransform (fun x => f (Fin.cons false x)) selected +
        harmonicTransform (fun x => f (Fin.cons true x)) selected) := by
  unfold harmonicTransform
  rw [← harmonicMean_equiv_internal (Fin.consEquiv (fun _ : Fin (n + 1) => Bool))]
  change harmonicMean (fun x : Bool × (Fin n → Bool) =>
    projectionAverage f (Fin.cons true selected) (Fin.cons x.1 x.2)) = _
  simp_rw [projectionAverage_cons_true_internal]
  exact harmonicMean_pair_internal fun b =>
    projectionAverage_nonneg_internal (fun x => hf (Fin.cons b x)) selected

/--
@isnad1 id=le.2h4v.s7.a28ef658c528 from=translated src=- shape=15545a89 vocab=7da3482e
-/
theorem harmonicTransform_midpoint_internal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f g : (ι → Bool) → ℝ} (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (selected : ι → Bool) :
    (harmonicTransform f selected + harmonicTransform g selected) / 2 ≤
      harmonicTransform (fun x => (f x + g x) / 2) selected := by
  classical
  have h := harmonicMean_concave_internal (projectionAverage_nonneg_internal hf selected)
    (projectionAverage_nonneg_internal hg selected) (t := 1 / 2) (by norm_num) (by norm_num)
  have he : (fun x => 1 / 2 * projectionAverage f selected x +
      (1 - 1 / 2) * projectionAverage g selected x) =
      projectionAverage (fun x => (f x + g x) / 2) selected := by
    funext x
    rw [projectionAverage_midpoint_internal]
    ring
  rw [he] at h
  dsimp [harmonicTransform]
  linarith

end Complexity.BooleanAnalysis
