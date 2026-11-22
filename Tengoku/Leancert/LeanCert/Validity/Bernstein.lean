/-
Copyright (c) 2026 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.Engine.Algebra.QPolyBernstein
import Tengoku.Leancert.LeanCert.Engine.Algebra.QPolyIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Golden theorems for Bernstein polynomial certificates

`checkPolyLowerBound e I c depth` recognises `e` as a univariate rational
polynomial (`QPoly.ofExpr`) and runs the recursive Bernstein certificate
`QPoly.bernsteinCheck`. Recognition doubles as the support proof, so the golden
theorems need no `ExprSupportedCore` premise. All theorems here are kernel-clean;
the checker itself may be closed by kernel or native evaluation.
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.Validity.Bernstein

open LeanCert.Core LeanCert.Engine

/-- Generic Bernstein checker over reified expressions. -/
def checkPolyBound (cmp : QPoly.Cmp) (e : Expr) (I : IntervalRat) (c : ℚ)
    (depth : Nat) : Bool :=
  match QPoly.ofExpr e with
  | some p => QPoly.bernsteinCheck cmp p c I depth
  | none => false

/-- `∀ x ∈ I, c ≤ e x` by Bernstein coefficients. -/
def checkPolyLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat) : Bool :=
  checkPolyBound .lower e I c depth

/-- `∀ x ∈ I, e x ≤ c` by Bernstein coefficients. -/
def checkPolyUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat) : Bool :=
  checkPolyBound .upper e I c depth

/-- `∀ x ∈ I, c < e x` by Bernstein coefficients. -/
def checkPolyStrictLowerBound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat) : Bool :=
  checkPolyBound .strictLower e I c depth

/-- `∀ x ∈ I, e x < c` by Bernstein coefficients. -/
def checkPolyStrictUpperBound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat) : Bool :=
  checkPolyBound .strictUpper e I c depth

/-- Does `QPoly.ofExpr` recognise `e`? Used by tactics to decide applicability
without spending budget. -/
def isPolynomial (e : Expr) : Bool :=
  (QPoly.ofExpr e).isSome

/--
@isnad1 id=holds.2h6v.s5.cb396f891c0f from=translated src=- shape=54ea711f vocab=6b4535fb
-/
theorem verify_poly_bound (cmp : QPoly.Cmp) (e : Expr) (I : IntervalRat) (c : ℚ)
    (depth : Nat) (h : checkPolyBound cmp e I c depth = true) :
    ∀ x ∈ I, cmp.holds c (Expr.eval (fun _ => x) e) := by
  unfold checkPolyBound at h
  cases hpoly : QPoly.ofExpr e with
  | none => simp [hpoly] at h
  | some p =>
      rw [hpoly] at h
      intro x hx
      rw [QPoly.ofExpr_correct hpoly, QPoly.eval_toExpr]
      exact QPoly.bernsteinCheck_sound h x hx

/-- **Golden theorem (lower bound).**
@isnad1 id=le.2h5v.s5.4d1cdd449290 from=translated src=- shape=9916005b vocab=1647e1b0
-/
theorem verify_poly_lower_bound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat)
    (h : checkPolyLowerBound e I c depth = true) :
    ∀ x ∈ I, (c : ℝ) ≤ Expr.eval (fun _ => x) e :=
  verify_poly_bound .lower e I c depth h

/-- **Golden theorem (upper bound).**
@isnad1 id=le.2h5v.s5.aeec90694887 from=translated src=- shape=ac35e364 vocab=a2a58c3d
-/
theorem verify_poly_upper_bound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat)
    (h : checkPolyUpperBound e I c depth = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e ≤ (c : ℝ) :=
  verify_poly_bound .upper e I c depth h

/-- **Golden theorem (strict lower bound).**
@isnad1 id=lt.2h5v.s5.9dbbff47be07 from=translated src=- shape=9916005b vocab=0c45b87c
-/
theorem verify_poly_strict_lower_bound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat)
    (h : checkPolyStrictLowerBound e I c depth = true) :
    ∀ x ∈ I, (c : ℝ) < Expr.eval (fun _ => x) e :=
  verify_poly_bound .strictLower e I c depth h

/-- **Golden theorem (strict upper bound).**
@isnad1 id=lt.2h5v.s5.3394feb24098 from=translated src=- shape=ac35e364 vocab=9d9e15d0
-/
theorem verify_poly_strict_upper_bound (e : Expr) (I : IntervalRat) (c : ℚ) (depth : Nat)
    (h : checkPolyStrictUpperBound e I c depth = true) :
    ∀ x ∈ I, Expr.eval (fun _ => x) e < (c : ℝ) :=
  verify_poly_bound .strictUpper e I c depth h

/-! ### `Set.Icc` bridges -/

/--
@isnad1 id=le.3h6v.s5.f966d7d5ea0b from=translated src=- shape=575addb2 vocab=b4b1f17d
-/
theorem verify_poly_lower_bound_Icc (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (depth : Nat) (h : checkPolyLowerBound e ⟨lo, hi, hle⟩ c depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, (c : ℝ) ≤ Expr.eval (fun _ => x) e := by
  intro x hx
  exact verify_poly_lower_bound e ⟨lo, hi, hle⟩ c depth h x
    ((IntervalRat.mem_iff_mem_Icc x _).mpr hx)

/--
@isnad1 id=le.3h6v.s5.5d9b3d165cda from=translated src=- shape=2760c1dd vocab=1c853596
-/
theorem verify_poly_upper_bound_Icc (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (depth : Nat) (h : checkPolyUpperBound e ⟨lo, hi, hle⟩ c depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e ≤ (c : ℝ) := by
  intro x hx
  exact verify_poly_upper_bound e ⟨lo, hi, hle⟩ c depth h x
    ((IntervalRat.mem_iff_mem_Icc x _).mpr hx)

/--
@isnad1 id=lt.3h6v.s5.1f2c32a0eecb from=translated src=- shape=9b9cd82a vocab=0668440d
-/
theorem verify_poly_strict_lower_bound_Icc (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (depth : Nat) (h : checkPolyStrictLowerBound e ⟨lo, hi, hle⟩ c depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, (c : ℝ) < Expr.eval (fun _ => x) e := by
  intro x hx
  exact verify_poly_strict_lower_bound e ⟨lo, hi, hle⟩ c depth h x
    ((IntervalRat.mem_iff_mem_Icc x _).mpr hx)

/--
@isnad1 id=lt.3h6v.s5.f8df3de4b65a from=translated src=- shape=7389e67f vocab=f65df18d
-/
theorem verify_poly_strict_upper_bound_Icc (e : Expr) (lo hi : ℚ) (hle : lo ≤ hi) (c : ℚ)
    (depth : Nat) (h : checkPolyStrictUpperBound e ⟨lo, hi, hle⟩ c depth = true) :
    ∀ x ∈ Set.Icc (lo : ℝ) hi, Expr.eval (fun _ => x) e < (c : ℝ) := by
  intro x hx
  exact verify_poly_strict_upper_bound e ⟨lo, hi, hle⟩ c depth h x
    ((IntervalRat.mem_iff_mem_Icc x _).mpr hx)

end LeanCert.Validity.Bernstein
