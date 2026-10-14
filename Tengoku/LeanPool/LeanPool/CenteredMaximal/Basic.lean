/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.LeanPool.LeanPool.CenteredMaximal.Statement

/-!
# Basic API for the centred maximal function and its weak type constant

* `le_maximalFunction`: every cube average is at most the maximal function;
* `exists_lt_average_of_lt_maximalFunction`: a level below the maximal function is exceeded by
  some cube average;
* `volume_closedBall_eq`: the cube of radius `r` has volume `(2r)ᵈ`;
* `weakTypeConstant_le`, `le_weakTypeConstant`: the constant is the least weak type bound.
-/

@[expose] public section

noncomputable section

open MeasureTheory Metric
open scoped ENNReal

namespace LeanPool.CenteredMaximal

variable {d : ℕ}

/-- Every cube average is at most the maximal function.
@isnad1 id=le.1h4v.s8.dfa837a02fb1 from=translated src=- shape=435a89a5 vocab=312fd215
-/
theorem le_maximalFunction (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) {r : ℝ} (hr : 0 < r) :
    (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ ≤ maximalFunction f x :=
  le_iSup₂ (f := fun r (_ : 0 < r) =>
    (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ) r hr

/-- A level strictly below the maximal function is exceeded by some cube average.
@isnad1 id=ex.1h4v.s8.e217cd78691d from=translated src=- shape=75cf9bd2 vocab=d6575709
-/
theorem exists_lt_average_of_lt_maximalFunction {f : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    {α : ℝ≥0∞} (h : α < maximalFunction f x) :
    ∃ r, 0 < r ∧ α < (volume (closedBall x r))⁻¹ * ∫⁻ y in closedBall x r, ‖f y‖ₑ := by
  obtain ⟨r, hr⟩ := lt_iSup_iff.1 h
  obtain ⟨hr₀, hr⟩ := lt_iSup_iff.1 hr
  exact ⟨r, hr₀, hr⟩

/-- The closed cube of radius `r` (side `2r`) in `ℝᵈ` has volume `(2r)ᵈ`.
@isnad1 id=eq.1h3v.s7.e32e37d222d5 from=translated src=- shape=aeadb8bc vocab=c9766e1b
-/
theorem volume_closedBall_eq (x : Fin d → ℝ) {r : ℝ} (hr : 0 ≤ r) :
    volume (closedBall x r) = ENNReal.ofReal ((2 * r) ^ d) := by
  simpa using Real.volume_pi_closedBall x hr

/-- A weak type bound stays a weak type bound when it is increased.
@isnad1 id=isweakty.2h3v.s4.dfd19cfb0a73 from=translated src=- shape=85d87de9 vocab=00e9de4f
-/
theorem IsWeakTypeBound.mono {C C' : ℝ≥0∞} (h : IsWeakTypeBound d C) (hCC' : C ≤ C') :
    IsWeakTypeBound d C' :=
  fun f hf α => (h f hf α).trans (mul_le_mul_left hCC' _)

/-- The weak type constant is at most every weak type bound.
@isnad1 id=le.1h2v.s3.e03d16c9fbde from=translated src=- shape=1f8c27ae vocab=080ca538
-/
theorem weakTypeConstant_le {C : ℝ≥0∞} (h : IsWeakTypeBound d C) : weakTypeConstant d ≤ C :=
  sInf_le h

/-- A lower bound for every weak type bound is a lower bound for the weak type constant.
@isnad1 id=le.1h2v.s4.d8e131620462 from=translated src=- shape=f0505e42 vocab=080ca538
-/
theorem le_weakTypeConstant {c : ℝ≥0∞} (h : ∀ C, IsWeakTypeBound d C → c ≤ C) :
    c ≤ weakTypeConstant d :=
  le_sInf h

end LeanPool.CenteredMaximal
