/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Haar measure on finite-dimensional `p`-adic vector spaces: the modulus of `p` (taxis #4)

Mathlib provides Haar measures on locally compact groups but no computation of the
modulus of scaling by `p` on `ℚ_p`. We prove:

* `Iut.LocalConstruct.measure_preimage_mul_padic`: for an additive Haar measure `μ` on
  `ℚ_p` and a measurable set `s`, `μ (p⁻¹·s) = p · μ s` — from the decomposition of the
  ball of radius `p` into `p` translates of `ℤ_p`;
* `Iut.LocalConstruct.measure_preimage_smul_padic`: for an additive Haar measure `μ` on a
  finite-dimensional `ℚ_p`-vector space `E` of dimension `n`, `μ (p⁻¹·s) = p^n · μ s` —
  by transport to `ℚ_p^n` and the product measure.

Here `p⁻¹·s` denotes the preimage `{x | p • x ∈ s}`. These are the inputs of the
normalization `μ^log(p⁻¹·U) = μ^log(U) + log p` of the log-volume (IUT III,
Proposition 3.9(i)).

`ℚ_p` receives its Borel σ-algebra as an instance here.
-/

namespace Iut

namespace LocalConstruct

open MeasureTheory

variable (p : ℕ) [Fact p.Prime]

noncomputable instance : MeasurableSpace ℚ_[p] := borel _

instance : BorelSpace ℚ_[p] := ⟨rfl⟩

lemma padic_natCast_ne_zero : ((p : ℕ) : ℚ_[p]) ≠ 0 := by
  exact_mod_cast (Fact.out : p.Prime).ne_zero

/-- Multiplication by `p` on `ℚ_p`, as a continuous linear automorphism. -/
noncomputable def mulPadic : ℚ_[p] ≃L[ℚ_[p]] ℚ_[p] :=
  (LinearEquiv.smulOfNeZero ℚ_[p] ℚ_[p] (p : ℚ_[p])
    (padic_natCast_ne_zero p)).toContinuousLinearEquiv

lemma mulPadic_apply (x : ℚ_[p]) : mulPadic p x = (p : ℚ_[p]) * x := rfl

/-! ### The ball of radius `p` as a union of `p` translates of `ℤ_p` -/

/-- The translate of the unit ball by `i / p`. -/
noncomputable def padicCoset (i : Fin p) : Set ℚ_[p] :=
  (fun x => -(((i : ℕ) : ℚ_[p]) / p) + x) ⁻¹' Metric.closedBall 0 1

lemma mem_padicCoset {i : Fin p} {x : ℚ_[p]} :
    x ∈ padicCoset p i ↔ ‖x - ((i : ℕ) : ℚ_[p]) / p‖ ≤ 1 := by
  simp only [padicCoset, Set.mem_preimage, Metric.mem_closedBall, dist_zero_right, neg_add_eq_sub]

lemma measurableSet_padicCoset (i : Fin p) : MeasurableSet (padicCoset p i) :=
  measurableSet_closedBall.preimage (by fun_prop)

lemma norm_sub_le_max' {x y : ℚ_[p]} : ‖x - y‖ ≤ max ‖x‖ ‖y‖ := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_eq (by rw [norm_neg])

lemma pairwise_disjoint_padicCoset :
    Pairwise fun i j : Fin p => Disjoint (padicCoset p i) (padicCoset p j) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hxi hxj
  rw [mem_padicCoset] at hxi hxj
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hpq := padic_natCast_ne_zero p
  set d : ℤ := ((i : ℕ) : ℤ) - ((j : ℕ) : ℤ) with hd
  have h1 : ‖(d : ℚ_[p]) / p‖ ≤ 1 := by
    have : (d : ℚ_[p]) / p = (x - ((j : ℕ) : ℚ_[p]) / p) - (x - ((i : ℕ) : ℚ_[p]) / p) := by
      rw [hd]
      push_cast
      ring
    rw [this]
    exact (norm_sub_le_max' p).trans (max_le hxj hxi)
  have h2 : ‖(d : ℚ_[p])‖ < 1 := by
    rw [norm_div, Padic.norm_p, div_inv_eq_mul] at h1
    have hinv : (p : ℝ)⁻¹ < 1 :=
      inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    calc ‖(d : ℚ_[p])‖ = ‖(d : ℚ_[p])‖ * p * (p : ℝ)⁻¹ := (mul_inv_cancel_right₀ hp0.ne' _).symm
      _ ≤ 1 * (p : ℝ)⁻¹ := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ < 1 := by rwa [one_mul]
  rw [Padic.norm_intCast_lt_one_iff] at h2
  have h3 : d = 0 := by
    refine Int.eq_zero_of_abs_lt_dvd h2 ?_
    rw [hd, abs_lt]
    constructor <;> omega
  exact hij (Fin.ext (by omega))

/-! ### The modulus of `p` on `ℚ_p` -/

variable {p}

/-! ### The modulus of `p` on a finite-dimensional `ℚ_p`-vector space -/

section FiniteDimensional

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℚ_[p] E] [FiniteDimensional ℚ_[p] E]
  [MeasurableSpace E] [BorelSpace E]

end FiniteDimensional

end LocalConstruct

end Iut
