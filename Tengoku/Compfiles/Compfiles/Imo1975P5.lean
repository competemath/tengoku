/-
Copyright (c) 2026 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Constantin Seebach
-/

module

public import Tengoku

@[expose] public section

/-!
# International Mathematical Olympiad 1975, Problem 5

Determine, with proof, whether or not one can find $1975$ points on the circumference of a circle
with unit radius such that the distance between any two of them is a rational number.
-/

namespace Imo1975P5

abbrev constructible : Bool := true

/--
@isnad1 id=not.2h2v.s4.fd5da59035bf from=translated src=- shape=fb78f282 vocab=fb9c6578
-/
theorem not_irrational_add {b c : ℝ}: ¬Irrational b → ¬Irrational c → ¬Irrational (b + c) := by
  intro h1 h2
  apply not_imp_not.mpr (Irrational.add_cases)
  apply not_or_intro h1 h2

/--
@isnad1 id=not.2h2v.s4.f1d32294e672 from=translated src=- shape=fb78f282 vocab=b8aa46b5
-/
theorem not_irrational_sub {b c : ℝ} : ¬Irrational b → ¬Irrational c → ¬Irrational (b - c) := by
  intro h1 h2
  apply not_imp_not.mpr (Irrational.add_cases)
  apply not_or_intro h1 _
  rw [irrational_neg_iff]
  exact h2

/--
@isnad1 id=not.2h2v.s4.9b5d37501142 from=translated src=- shape=fb78f282 vocab=433bfd8f
-/
theorem not_irrational_mul {b c : ℝ} : ¬Irrational b → ¬Irrational c → ¬Irrational (b * c) := by
  intro h1 h2
  apply not_imp_not.mpr (Irrational.mul_cases)
  apply not_or_intro h1 h2

/--
@isnad1 id=iff.0h1v.s3.07f07e2e1ad6 from=translated src=- shape=f58cbc93 vocab=70b18ea2
-/
theorem irrational_abs_iff {x : ℝ} : Irrational |x| ↔ Irrational x := by
  apply abs_by_cases (fun y => Irrational y ↔ Irrational x) Iff.rfl
  exact irrational_neg_iff

noncomputable def θ : ℝ := Real.arccos (4/5)

/--
@isnad1 id=eq.0h0v.s4.402486ec0093 from=translated src=- shape=96f2ca54 vocab=6d3cbe0f
-/
theorem sin_θ : Real.sin θ = (3/5:ℚ) := by
  unfold θ
  rw [Real.sin_arccos]
  field

/--
@isnad1 id=eq.0h0v.s4.f50fcfae4848 from=translated src=- shape=96f2ca54 vocab=81b55c7b
-/
theorem cos_θ : Real.cos θ = (4/5:ℚ) := by
  unfold θ
  rw [Real.cos_arccos] <;> linarith

noncomputable def P (n : ℕ) : Circle := Circle.exp (θ * n * 2)

/--
@isnad1 id=eq.0h1v.s7.b7200e787411 from=translated src=- shape=58e54e19 vocab=3369c926
-/
lemma P_cast_eq {n : ℕ} : (P n : ℂ) = ⟨Real.cos (θ*2*n), Real.sin (θ*2*n)⟩ := by
  rw [P, Circle.coe_exp, Complex.ext_iff]
  simp [Complex.exp_re, Complex.exp_im]
  ring_nf
  trivial

/--
@isnad1 id=and.0h1v.s5.c9cb5efa14b9 from=translated src=- shape=01c8d1e2 vocab=f7235055
-/
theorem not_irrational_sin_θ_mul_and_not_irrational_cos_θ_mul (n : ℕ)
    : ¬ Irrational (Real.sin (θ*n)) ∧ ¬ Irrational (Real.cos (θ*n)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_add, mul_add, Real.sin_add, Real.cos_add]
    grind only [= cos_θ, = sin_θ, Rat.not_irrational, not_irrational_mul, not_irrational_add, not_irrational_sub]

/--
@isnad1 id=eq.0h2v.s7.d0e8d13d51b9 from=translated src=- shape=aa97e1e0 vocab=5f5ac4c4
-/
lemma Circle.dist_eq (x y : Circle) : dist x y = dist (x : ℂ) y := rfl

/--
@isnad1 id=not.0h2v.s4.c90201b98322 from=translated src=- shape=76505b4b vocab=a2244601
-/
theorem not_irrational_dist_P_P (i j : ℕ) : ¬ Irrational (dist (P i) (P j)) := by
  simp_rw [Circle.dist_eq, P_cast_eq]
  rw [Complex.dist_mk, Real.cos_sub_cos, Real.sin_sub_sin, mul_right_comm]
  repeat rw [mul_pow]
  simp only [even_two, Even.neg_pow]
  rw [← mul_add]
  simp only [Real.sin_sq_add_cos_sq, mul_one, Nat.ofNat_nonneg, pow_succ_nonneg, Real.sqrt_mul,
    Real.sqrt_sq]
  rw [Real.sqrt_sq_eq_abs]
  apply not_irrational_mul (not_irrational_ofNat _)
  rw [irrational_abs_iff, mul_right_comm _ 2 _, mul_right_comm _ 2 _, ← sub_mul, mul_div_cancel_right₀ _ (by simp), Real.sin_sub]
  apply not_irrational_sub <;> apply not_irrational_mul <;> simp [not_irrational_sin_θ_mul_and_not_irrational_cos_θ_mul]

/--
@isnad1 id=ne.1h1v.s5.e26b8adc4813 from=translated src=- shape=2420ddcb vocab=e7fcf38a
-/
theorem sin_mul_θ_ne_zero (n : ℕ) (hz : 1 ≤ n) : Real.sin (n * θ) ≠ 0 := by
  by_contra
  have := @niven_sin θ ?_ ?_
  · rw [sin_θ] at this
    simp at this
    grind only
  · rw [Real.sin_eq_zero_iff] at this
    let ⟨z, h⟩ := this
    use z/n
    rify
    have : 0 < (n:ℝ) := by
      rw [Nat.cast_pos]
      exact Nat.zero_lt_of_lt hz
    grind only
  · rw [sin_θ]
    use ?_

/--
@isnad1 id=injectiv.0h0v.s2.af4dadeeb7b8 from=translated src=- shape=54c8eceb vocab=e2010e2e
-/
theorem P_injective : Function.Injective P := by
  intro i j e
  contrapose! e
  wlog w : j < i
  · rw [ne_comm]
    have := this e.symm
    grind only
  simp_rw [Ne, Circle.ext_iff, P_cast_eq]
  simp only [Complex.mk.injEq, not_and]
  intro _
  suffices Real.sin (θ*2*(i-j)) ≠ 0 by
    grind only [mul_sub, Real.sin_sub]
  rw [mul_assoc, mul_comm]
  rw [show (2 * (i - j) : ℝ) = (2 * (i-j) : ℕ) by rw [Nat.cast_mul, Nat.cast_sub] <;> lia]
  apply sin_mul_θ_ne_zero
  lia

end Imo1975P5
