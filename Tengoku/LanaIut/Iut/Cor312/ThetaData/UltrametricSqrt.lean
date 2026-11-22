/-
Copyright (c) 2026 The iut contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The iut contributors
-/
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Square roots in complete ultrametric fields (Hensel's lemma, Babylonian form)

Let `k` be a complete non-archimedean normed field in which `‖2‖ = 1` (residue characteristic
different from `2`). If `x₀` is a unit (`‖x₀‖ = 1`) with `‖x₀ ^ 2 - a‖ < 1`, then `a` has a
square root `x` in `k` with `‖x - x₀‖ < 1`: this is Hensel's lemma for the polynomial
`X ^ 2 - a`, proved here directly by the Babylonian (Newton) iteration

`x (n + 1) = (x n + a / x n) / 2`,

which stays on the unit sphere and satisfies the exact identity

`(x (n + 1)) ^ 2 - a = ((x n) ^ 2 - a) ^ 2 / (4 * (x n) ^ 2)`,

so that `‖(x (n + 1)) ^ 2 - a‖ = ‖(x n) ^ 2 - a‖ ^ 2`. Consequently the defects
`‖(x n) ^ 2 - a‖` are bounded by `ε ^ (n + 1)` with `ε := ‖x₀ ^ 2 - a‖ < 1`, the increments
`x (n + 1) - x n = (a - (x n) ^ 2) / (2 * x n)` have the same norm as the defects, the sequence is
Cauchy, and its limit is the required square root.

## Main results

* `Iut.babylonianSqrt`: the iteration.
* `Iut.exists_sq_eq_of_norm_sq_sub_lt`: Hensel's lemma for square roots, with the bound
  `‖x - x₀‖ < 1` on the root.
* `Iut.exists_sq_eq_of_norm_sub_one_lt`: every `a` with `‖a - 1‖ < 1` is a square.
-/

open Filter Topology

namespace Iut

variable {k : Type*} [NormedField k]

/-- The Babylonian (Newton) iteration for a square root of `a`, started at `x₀`:
`x 0 = x₀` and `x (n + 1) = (x n + a / x n) / 2`. -/
noncomputable def babylonianSqrt (a x₀ : k) : ℕ → k
  | 0 => x₀
  | n + 1 => (babylonianSqrt a x₀ n + a / babylonianSqrt a x₀ n) / 2

/--
@isnad1 id=eq.0h3v.s4.f361718bb0fe from=translated src=- shape=3b0788dd vocab=a0790778
-/
@[simp]
theorem babylonianSqrt_zero (a x₀ : k) : babylonianSqrt a x₀ 0 = x₀ := rfl

/--
@isnad1 id=eq.0h4v.s6.dd2f2d0df777 from=translated src=- shape=5129d575 vocab=f30e3959
-/
theorem babylonianSqrt_succ (a x₀ : k) (n : ℕ) :
    babylonianSqrt a x₀ (n + 1) = (babylonianSqrt a x₀ n + a / babylonianSqrt a x₀ n) / 2 := rfl

/-- The exact one-step identity for the defect of the Babylonian iteration.
@isnad1 id=eq.2h3v.s8.ec2b9912e9f4 from=translated src=- shape=fa12d303 vocab=f015b3c1
-/
theorem babylonian_step_sq_sub (a x : k) (hx : x ≠ 0) (h2 : (2 : k) ≠ 0) :
    ((x + a / x) / 2) ^ 2 - a = (x ^ 2 - a) ^ 2 / (4 * x ^ 2) := by
  have h4 : (4 : k) ≠ 0 := by
    have : (4 : k) = 2 * 2 := by norm_num
    rw [this]
    exact mul_ne_zero h2 h2
  field_simp
  ring

/-- The exact one-step identity for the increment of the Babylonian iteration.
@isnad1 id=eq.2h3v.s8.c6327db0b54c from=translated src=- shape=911eefb4 vocab=f015b3c1
-/
theorem babylonian_step_sub (a x : k) (hx : x ≠ 0) (h2 : (2 : k) ≠ 0) :
    (x + a / x) / 2 - x = (a - x ^ 2) / (2 * x) := by
  field_simp
  ring

section Norms

variable (h2 : ‖(2 : k)‖ = 1)
include h2

/--
@isnad1 id=eq.1h1v.s6.92b8c0536a66 from=translated src=- shape=4b448813 vocab=759622ca
-/
theorem norm_four_eq_one : ‖(4 : k)‖ = 1 := by
  have : (4 : k) = 2 * 2 := by norm_num
  rw [this, norm_mul, h2, one_mul]

/--
@isnad1 id=ne.1h1v.s6.397c17c764db from=translated src=- shape=f741e352 vocab=759622ca
-/
theorem two_ne_zero_of_norm_two_eq_one : (2 : k) ≠ 0 := by
  intro h
  rw [h, norm_zero] at h2
  exact zero_ne_one h2

/-- One step of the Babylonian iteration squares the defect (in norm).
@isnad1 id=eq.2h3v.s8.986602c4b0ae from=translated src=- shape=2c7c7aac vocab=bf413cd6
-/
theorem norm_babylonian_step_sq_sub (a : k) {x : k} (hx : ‖x‖ = 1) :
    ‖((x + a / x) / 2) ^ 2 - a‖ = ‖x ^ 2 - a‖ ^ 2 := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact zero_ne_one hx
  rw [babylonian_step_sq_sub a x hx0 (two_ne_zero_of_norm_two_eq_one h2), norm_div, norm_pow,
    norm_mul, norm_four_eq_one h2, norm_pow, hx, one_pow, one_mul, div_one]

/-- One step of the Babylonian iteration moves by exactly the norm of the defect.
@isnad1 id=eq.2h3v.s7.bd294d37f50c from=translated src=- shape=f57bae61 vocab=bf413cd6
-/
theorem norm_babylonian_step_sub (a : k) {x : k} (hx : ‖x‖ = 1) :
    ‖(x + a / x) / 2 - x‖ = ‖x ^ 2 - a‖ := by
  have hx0 : x ≠ 0 := by
    intro h
    rw [h, norm_zero] at hx
    exact zero_ne_one hx
  rw [babylonian_step_sub a x hx0 (two_ne_zero_of_norm_two_eq_one h2), norm_div, norm_mul, h2, hx,
    one_mul, div_one, norm_sub_rev]

variable [IsUltrametricDist k]

omit h2 in
/-- In an ultrametric normed field, a perturbation of a unit by an element of norm `< 1` is
again a unit.
@isnad1 id=eq.2h3v.s6.e9258703cd85 from=translated src=- shape=098ded44 vocab=cf069cc3
-/
theorem norm_eq_one_of_norm_sub_lt_one {x y : k} (hx : ‖x‖ = 1) (h : ‖y - x‖ < 1) : ‖y‖ = 1 := by
  have hy : y = x + (y - x) := by ring
  have hne : ‖x‖ ≠ ‖y - x‖ := by
    rw [hx]
    exact h.ne'
  rw [hy, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm hne, hx, max_eq_left h.le]

/-- Along the Babylonian iteration started at a unit `x₀` with `‖x₀ ^ 2 - a‖ < 1`, every term
is a unit and the defect at stage `n` is at most `‖x₀ ^ 2 - a‖ ^ (n + 1)`.
@isnad1 id=and.3h4v.s8.7b43ef8d03f6 from=translated src=- shape=20665d35 vocab=c7a7eca3
-/
theorem babylonianSqrt_norm_eq_one_and_norm_sq_sub_le {a x₀ : k} (hx₀ : ‖x₀‖ = 1)
    (h : ‖x₀ ^ 2 - a‖ < 1) (n : ℕ) :
    ‖babylonianSqrt a x₀ n‖ = 1 ∧
      ‖babylonianSqrt a x₀ n ^ 2 - a‖ ≤ ‖x₀ ^ 2 - a‖ ^ (n + 1) := by
  set ε := ‖x₀ ^ 2 - a‖ with hε
  have hε0 : 0 ≤ ε := norm_nonneg _
  have hε1 : ε ≤ 1 := h.le
  induction n with
  | zero =>
    refine ⟨hx₀, ?_⟩
    simp [hε]
  | succ n ih =>
    obtain ⟨hn, hb⟩ := ih
    have hstep : ‖babylonianSqrt a x₀ (n + 1) ^ 2 - a‖ = ‖babylonianSqrt a x₀ n ^ 2 - a‖ ^ 2 := by
      rw [babylonianSqrt_succ]
      exact norm_babylonian_step_sq_sub h2 a hn
    have hinc : ‖babylonianSqrt a x₀ (n + 1) - babylonianSqrt a x₀ n‖ =
        ‖babylonianSqrt a x₀ n ^ 2 - a‖ := by
      rw [babylonianSqrt_succ]
      exact norm_babylonian_step_sub h2 a hn
    have hlt : ‖babylonianSqrt a x₀ (n + 1) - babylonianSqrt a x₀ n‖ < 1 := by
      rw [hinc]
      calc ‖babylonianSqrt a x₀ n ^ 2 - a‖ ≤ ε ^ (n + 1) := hb
        _ < 1 := pow_lt_one₀ hε0 h n.succ_ne_zero
    refine ⟨norm_eq_one_of_norm_sub_lt_one hn hlt, ?_⟩
    calc ‖babylonianSqrt a x₀ (n + 1) ^ 2 - a‖
        = ‖babylonianSqrt a x₀ n ^ 2 - a‖ ^ 2 := hstep
      _ ≤ (ε ^ (n + 1)) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = ε ^ (2 * (n + 1)) := by rw [← pow_mul, mul_comm]
      _ ≤ ε ^ (n + 1 + 1) := pow_le_pow_of_le_one hε0 hε1 (by omega)

/-- Along the Babylonian iteration, every term stays within `‖x₀ ^ 2 - a‖` of `x₀`.
@isnad1 id=le.3h4v.s7.07fee15bd1e6 from=translated src=- shape=e1c06870 vocab=1b7cac01
-/
theorem norm_babylonianSqrt_sub_le {a x₀ : k} (hx₀ : ‖x₀‖ = 1) (h : ‖x₀ ^ 2 - a‖ < 1) (n : ℕ) :
    ‖babylonianSqrt a x₀ n - x₀‖ ≤ ‖x₀ ^ 2 - a‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    obtain ⟨hn, hb⟩ := babylonianSqrt_norm_eq_one_and_norm_sq_sub_le h2 hx₀ h n
    have hinc : ‖babylonianSqrt a x₀ (n + 1) - babylonianSqrt a x₀ n‖ ≤ ‖x₀ ^ 2 - a‖ := by
      rw [babylonianSqrt_succ, norm_babylonian_step_sub h2 a hn]
      calc ‖babylonianSqrt a x₀ n ^ 2 - a‖ ≤ ‖x₀ ^ 2 - a‖ ^ (n + 1) := hb
        _ ≤ ‖x₀ ^ 2 - a‖ := pow_le_of_le_one (norm_nonneg _) h.le n.succ_ne_zero
    have hsplit : babylonianSqrt a x₀ (n + 1) - x₀ =
        (babylonianSqrt a x₀ (n + 1) - babylonianSqrt a x₀ n) + (babylonianSqrt a x₀ n - x₀) := by
      ring
    rw [hsplit]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hinc ih)

end Norms

variable [IsUltrametricDist k] [CompleteSpace k]

/-- **Hensel's lemma for square roots** in a complete ultrametric field with `‖2‖ = 1`: an
approximate square root `x₀` of `a` on the unit sphere with `‖x₀ ^ 2 - a‖ < 1` refines to an
exact square root `x` with `‖x - x₀‖ < 1`.
@isnad1 id=ex.3h3v.s7.07ff0a575c81 from=translated src=- shape=eda0bf1c vocab=f70242f5
-/
theorem exists_sq_eq_of_norm_sq_sub_lt (h2 : ‖(2 : k)‖ = 1) {a x₀ : k} (hx₀ : ‖x₀‖ = 1)
    (h : ‖x₀ ^ 2 - a‖ < 1) : ∃ x : k, x ^ 2 = a ∧ ‖x - x₀‖ < 1 := by
  set ε := ‖x₀ ^ 2 - a‖ with hε
  have hε0 : 0 ≤ ε := norm_nonneg _
  set u : ℕ → k := babylonianSqrt a x₀ with hu
  have hbound : ∀ n, ‖u n ^ 2 - a‖ ≤ ε ^ (n + 1) := fun n =>
    (babylonianSqrt_norm_eq_one_and_norm_sq_sub_le h2 hx₀ h n).2
  have hunit : ∀ n, ‖u n‖ = 1 := fun n =>
    (babylonianSqrt_norm_eq_one_and_norm_sq_sub_le h2 hx₀ h n).1
  -- the sequence is Cauchy
  have hdist : ∀ n, dist (u n) (u (n + 1)) ≤ ε * ε ^ n := by
    intro n
    rw [dist_eq_norm, norm_sub_rev, hu, babylonianSqrt_succ, norm_babylonian_step_sub h2 a (hunit n),
      ← pow_succ']
    exact hbound n
  have hcauchy : CauchySeq u := cauchySeq_of_le_geometric ε ε h hdist
  obtain ⟨x, hx⟩ := cauchySeq_tendsto_of_complete hcauchy
  refine ⟨x, ?_, ?_⟩
  · -- the limit is a square root of `a`
    have h1 : Tendsto (fun n => u n ^ 2 - a) atTop (𝓝 (x ^ 2 - a)) := (hx.pow 2).sub_const a
    have hpow : Tendsto (fun n : ℕ => ε ^ (n + 1)) atTop (𝓝 0) :=
      (tendsto_pow_atTop_nhds_zero_of_lt_one hε0 h).comp (tendsto_add_atTop_nat 1)
    have h0 : Tendsto (fun n => u n ^ 2 - a) atTop (𝓝 0) :=
      squeeze_zero_norm hbound hpow
    exact sub_eq_zero.mp (tendsto_nhds_unique h1 h0)
  · -- the limit stays within `ε < 1` of `x₀`
    have hlim : Tendsto (fun n => ‖u n - x₀‖) atTop (𝓝 ‖x - x₀‖) := (hx.sub_const x₀).norm
    have hle : ‖x - x₀‖ ≤ ε :=
      le_of_tendsto' hlim fun n => norm_babylonianSqrt_sub_le h2 hx₀ h n
    exact hle.trans_lt h

/-- In a complete ultrametric field with `‖2‖ = 1`, every element of the open unit ball around
`1` is a square.
@isnad1 id=ex.2h2v.s7.3615f873637b from=translated src=- shape=9b169e62 vocab=f70242f5
-/
theorem exists_sq_eq_of_norm_sub_one_lt (h2 : ‖(2 : k)‖ = 1) {a : k} (ha : ‖a - 1‖ < 1) :
    ∃ x : k, x ^ 2 = a := by
  have h : ‖(1 : k) ^ 2 - a‖ < 1 := by
    rw [one_pow, norm_sub_rev]
    exact ha
  obtain ⟨x, hx, -⟩ := exists_sq_eq_of_norm_sq_sub_lt h2 norm_one h
  exact ⟨x, hx⟩

end Iut
