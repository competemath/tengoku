/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.Holonomic
import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial
import Tengoku.Seed.Analysis.Calculus.Deriv.Shift
import Tengoku.Seed.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Tengoku.Seed.Data.Matrix.Mul
import Tengoku.Seed.RingTheory.PowerSeries.Derivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.9.2: Theorem 4.2 (the bit-burst algorithm)

**Theorem 4.2.** If `f` is holonomic with no singularity on `[A, B] ∋ 0` and `f(0) = 0`, then
`f(x)` can be computed to `n` bits for any `n`-bit `x ∈ (A, B)` in time `O(M(n) log³ n)`.

The proof: for `0 ≤ x < 1` write `x = r₁ + ⋯ + r_k` with `r₁` the first bit, `r₂` the next two,
`r₃` the next four, … (`2^(k−1) ≤ n < 2^k`); `x_i = r₁ + ⋯ + r_i`, `f_i(t) = f(x_i + t)`,
`f_i^*(t) = f_i(t) − f_i(0)`, so `f(x) = ∑_{i<k} f_i^*(r_{i+1})` by telescoping; each `r_{i+1}` has
a numerator of at most `2^i` bits and `0 ≤ r_{i+1} < 2^(1−2^i)`, so `n/2^i + O(log n)` Taylor terms
of `f_i^*` suffice; `f_i` satisfies the translated ODE `∑ c_j(x_i + t) f_i^{(j)}(t) = 0` (an
inhomogeneous equation `E = b` is homogenized as `b′E − bF`), whose coefficient recurrence has
`O(2^i)`-bit coefficients; rewriting the recurrence for the partial sums `s_ℓ` gives a matrix
recurrence `S_ℓ = M_ℓ S_{ℓ−1}` and the product (4.81) is a binary splitting.  Example: `arctan`,
`f′(1 + t²) = 1`, translated recurrence `(1 + x_i²) ℓ u_ℓ + 2x_i(ℓ−1) u_{ℓ−1} + (ℓ−2) u_{ℓ−2} = 0`,
then for `v_ℓ = u_ℓ r^ℓ` and `s_ℓ = ∑_{j≤ℓ} v_j`, a 3×3 matrix recurrence.

What is formalized (all proven) — the mathematical skeleton; the cost statement is not:

* Bit blocks: `blockNum x a b = ⌊x 2^b⌋ − 2^(b−a) ⌊x 2^a⌋` (bits `a+1..b`),
  `0 ≤ blockNum < 2^(b−a)`, `bitBlock = blockNum/2^b < 2^(−a)`, telescoping `bitBlock_eq_sub`.
  Theorem 4.2's blocks
  `burstBlock x i = bitBlock x (2^i − 1) (2^(i+1) − 1)`: numerator `< 2^(2^i)` (`2^i` bits), value
  `< 2^(1−2^i)` (`burstBlock_lt`), `∑_{i<k} r_{i+1}` is the `2^k − 1`-bit truncation
  (`sum_burstBlock`), and equals `x` when `x` has `n ≤ 2^k − 1` bits (`sum_burstBlock_eq_self`).
* `sum_shift_sub`: `∑_{i<k} (f(x_i + r_i) − f(x_i)) = f(x_k) − f(0)`, the telescoping behind
  `f(x) = ∑ f_i^*(r_{i+1})`.
* Translation: `iteratedDeriv_comp_const_add` and `IsHolonomic.comp_const_add` (`f(x_i + t)` is
  holonomic with coefficients `c_j(X + x_i)`); homogenization `isHolonomic_of_inhomogeneous`
  (`∑ c_j f^{(j)} = b` with `c_m, b ≠ 0` ⇒ holonomic, via `b′E − bF`).
* The example: `isHolonomic_arctan` (`(1 + t²) f″ + 2t f′ = 0`); the translated recurrence for a
  formal power series `g` with `g′ · (1 + (c + t)²) = 1`: `arctan_shift_coeff_recurrence`
  (`(1+c²)(ℓ+2) u_{ℓ+2} + 2c(ℓ+1) u_{ℓ+1} + ℓ u_ℓ = 0`); the passage to `v_ℓ = u_ℓ r^ℓ`
  (`arctan_v_recurrence`) and to the partial sums (`arctan_s_recurrence`); the 3×3 step matrix
  `arctanStepMatrix` with `arctan_step_matrix_eq` (`S_{ℓ+3} = M_{ℓ+3} S_{ℓ+2}`).
* (4.81): `matProd` and `vec_eq_matProd_mulVec`: `S_{d+j} = M_{d+j} ⋯ M_{d+1} S_d`.

Not formalized: the `O(M(n) log³ n)` (and `O(M(n) log² n)` per term) costs, the term count
`n/2^i + O(log n)` (needs Taylor-coefficient bounds of the translated series), the coefficient-size
estimate `O(ℓ(2^i + log ℓ))`, the general passage from a translated ODE to its coefficient
recurrence (§4.12; done here for the example), Exercise 4.49, and the algorithm itself.
-/
namespace Tengoku.Azurite end Tengoku.Azurite open Tengoku.Azurite
namespace Azurite

namespace BZ

open Finset Polynomial

variable {x : ℝ}

/-! ### Bit blocks -/

/-- The integer formed by bits `a+1, …, b` of `x`: `⌊x 2^b⌋ − 2^(b−a) ⌊x 2^a⌋`.-/
noncomputable def blockNum (x : ℝ) (a b : ℕ) : ℤ := ⌊x * 2 ^ b⌋ - 2 ^ (b - a) * ⌊x * 2 ^ a⌋

/-- The block as a real number, `blockNum/2^b`.-/
noncomputable def bitBlock (x : ℝ) (a b : ℕ) : ℝ := (blockNum x a b : ℝ) / 2 ^ b

/--
@isnad1 id=eq.1h3v.s6.44dac4d09769 from=translated src=- shape=07cc1985 vocab=2ee782f6
-/
theorem two_pow_sub_mul {a b : ℕ} (hab : a ≤ b) : (2 : ℝ) ^ (b - a) * (x * 2 ^ a) = x * 2 ^ b := by
  rw [show b = a + (b - a) by omega, pow_add, Nat.add_sub_cancel_left]
  ring

/--
@isnad1 id=le.1h3v.s4.638e685ac58a from=translated src=- shape=163579cf vocab=3317ad6d
-/
theorem blockNum_nonneg {a b : ℕ} (hab : a ≤ b) : 0 ≤ blockNum x a b := by
  unfold blockNum
  have h := (floor_mul_pow_bounds (x * 2 ^ a) (b - a)).1
  rw [two_pow_sub_mul hab] at h
  linarith

/--
@isnad1 id=lt.1h3v.s5.31cfc801fac2 from=translated src=- shape=2cda043b vocab=f14a4c0b
-/
theorem blockNum_lt {a b : ℕ} (hab : a ≤ b) : blockNum x a b < 2 ^ (b - a) := by
  unfold blockNum
  have h := (floor_mul_pow_bounds (x * 2 ^ a) (b - a)).2
  rw [two_pow_sub_mul hab] at h
  linarith

/--
@isnad1 id=le.1h3v.s4.cfb552c4bb55 from=translated src=- shape=c8928ba9 vocab=e148a04e
-/
theorem bitBlock_nonneg {a b : ℕ} (hab : a ≤ b) : 0 ≤ bitBlock x a b :=
  div_nonneg (by exact_mod_cast blockNum_nonneg hab) (by positivity)

/-- A block of bits `a+1..b` is below `2^(−a)`.
@isnad1 id=lt.1h3v.s5.a013cb4d36bd from=translated src=- shape=bf109076 vocab=0f194776
-/
theorem bitBlock_lt {a b : ℕ} (hab : a ≤ b) : bitBlock x a b < 1 / 2 ^ a := by
  unfold bitBlock
  have h : (blockNum x a b : ℝ) < 2 ^ (b - a) := by exact_mod_cast blockNum_lt hab
  rw [div_lt_div_iff₀ (by positivity) (by positivity), one_mul]
  calc (blockNum x a b : ℝ) * 2 ^ a < 2 ^ (b - a) * 2 ^ a := by gcongr
    _ = 2 ^ b := by rw [← pow_add]; congr 1; omega

/--
@isnad1 id=eq.1h3v.s7.945fe8bba7cd from=translated src=- shape=20cd7f70 vocab=beb45e1b
-/
theorem bitBlock_eq_sub {a b : ℕ} (hab : a ≤ b) :
    bitBlock x a b = (⌊x * 2 ^ b⌋ : ℝ) / 2 ^ b - (⌊x * 2 ^ a⌋ : ℝ) / 2 ^ a := by
  unfold bitBlock blockNum
  push_cast
  rw [show b = a + (b - a) by omega, Nat.add_sub_cancel_left, pow_add]
  field_simp

/-- Theorem 4.2's blocks: `r_{i+1}` consists of bits `2^i, …, 2^(i+1) − 1` of `x`.-/
noncomputable def burstBlock (x : ℝ) (i : ℕ) : ℝ := bitBlock x (2 ^ i - 1) (2 ^ (i + 1) - 1)

/--
@isnad1 id=le.0h1v.s6.6f2314e802dd from=translated src=- shape=4a43043c vocab=35c416b2
-/
theorem two_pow_sub_one_le (i : ℕ) : 2 ^ i - 1 ≤ 2 ^ (i + 1) - 1 := by
  have := Nat.one_le_two_pow (n := i)
  rw [pow_succ]
  omega

/-- The numerator of `r_{i+1}` has at most `2^i` bits.
@isnad1 id=lt.0h2v.s6.b823425b8425 from=translated src=- shape=aaf7e78c vocab=63b8e051
-/
theorem burstBlock_num_lt (i : ℕ) : blockNum x (2 ^ i - 1) (2 ^ (i + 1) - 1) < 2 ^ 2 ^ i := by
  have h := blockNum_lt (x := x) (two_pow_sub_one_le i)
  have e : 2 ^ (i + 1) - 1 - (2 ^ i - 1) = 2 ^ i := by
    have := Nat.one_le_two_pow (n := i)
    rw [pow_succ]
    omega
  rwa [e] at h

/--
@isnad1 id=le.0h2v.s4.1202b7d2e4ac from=translated src=- shape=25b8bdde vocab=1bd6f3c9
-/
theorem burstBlock_nonneg (i : ℕ) : 0 ≤ burstBlock x i := bitBlock_nonneg (two_pow_sub_one_le i)

/-- `0 ≤ r_{i+1} < 2^(1 − 2^i)`.
@isnad1 id=lt.0h2v.s6.d4cecd104e21 from=translated src=- shape=39d04647 vocab=5c959a42
-/
theorem burstBlock_lt (i : ℕ) : burstBlock x i < 2 * (1 / 2) ^ 2 ^ i := by
  have h := bitBlock_lt (x := x) (two_pow_sub_one_le i)
  have e : (1 : ℝ) / 2 ^ (2 ^ i - 1) = 2 * (1 / 2) ^ 2 ^ i := by
    have hk : 2 ^ i = (2 ^ i - 1) + 1 := by have := Nat.one_le_two_pow (n := i); omega
    conv_rhs => rw [hk, pow_succ, one_div_pow]
    field_simp
  rwa [e] at h

/-- `∑_{i<k} r_{i+1}` is the truncation of `x ∈ [0, 1)` to `2^k − 1` bits.
@isnad1 id=eq.2h2v.s7.e7867bd1eee7 from=translated src=- shape=e1aaf58b vocab=11baeee6
-/
theorem sum_burstBlock (hx0 : 0 ≤ x) (hx : x < 1) (k : ℕ) :
    ∑ i ∈ range k, burstBlock x i = (⌊x * 2 ^ (2 ^ k - 1)⌋ : ℝ) / 2 ^ (2 ^ k - 1) := by
  have hterm : ∀ i, burstBlock x i
      = (⌊x * 2 ^ (2 ^ (i + 1) - 1)⌋ : ℝ) / 2 ^ (2 ^ (i + 1) - 1)
        - (⌊x * 2 ^ (2 ^ i - 1)⌋ : ℝ) / 2 ^ (2 ^ i - 1) :=
    fun i => bitBlock_eq_sub (two_pow_sub_one_le i)
  simp_rw [hterm]
  rw [sum_range_sub (fun i => (⌊x * 2 ^ (2 ^ i - 1)⌋ : ℝ) / 2 ^ (2 ^ i - 1))]
  have h0 : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr ⟨hx0, hx⟩
  simp [h0]

/-- For an `n`-bit `x` (`x 2^n ∈ ℤ`) with `n ≤ 2^k − 1`, the blocks reassemble `x` exactly.
@isnad1 id=eq.4h3v.s6.b85fe32e9565 from=translated src=- shape=8fe66e45 vocab=c0b89fd2
-/
theorem sum_burstBlock_eq_self (hx0 : 0 ≤ x) (hx : x < 1) {n k : ℕ} (hn : n ≤ 2 ^ k - 1)
    (hxn : ∃ m : ℤ, x * 2 ^ n = m) : ∑ i ∈ range k, burstBlock x i = x := by
  obtain ⟨m, hm⟩ := hxn
  obtain ⟨p, hp⟩ : ∃ p, 2 ^ k - 1 = n + p := ⟨2 ^ k - 1 - n, by omega⟩
  rw [sum_burstBlock hx0 hx, hp]
  have h2n : (0 : ℝ) < 2 ^ n := by positivity
  have hxm : x = m / 2 ^ n := by rw [eq_div_iff h2n.ne']; exact hm
  have e : x * 2 ^ (n + p) = ((m * 2 ^ p : ℤ) : ℝ) := by
    push_cast
    rw [hxm, pow_add]
    field_simp
  rw [e, Int.floor_intCast]
  push_cast
  rw [hxm, pow_add]
  field_simp

/-! ### The telescoping `f(x) = ∑ f_i^*(r_{i+1})` -/

/-- With `x_i = ∑_{j<i} r_j`: `∑_{i<k} (f(x_i + r_i) − f(x_i)) = f(x_k) − f(0)`; each summand is
`f_i^*(r_{i+1})` for `f_i(t) = f(x_i + t)`, `f_i^*(t) = f_i(t) − f_i(0)`.
@isnad1 id=eq.0h3v.s6.f0e62b1f0357 from=translated src=- shape=44799d28 vocab=4b1bed3f
-/
theorem sum_shift_sub (f : ℝ → ℝ) (r : ℕ → ℝ) (k : ℕ) :
    ∑ i ∈ range k, (f (∑ j ∈ range i, r j + r i) - f (∑ j ∈ range i, r j))
      = f (∑ j ∈ range k, r j) - f 0 := by
  have := sum_range_sub (fun i => f (∑ j ∈ range i, r j)) k
  simp only [sum_range_succ, sum_range_zero] at this
  exact this

/-- The decomposition of Theorem 4.2 with `f(0) = 0`.-/
theorem eq_sum_shift_sub {f : ℝ → ℝ} (hf0 : f 0 = 0) (r : ℕ → ℝ) (k : ℕ) :
    f (∑ j ∈ range k, r j)
      = ∑ i ∈ range k, (f (∑ j ∈ range i, r j + r i) - f (∑ j ∈ range i, r j)) := by
  rw [sum_shift_sub, hf0, sub_zero]

/-! ### Translating the differential equation -/

/--
@isnad1 id=eq.0h3v.s6.4a483517e13d from=translated src=- shape=152d273a vocab=53fd09fe
-/
theorem iteratedDeriv_comp_const_add (f : ℝ → ℝ) (c : ℝ) (n : ℕ) :
    iteratedDeriv n (fun t => f (c + t)) = fun t => iteratedDeriv n f (c + t) := by
  induction n generalizing f with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ', iteratedDeriv_succ']
    have : deriv (fun t => f (c + t)) = fun t => deriv f (c + t) :=
      funext fun t => deriv_comp_const_add f c t
    rw [this, ih]

/-- `f_i(t) = f(x_i + t)` is holonomic when `f` is, with coefficients `c_j(x_i + t)`.
@isnad1 id=isholono.1h2v.s4.9ead37f7a165 from=translated src=- shape=d0661061 vocab=c73397b3
-/
theorem IsHolonomic.comp_const_add {f : ℝ → ℝ} (hf : IsHolonomic f) (c : ℝ) :
    IsHolonomic fun t => f (c + t) := by
  obtain ⟨r, a, ⟨i, hi⟩, h⟩ := hf
  refine ⟨r, fun j => (a j).comp (X + C c), ⟨i, comp_X_add_C_ne_zero_iff.mpr hi⟩, fun t => ?_⟩
  simp only [iteratedDeriv_comp_const_add, eval_comp, eval_add, eval_X, eval_C]
  rw [add_comm t c]
  exact h (c + t)

/-- Homogenization: if `∑_{j≤m} c_j f^{(j)} = b` with polynomials `c_j, b`, `c_m ≠ 0 ≠ b`, then `f`
is holonomic (`b′E − bF`).
@isnad1 id=isholono.4h4v.s8.55c612fed264 from=translated src=- shape=20425180 vocab=5aacc138
-/
theorem isHolonomic_of_inhomogeneous {f : ℝ → ℝ} (hf : ∀ j, Differentiable ℝ (iteratedDeriv j f))
    {m : ℕ} (c : Fin (m + 1) → ℝ[X]) (hc : c (Fin.last m) ≠ 0) (b : ℝ[X]) (hb : b ≠ 0)
    (h : ∀ t, ∑ j, (c j).eval t * iteratedDeriv j f t = b.eval t) : IsHolonomic f := by
  -- the derivative of the relation
  have hF : ∀ t, ∑ j : Fin (m + 1), ((c j).derivative.eval t * iteratedDeriv j f t
      + (c j).eval t * iteratedDeriv (j + 1) f t) = b.derivative.eval t := by
    intro t
    have h1 : HasDerivAt (fun t => ∑ j : Fin (m + 1), (c j).eval t * iteratedDeriv j f t)
        (∑ j : Fin (m + 1), ((c j).derivative.eval t * iteratedDeriv j f t
          + (c j).eval t * iteratedDeriv (j + 1) f t)) t := by
      refine (HasDerivAt.sum (u := Finset.univ)
        (A := fun j y => (c j).eval y * iteratedDeriv (j : ℕ) f y)
        (A' := fun j => (c j).derivative.eval t * iteratedDeriv (j : ℕ) f t
          + (c j).eval t * iteratedDeriv ((j : ℕ) + 1) f t) fun j _ => ?_).congr_of_eventuallyEq
        (Filter.Eventually.of_forall fun y => (Finset.sum_apply y Finset.univ
          (fun j y => (c j).eval y * iteratedDeriv (j : ℕ) f y)).symm)
      have hp : HasDerivAt (fun y : ℝ => (c j).eval y) ((c j).derivative.eval t) t :=
        (c j).hasDerivAt t
      have hq : HasDerivAt (iteratedDeriv (j : ℕ) f) (iteratedDeriv ((j : ℕ) + 1) f t) t := by
        rw [iteratedDeriv_succ]
        exact (hf j t).hasDerivAt
      exact hp.mul hq
    have h2 : HasDerivAt (fun t => ∑ j : Fin (m + 1), (c j).eval t * iteratedDeriv j f t)
        (b.derivative.eval t) t := by
      have : (fun t => ∑ j : Fin (m + 1), (c j).eval t * iteratedDeriv j f t)
          = fun t => b.eval t := funext h
      rw [this]
      exact b.hasDerivAt t
    exact h1.unique h2
  -- the homogeneous coefficients: `b′ c_j − b c_j′ − b c_{j−1}`
  let c' : Fin (m + 2) → ℝ[X] := Fin.snoc c 0
  let c'' : Fin (m + 2) → ℝ[X] := Fin.cons 0 c
  refine ⟨m + 1, fun j => b.derivative * c' j - b * (c' j).derivative - b * c'' j,
    ⟨Fin.last (m + 1), ?_⟩, fun t => ?_⟩
  · have e1 : c' (Fin.last (m + 1)) = 0 := Fin.snoc_last _ _
    have e2 : c'' (Fin.last (m + 1)) = c (Fin.last m) := by
      rw [← Fin.succ_last]
      exact Fin.cons_succ _ _ _
    beta_reduce
    rw [e1, e2]
    simp only [mul_zero, derivative_zero, zero_sub, neg_zero]
    exact neg_ne_zero.mpr (mul_ne_zero hb hc)
  · have hsnoc : ∀ g : Fin (m + 2) → ℝ,
        ∑ j : Fin (m + 2), (c' j).eval t * g j
          = ∑ j : Fin (m + 1), (c j).eval t * g j.castSucc := by
      intro g
      rw [Fin.sum_univ_castSucc]
      simp [c', Fin.snoc_castSucc, Fin.snoc_last]
    have hsnoc' : ∀ g : Fin (m + 2) → ℝ,
        ∑ j : Fin (m + 2), (c' j).derivative.eval t * g j
          = ∑ j : Fin (m + 1), (c j).derivative.eval t * g j.castSucc := by
      intro g
      rw [Fin.sum_univ_castSucc]
      simp [c', Fin.snoc_castSucc, Fin.snoc_last]
    have hcons : ∀ g : Fin (m + 2) → ℝ,
        ∑ j : Fin (m + 2), (c'' j).eval t * g j = ∑ j : Fin (m + 1), (c j).eval t * g j.succ := by
      intro g
      rw [Fin.sum_univ_succ]
      simp [c'', Fin.cons_zero, Fin.cons_succ]
    simp only [eval_sub, eval_mul, sub_mul, sum_sub_distrib, mul_assoc, ← mul_sum]
    rw [hsnoc, hsnoc', hcons]
    simp only [Fin.val_castSucc, Fin.val_succ]
    have hE := h t
    have hF' := hF t
    rw [sum_add_distrib] at hF'
    linear_combination b.derivative.eval t * hE - b.eval t * hF'

/-! ### The example: `arctan` -/

/-- `(1 + t²) arctan″ + 2t arctan′ = 0`.
@isnad1 id=isholono.0h0v.s1.ae9279188921 from=translated src=- shape=49959d42 vocab=88fc4d79
-/
theorem isHolonomic_arctan : IsHolonomic Real.arctan := by
  refine ⟨2, ![0, C 2 * X, C 1 + X ^ 2], ⟨1, by simp⟩, fun t => ?_⟩
  have h2 : iteratedDeriv 2 Real.arctan = fun t => -(2 * t) / (1 + t ^ 2) ^ 2 := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, Real.deriv_arctan]
    funext t
    have hpos : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
    have h' : HasDerivAt (fun x : ℝ => (1 + x ^ 2)⁻¹)
        (-((2 : ℕ) * t ^ (2 - 1)) / (1 + t ^ 2) ^ 2) t :=
      ((hasDerivAt_pow 2 t).const_add 1).inv hpos
    have h1 : (fun x : ℝ => 1 / (1 + x ^ 2)) = fun x => (1 + x ^ 2)⁻¹ := by
      funext x
      rw [one_div]
    rw [h1, h'.deriv]
    push_cast
    ring
  rw [Fin.sum_univ_three]
  simp [h2, Real.deriv_arctan, iteratedDeriv_one]
  have hpos : (1 : ℝ) + t ^ 2 ≠ 0 := by positivity
  field_simp
  ring

section Recurrence

end Recurrence

/-- Passing to `v_ℓ = u_ℓ r^ℓ`: `(1 + c²)(ℓ+2) v_{ℓ+2} + 2cr(ℓ+1) v_{ℓ+1} + r²ℓ v_ℓ = 0`.
@isnad1 id=eq.1h4v.s8.37f3664f1b38 from=translated src=- shape=2c1f785d vocab=d18151ec
-/
theorem arctan_v_recurrence {c r : ℝ} {u : ℕ → ℝ} {ℓ : ℕ}
    (h : (1 + c ^ 2) * (ℓ + 2) * u (ℓ + 2) + 2 * c * (ℓ + 1) * u (ℓ + 1) + ℓ * u ℓ = 0) :
    (1 + c ^ 2) * (ℓ + 2) * (u (ℓ + 2) * r ^ (ℓ + 2))
      + 2 * c * r * (ℓ + 1) * (u (ℓ + 1) * r ^ (ℓ + 1)) + r ^ 2 * ℓ * (u ℓ * r ^ ℓ) = 0 := by
  linear_combination r ^ (ℓ + 2) * h

/-- Passing to the partial sums `s_ℓ` (`s_{ℓ+1} = s_ℓ + v_{ℓ+1}`): the order-3 recurrence
`(1 + c²)(ℓ+3)(s_{ℓ+3} − s_{ℓ+2}) + 2cr(ℓ+2)(s_{ℓ+2} − s_{ℓ+1}) + r²(ℓ+1)(s_{ℓ+1} − s_ℓ) = 0`.
@isnad1 id=eq.2h5v.s9.3456fd2cc53d from=translated src=- shape=153bb46e vocab=64e0814d
-/
theorem arctan_s_recurrence {c r : ℝ} {v s : ℕ → ℝ} (hs : ∀ ℓ, s (ℓ + 1) = s ℓ + v (ℓ + 1)) {ℓ : ℕ}
    (h : (1 + c ^ 2) * (ℓ + 1 + 2) * v (ℓ + 1 + 2) + 2 * c * r * (ℓ + 1 + 1) * v (ℓ + 1 + 1)
      + r ^ 2 * (ℓ + 1) * v (ℓ + 1) = 0) :
    (1 + c ^ 2) * (ℓ + 3) * (s (ℓ + 3) - s (ℓ + 2)) + 2 * c * r * (ℓ + 2) * (s (ℓ + 2) - s (ℓ + 1))
      + r ^ 2 * (ℓ + 1) * (s (ℓ + 1) - s ℓ) = 0 := by
  have h1 := hs (ℓ + 2)
  have h2 := hs (ℓ + 1)
  have h3 := hs ℓ
  rw [show ℓ + 2 + 1 = ℓ + 3 by ring] at h1
  rw [show ℓ + 1 + 1 = ℓ + 2 by ring] at h2 h
  rw [show ℓ + 1 + 2 = ℓ + 3 by ring] at h
  linear_combination h + (1 + c ^ 2) * (ℓ + 3) * h1 + 2 * c * r * (ℓ + 2) * h2
    + r ^ 2 * (ℓ + 1) * h3

/-- The step matrix `M_{ℓ+3}` of the arctan recurrence, acting on `(s_{ℓ+2}, s_{ℓ+1}, s_ℓ)`.-/
noncomputable def arctanStepMatrix (c r : ℝ) (ℓ : ℕ) : Matrix (Fin 3) (Fin 3) ℝ :=
  let D : ℝ := (1 + c ^ 2) * (ℓ + 3)
  ![![1 - 2 * c * r * (ℓ + 2) / D, (2 * c * r * (ℓ + 2) - r ^ 2 * (ℓ + 1)) / D,
      r ^ 2 * (ℓ + 1) / D],
    ![1, 0, 0],
    ![0, 1, 0]]

/-- `S_{ℓ+3} = M_{ℓ+3} S_{ℓ+2}` for `S_ℓ = (s_ℓ, s_{ℓ−1}, s_{ℓ−2})`.
@isnad1 id=eq.1h4v.s8.3f942ae5a82f from=translated src=- shape=2bfd88c7 vocab=a571c524
-/
theorem arctan_step_matrix_eq {c r : ℝ} {s : ℕ → ℝ} {ℓ : ℕ}
    (h : (1 + c ^ 2) * (ℓ + 3) * (s (ℓ + 3) - s (ℓ + 2))
      + 2 * c * r * (ℓ + 2) * (s (ℓ + 2) - s (ℓ + 1)) + r ^ 2 * (ℓ + 1) * (s (ℓ + 1) - s ℓ) = 0) :
    ![s (ℓ + 3), s (ℓ + 2), s (ℓ + 1)]
      = (arctanStepMatrix c r ℓ).mulVec ![s (ℓ + 2), s (ℓ + 1), s ℓ] := by
  have hD : (1 + c ^ 2) * ((ℓ : ℝ) + 3) ≠ 0 := by positivity
  have key : s (ℓ + 3) = ((1 + c ^ 2) * (ℓ + 3) * s (ℓ + 2)
      - 2 * c * r * (ℓ + 2) * (s (ℓ + 2) - s (ℓ + 1)) - r ^ 2 * (ℓ + 1) * (s (ℓ + 1) - s ℓ))
      / ((1 + c ^ 2) * (ℓ + 3)) := by
    rw [eq_div_iff hD]
    linear_combination h
  rw [key]
  ext i
  fin_cases i
  · simp [arctanStepMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    field_simp
    ring
  · simp [arctanStepMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  · simp [arctanStepMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-! ### The matrix product (4.81) -/

variable {m : ℕ}

/-- `matProd M d j = M_{d+j} ⋯ M_{d+1}` (and `1` for `j = 0`).-/
def matProd (M : ℕ → Matrix (Fin m) (Fin m) ℝ) (d : ℕ) : ℕ → Matrix (Fin m) (Fin m) ℝ
  | 0 => 1
  | j + 1 => M (d + j + 1) * matProd M d j

/-- (4.81): a matrix recurrence `S_{ℓ+1} = M_{ℓ+1} S_ℓ` (for `ℓ ≥ d`) unrolls to
`S_{d+j} = M_{d+j} ⋯ M_{d+1} S_d`.
@isnad1 id=eq.1h5v.s7.1291da93574b from=translated src=- shape=c86c067a vocab=e9df0413
-/
theorem vec_eq_matProd_mulVec (M : ℕ → Matrix (Fin m) (Fin m) ℝ) (S : ℕ → Fin m → ℝ) (d : ℕ)
    (hS : ∀ ℓ, S (d + ℓ + 1) = (M (d + ℓ + 1)).mulVec (S (d + ℓ))) (j : ℕ) :
    S (d + j) = (matProd M d j).mulVec (S d) := by
  induction j with
  | zero => simp [matProd]
  | succ j ih =>
    rw [show d + (j + 1) = d + j + 1 by ring, hS, ih, matProd, Matrix.mulVec_mulVec]

end BZ

end Azurite
-- Tengoku: root names of this library moved to Tengoku.Azurite so they do not collide with other libraries (generated)
