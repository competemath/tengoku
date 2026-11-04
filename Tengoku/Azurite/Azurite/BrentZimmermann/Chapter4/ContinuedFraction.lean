/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.StirlingLogGamma
import Tengoku.Seed.Algebra.ContinuedFractions.ContinuantsRecurrence
import Tengoku.Seed.Algebra.ContinuedFractions.ConvergentsEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.6: Continued fractions (introduction)

A continued fraction `f = b₀ + a₁/b₁+ a₂/b₂+ a₃/b₃+ …` (in the shorthand with `+` after each
denominator) is given by two sequences `(a_j)_{j≥1}`, `(b_j)_{j≥0}`; its value is `lim f_k` when
the limit exists, where `f_k = b₀ + a₁/b₁+ … a_k/b_k` is the `k`-th approximant (4.41).  Examples:
Euler's

  `e^x E₁(x) = 1/x+ 1/1+ 1/x+ 2/1+ 2/x+ 3/1+ …`                                            (4.39)

and

  `erfc x = (e^(−x²)/√π) · 1/x+ (1/2)/x+ (2/2)/x+ (3/2)/x+ (4/2)/x+ …`.                       (4.40)

(4.39) converges for all real `x > 0` and is the method of choice for `E₁` where the power series
cancels and the asymptotic expansion is not yet accurate — in practice for `x ∈ (c₁ n, c₂ n)`,
`c₁ ≈ 0.1`, `c₂ = ln 2` (Exercise 4.24).

What is formalized, on top of Mathlib's `GenContFract`:

* `contFrac a b` — the generalized continued fraction with head `b 0` and pairs
  `(a (j+1), b (j+1))`; `contFrac_get?`, `contFrac_head`, `contFrac_tail`.
* `approximant a b k` — the `k`-th approximant (4.41) by nested evaluation (`convs'`);
  `approximant_zero`, `approximant_one`, `approximant_succ` (the nesting
  `f_{k+1}(a, b) = b₀ + a₁ / f_k(a', b')` with the shifted sequences); `HasContFracValue`.
* The continuants: `nums_zero`, `dens_zero`, `nums_one`, `dens_one`, `nums_recurrence'`,
  `dens_recurrence'` (`A_{n+2} = b_{n+2} A_{n+1} + a_{n+2} A_n`, likewise `B`), and
  `approximant_eq_convs` — for positive coefficients the nested approximant is `A_k / B_k`
  (Mathlib's `convs_eq_convs'`).
* `eulerNum`, `eulerDen` — the coefficients of (4.39); `erfcCFNum`, `erfcCFDen` — of (4.40);
  their first approximants (`eulerE1_approximant_one/two`, `erfcCF_approximant_one/two`), and
  the consistency check `erfcCF_approximant_two_mem`: the second approximant of (4.40) lies in
  the bracket `[L(1 − 1/(2x²)), L]` of the asymptotic expansion (4.37).

Not formalized: the convergence of (4.39) and (4.40) to `e^x E₁(x)` and `erfc x` (Stieltjes /
hypergeometric continued-fraction theory), the interval `(c₁ n, c₂ n)`, Exercise 4.24, extended
complex values.
-/

namespace Azurite

namespace BZ

open Filter Topology GenContFract

/-! ### Continued fractions from coefficient sequences -/

/-- The continued fraction `b₀ + a₁/b₁+ a₂/b₂+ …`.-/
noncomputable def contFrac (a b : ℕ → ℝ) : GenContFract ℝ :=
  ⟨b 0, Stream'.Seq.ofStream fun n => ⟨a (n + 1), b (n + 1)⟩⟩

/--
@isnad1 id=eq.0h3v.s5.b6562caf7cfc from=translated src=- shape=0e463845 vocab=316261a2
-/
theorem contFrac_get? (a b : ℕ → ℝ) (n : ℕ) :
    (contFrac a b).s.get? n = some ⟨a (n + 1), b (n + 1)⟩ := rfl

/--
@isnad1 id=eq.0h2v.s5.5c5b97754a8f from=translated src=- shape=5efa35f5 vocab=34dbfc05
-/
theorem contFrac_head (a b : ℕ → ℝ) : (contFrac a b).s.head = some ⟨a 1, b 1⟩ := rfl

/-- The tail of the sequence is the sequence of the shifted coefficients.
@isnad1 id=eq.0h2v.s5.e4a02c588b31 from=translated src=- shape=9e9173cd vocab=a4614578
-/
theorem contFrac_tail (a b : ℕ → ℝ) :
    (contFrac a b).s.tail = (contFrac (fun j => a (j + 1)) (fun j => b (j + 1))).s := rfl

/-- The `k`-th approximant `f_k = b₀ + a₁/b₁+ … a_k/b_k` (4.41), by nested evaluation.-/
noncomputable def approximant (a b : ℕ → ℝ) (k : ℕ) : ℝ := (contFrac a b).convs' k

/-- The value of a continued fraction: the limit of its approximants, when it exists.-/
def HasContFracValue (a b : ℕ → ℝ) (f : ℝ) : Prop := Tendsto (approximant a b) atTop (𝓝 f)

/--
@isnad1 id=eq.0h2v.s4.3cf7b9152250 from=translated src=- shape=df9b3ed1 vocab=556a801e
-/
@[simp] theorem approximant_zero (a b : ℕ → ℝ) : approximant a b 0 = b 0 := by
  unfold approximant convs'
  simp [convs'Aux]
  rfl

/-- `f_{k+1}(a, b) = b₀ + a₁ / f_k(a', b')` where `a' j = a (j+1)`, `b' j = b (j+1)`.
@isnad1 id=eq.0h3v.s6.81521051355e from=translated src=- shape=70a7ca6c vocab=574a1e6c
-/
theorem approximant_succ (a b : ℕ → ℝ) (k : ℕ) :
    approximant a b (k + 1)
      = b 0 + a 1 / approximant (fun j => a (j + 1)) (fun j => b (j + 1)) k := by
  unfold approximant
  rw [convs', convs'Aux_succ_some (contFrac_head a b), contFrac_tail, convs']
  rfl

/--
@isnad1 id=eq.0h2v.s5.8429201b6b0f from=translated src=- shape=b8c2b2f6 vocab=574a1e6c
-/
theorem approximant_one (a b : ℕ → ℝ) : approximant a b 1 = b 0 + a 1 / b 1 := by
  rw [approximant_succ, approximant_zero]

/-! ### Continuants -/

/--
@isnad1 id=eq.0h2v.s4.e8abd7ce91b3 from=translated src=- shape=1f7cd19d vocab=20e00ddf
-/
theorem nums_zero (a b : ℕ → ℝ) : (contFrac a b).nums 0 = b 0 := zeroth_num_eq_h

/--
@isnad1 id=eq.0h2v.s4.635f27e42a12 from=translated src=- shape=ba58dfec vocab=35707766
-/
theorem dens_zero (a b : ℕ → ℝ) : (contFrac a b).dens 0 = 1 := zeroth_den_eq_one

/--
@isnad1 id=eq.0h2v.s5.92f2cefcae97 from=translated src=- shape=746c8da8 vocab=3e09b96c
-/
theorem nums_one (a b : ℕ → ℝ) : (contFrac a b).nums 1 = b 1 * b 0 + a 1 :=
  first_num_eq (contFrac_get? a b 0)

/--
@isnad1 id=eq.0h2v.s4.a96b2f97159e from=translated src=- shape=1f7cd19d vocab=35707766
-/
theorem dens_one (a b : ℕ → ℝ) : (contFrac a b).dens 1 = b 1 := first_den_eq (contFrac_get? a b 0)

/-- `A_{n+2} = b_{n+2} A_{n+1} + a_{n+2} A_n`.
@isnad1 id=eq.0h3v.s6.fe240884a0e8 from=translated src=- shape=329ce479 vocab=3e09b96c
-/
theorem nums_recurrence' (a b : ℕ → ℝ) (n : ℕ) :
    (contFrac a b).nums (n + 2)
      = b (n + 2) * (contFrac a b).nums (n + 1) + a (n + 2) * (contFrac a b).nums n :=
  nums_recurrence (contFrac_get? a b (n + 1)) rfl rfl

/-- `B_{n+2} = b_{n+2} B_{n+1} + a_{n+2} B_n`.
@isnad1 id=eq.0h3v.s6.67b2d079aa3d from=translated src=- shape=329ce479 vocab=5f24eb8d
-/
theorem dens_recurrence' (a b : ℕ → ℝ) (n : ℕ) :
    (contFrac a b).dens (n + 2)
      = b (n + 2) * (contFrac a b).dens (n + 1) + a (n + 2) * (contFrac a b).dens n :=
  dens_recurrence (contFrac_get? a b (n + 1)) rfl rfl

/-- For positive coefficients the nested approximant is the quotient of continuants
`A_k / B_k` (Mathlib's `convs_eq_convs'`).
@isnad1 id=eq.1h3v.s5.48677d10d9ac from=translated src=- shape=07e6dbfa vocab=3f68e466
-/
theorem approximant_eq_convs {a b : ℕ → ℝ} (hpos : ∀ j, 1 ≤ j → 0 < a j ∧ 0 < b j) (k : ℕ) :
    approximant a b k = (contFrac a b).convs k := by
  unfold approximant
  symm
  apply convs_eq_convs'
  intro gp m _ hm
  rw [contFrac_get?] at hm
  obtain rfl := Option.some_injective _ hm
  exact hpos (m + 1) (by omega)

/-! ### The examples (4.39) and (4.40) -/

/-- The partial numerators of Euler's fraction (4.39): `1, 1, 1, 2, 2, 3, 3, …`, i.e.
`a_j = max 1 ⌊j/2⌋`.-/
noncomputable def eulerNum (j : ℕ) : ℝ := (max 1 (j / 2) : ℕ)

/-- The partial denominators of (4.39): `b₀ = 0`, then `x, 1, x, 1, …`.-/
noncomputable def eulerDen (x : ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else if j % 2 = 1 then x else 1

/--
@isnad1 id=eq.0h1v.s4.76c18981174a from=translated src=- shape=a8c559ca vocab=1df87d21
-/
theorem eulerE1_approximant_one (x : ℝ) : approximant eulerNum (eulerDen x) 1 = 1 / x := by
  rw [approximant_one]; simp [eulerNum, eulerDen]

/--
@isnad1 id=eq.0h1v.s5.c8f9ba1d44ee from=translated src=- shape=343f314d vocab=96b6c490
-/
theorem eulerE1_approximant_two (x : ℝ) : approximant eulerNum (eulerDen x) 2 = 1 / (x + 1) := by
  rw [approximant_succ, approximant_one]; simp [eulerNum, eulerDen]

/-- The partial numerators of (4.40): `1, 1/2, 2/2, 3/2, …`, i.e. `a₁ = 1`, `a_j = (j−1)/2`.-/
noncomputable def erfcCFNum (j : ℕ) : ℝ := if j = 1 then 1 else ((j : ℝ) - 1) / 2

/-- The partial denominators of (4.40): `b₀ = 0`, then `x, x, x, …`.-/
noncomputable def erfcCFDen (x : ℝ) (j : ℕ) : ℝ := if j = 0 then 0 else x

/--
@isnad1 id=eq.0h1v.s4.f125b2b4cbdf from=translated src=- shape=a8c559ca vocab=502ec324
-/
theorem erfcCF_approximant_one (x : ℝ) : approximant erfcCFNum (erfcCFDen x) 1 = 1 / x := by
  rw [approximant_one]; simp [erfcCFNum, erfcCFDen]

/--
@isnad1 id=eq.0h1v.s6.96516cd75da9 from=translated src=- shape=617dee2c vocab=58f2587f
-/
theorem erfcCF_approximant_two (x : ℝ) :
    approximant erfcCFNum (erfcCFDen x) 2 = 1 / (x + 1 / 2 / x) := by
  rw [approximant_succ, approximant_one]; simp [erfcCFNum, erfcCFDen]; norm_num

/-- Consistency with the asymptotic expansion: the second approximant of (4.40), times the
prefactor `e^(−x²)/√π`, lies in the bracket `[L(1 − 1/(2x²)), L]` of (4.37), `L = e^(−x²)/(x√π)`.
@isnad1 id=and.1h1v.s8.cd7bee54d437 from=translated src=- shape=6b257b3d vocab=b01f4521
-/
theorem erfcCF_approximant_two_mem {x : ℝ} (hx : 0 < x) :
    Real.exp (-x ^ 2) / (x * Real.sqrt Real.pi) * (1 - 1 / (2 * x ^ 2))
        ≤ Real.exp (-x ^ 2) / Real.sqrt Real.pi * approximant erfcCFNum (erfcCFDen x) 2 ∧
      Real.exp (-x ^ 2) / Real.sqrt Real.pi * approximant erfcCFNum (erfcCFDen x) 2
        ≤ Real.exp (-x ^ 2) / (x * Real.sqrt Real.pi) := by
  rw [erfcCF_approximant_two]
  have hπ : 0 < Real.sqrt Real.pi := Real.sqrt_pos.mpr Real.pi_pos
  have hL : 0 < Real.exp (-x ^ 2) / (x * Real.sqrt Real.pi) := by positivity
  have hval : Real.exp (-x ^ 2) / Real.sqrt Real.pi * (1 / (x + 1 / 2 / x))
      = Real.exp (-x ^ 2) / (x * Real.sqrt Real.pi) * (2 * x ^ 2 / (2 * x ^ 2 + 1)) := by
    field_simp
  rw [hval]
  have hfrac1 : 1 - 1 / (2 * x ^ 2) ≤ 2 * x ^ 2 / (2 * x ^ 2 + 1) := by
    rw [show (1 : ℝ) - 1 / (2 * x ^ 2) = (2 * x ^ 2 - 1) / (2 * x ^ 2) by field_simp,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hfrac2 : 2 * x ^ 2 / (2 * x ^ 2 + 1) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  constructor
  · exact mul_le_mul_of_nonneg_left hfrac1 hL.le
  · calc Real.exp (-x ^ 2) / (x * Real.sqrt Real.pi) * (2 * x ^ 2 / (2 * x ^ 2 + 1))
        ≤ Real.exp (-x ^ 2) / (x * Real.sqrt Real.pi) * 1 := mul_le_mul_of_nonneg_left hfrac2 hL.le
      _ = Real.exp (-x ^ 2) / (x * Real.sqrt Real.pi) := mul_one _

end BZ

end Azurite
