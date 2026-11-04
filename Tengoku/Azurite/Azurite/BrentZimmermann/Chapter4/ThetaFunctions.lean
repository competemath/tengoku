/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

import Tengoku.Azurite.Azurite.BrentZimmermann.Chapter4.AGMLog

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Brent–Zimmermann §4.8.3: Theta functions

For `|q| < 1`,

  `θ₂(q) = ∑_{n∈ℤ} q^((n+1/2)²) = 2 q^(1/4) ∑_{n≥0} q^(n(n+1))`,                        (4.74)
  `θ₃(q) = ∑_{n∈ℤ} q^(n²) = 1 + 2 ∑_{n≥1} q^(n²)`,                                      (4.75)
  `θ₄(q) = θ₃(−q) = 1 + 2 ∑_{n≥1} (−1)^n q^(n²)`.                                       (4.76)

The series are sparse, so `θ₂`, `θ₃` are cheap for small `q`.  The identities

  `(θ₃²(q) + θ₄²(q))/2 = θ₃²(q²)`,  `θ₃(q) θ₄(q) = θ₄²(q²)`

show that `(θ₃²(q), θ₄²(q)) ↦ (θ₃²(q²), θ₄²(q²))` is one AGM step, so
`AGM(θ₃²(q), θ₄²(q)) = AGM(θ₃²(q^(2^k)), θ₄²(q^(2^k))) = … = 1`: the AGM iteration is
parameterized by `(θ₃²(q^(2^k)), θ₄²(q^(2^k)))`.  Scaling gives `AGM(1, k') = 1/θ₃²(q)` for
`k' = θ₄²(q)/θ₃²(q)` (equivalently `k = θ₂²(q)/θ₃²(q)` by Jacobi's `θ₂⁴ + θ₄⁴ = θ₃⁴`), and with
(4.68),

  `K(k) = (π/2) θ₃²(q)`;                                                                      (4.77)

`q` is the *nome* of `k`.  The inverse formula is `q = exp(−π K'(k)/K(k))`, i.e.
`ln(1/q) = π K'(k)/K(k)` (4.78), and substituting (4.68), (4.77) gives Sasaki–Kanada's
`ln(1/q) = π/AGM(θ₂²(q), θ₃²(q))` (4.79).

What is formalized (real `q`):

* `theta3 q = ∑_{m∈ℤ} q^(m²)`, `theta4 q = ∑_{m∈ℤ} (−1)^m q^(m²)` (as `ℤ`-sums with `m.natAbs`),
  `theta2 q = 2 q^(1/4) ∑_{n≥0} q^(n(n+1))`; summability for `|q| < 1`; the one-sided forms
  `theta3_eq_one_add`, `theta4_eq_one_add`, `theta4_eq_theta3_neg` (`θ₄(q) = θ₃(−q)`), and the
  `ℤ`-form of (4.74), `theta2_eq_tsum_int` (`0 < q < 1`).
* The two AGM identities `theta3_sq_add_theta4_sq` and `theta3_mul_theta4` (for `|q| < 1`), by
  splitting the double series over `ℤ²` by the parity of `m + n` through the bijections
  `(a, b) ↦ (a+b, a−b)` and `(a, b) ↦ (a+b+1, a−b)` (`evenEquiv`, `oddEquiv`,
  `tsum_prod_int_split`), the odd part vanishing by the involution `(a, b) ↦ (a, −b−1)`.
* Bounds for `0 ≤ q < 1`: `one_le_theta3`, `theta3_sub_one_le` (`≤ 2q/(1−q)`),
  `one_sub_theta4_le`, `theta4_le_theta3`, `theta4_nonneg`, `theta4_pos` (via the identity and the
  limit along `q^(2^k)`).
* The AGM parameterization: `AGM_theta_step` (`AGM(θ₃²(q), θ₄²(q)) = AGM(θ₃²(q²), θ₄²(q²))`),
  `AGM_theta_pow` and `AGM_theta` (`AGM(θ₃²(q), θ₄²(q)) = 1`), then `AGM_one_nomeK'`
  (`AGM(1, k') = 1/θ₃²(q)`, `k' = θ₄²/θ₃²`) and (4.77) in the form
  `ellipticK_nome : K(√(1 − k'²)) = (π/2) θ₃²(q)`.
* `nomeK q = θ₂²(q)/θ₃²(q)` and `nomeK' q = θ₄²(q)/θ₃²(q)` as definitions.

Not formalized: Jacobi's `θ₂⁴ + θ₄⁴ = θ₃⁴` (so `k = θ₂²/θ₃²` is only a definition here), the
inverse nome formula (4.78) (a modular transformation; Mathlib has `jacobiTheta_S_smul` for `θ₃`,
to be connected later), Sasaki–Kanada (4.79), and the remark that AGM-based theta computation
would be circular.
-/

namespace Azurite

namespace BZ

open Filter Topology Set

/-! ### Definitions and summability -/

/-- `θ₃(q) = ∑_{m ∈ ℤ} q^(m²)`.-/
noncomputable def theta3 (q : ℝ) : ℝ := ∑' m : ℤ, q ^ (m.natAbs ^ 2)

/-- `θ₄(q) = ∑_{m ∈ ℤ} (−1)^m q^(m²)`.-/
noncomputable def theta4 (q : ℝ) : ℝ := ∑' m : ℤ, (-1) ^ m.natAbs * q ^ (m.natAbs ^ 2)

/-- `θ₂(q) = 2 q^(1/4) ∑_{n ≥ 0} q^(n(n+1))` (for `q ≥ 0`).-/
noncomputable def theta2 (q : ℝ) : ℝ := 2 * q ^ (1 / 4 : ℝ) * ∑' n : ℕ, q ^ (n * (n + 1))

variable {q : ℝ}

/-- `|q|^(m²) ≤ |q|^|m|` for `|q| ≤ 1`.
@isnad1 id=le.1h2v.s6.ddd4d5a01c9f from=translated src=- shape=79f6bec6 vocab=b35db661
-/
theorem abs_pow_natAbs_sq_le (hq : |q| < 1) (m : ℤ) :
    |q ^ (m.natAbs ^ 2)| ≤ |q| ^ m.natAbs := by
  rw [abs_pow]
  exact pow_le_pow_of_le_one (abs_nonneg q) hq.le (Nat.le_self_pow two_ne_zero _)

/--
@isnad1 id=summable.1h1v.s5.5cb5523bfe6a from=translated src=- shape=91f41af0 vocab=70761d17
-/
theorem summable_abs_pow_natAbs (hq : |q| < 1) : Summable fun m : ℤ => |q| ^ m.natAbs := by
  have h := Summable.int_rec (f := fun n : ℕ => |q| ^ n) (g := fun n : ℕ => |q| ^ (n + 1))
    (summable_geometric_of_lt_one (abs_nonneg q) hq)
    ((summable_nat_add_iff (f := fun n : ℕ => |q| ^ n) 1).mpr
      (summable_geometric_of_lt_one (abs_nonneg q) hq))
  refine h.congr fun m => ?_
  rcases m with n | n <;> rfl

/--
@isnad1 id=summable.1h1v.s5.f390cab063e2 from=translated src=- shape=43a1520e vocab=70761d17
-/
theorem summable_theta3_term (hq : |q| < 1) : Summable fun m : ℤ => q ^ (m.natAbs ^ 2) :=
  (summable_abs_pow_natAbs hq).of_norm_bounded fun m => by
    rw [Real.norm_eq_abs]; exact abs_pow_natAbs_sq_le hq m

/--
@isnad1 id=summable.1h1v.s6.af9e14c7be67 from=translated src=- shape=da9f2a00 vocab=15599a61
-/
theorem summable_theta4_term (hq : |q| < 1) :
    Summable fun m : ℤ => (-1) ^ m.natAbs * q ^ (m.natAbs ^ 2) :=
  (summable_abs_pow_natAbs hq).of_norm_bounded fun m => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_pow_natAbs_sq_le hq m

/--
@isnad1 id=summable.1h1v.s6.51feef579a39 from=translated src=- shape=22143cb8 vocab=4e0b428d
-/
theorem summable_norm_theta3_term (hq : |q| < 1) :
    Summable fun m : ℤ => ‖q ^ (m.natAbs ^ 2)‖ :=
  (summable_abs_pow_natAbs hq).of_nonneg_of_le (fun _ => norm_nonneg _) fun m => by
    rw [Real.norm_eq_abs]; exact abs_pow_natAbs_sq_le hq m

/--
@isnad1 id=summable.1h1v.s6.135c46890cee from=translated src=- shape=7d08790b vocab=d9e5bbca
-/
theorem summable_norm_theta4_term (hq : |q| < 1) :
    Summable fun m : ℤ => ‖(-1) ^ m.natAbs * q ^ (m.natAbs ^ 2)‖ :=
  (summable_abs_pow_natAbs hq).of_nonneg_of_le (fun _ => norm_nonneg _) fun m => by
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul]
    exact abs_pow_natAbs_sq_le hq m

/-! ### One-sided forms -/

/--
@isnad1 id=summable.1h1v.s6.b30716307d7a from=translated src=- shape=9fa54e6d vocab=ec801cdf
-/
theorem summable_pow_succ_sq (hq : |q| < 1) : Summable fun n : ℕ => q ^ ((n + 1) ^ 2) :=
  ((summable_nat_add_iff (f := fun n : ℕ => |q| ^ n) 1).mpr
    (summable_geometric_of_lt_one (abs_nonneg q) hq)).of_norm_bounded fun n => by
      rw [Real.norm_eq_abs, abs_pow]
      exact pow_le_pow_of_le_one (abs_nonneg q) hq.le (Nat.le_self_pow two_ne_zero _)

/-- (4.75): `θ₃(q) = 1 + 2 ∑_{n ≥ 1} q^(n²)`.
@isnad1 id=eq.1h1v.s6.301d72a7cfde from=translated src=- shape=dfb4b268 vocab=fd051181
-/
theorem theta3_eq_one_add (hq : |q| < 1) : theta3 q = 1 + 2 * ∑' n : ℕ, q ^ ((n + 1) ^ 2) := by
  have hf : Summable fun n : ℕ => q ^ (n ^ 2) :=
    (summable_theta3_term hq).comp_injective (i := fun n : ℕ => (n : ℤ)) Int.ofNat_injective
  have hg := summable_pow_succ_sq hq
  have heq : (fun m : ℤ => q ^ (m.natAbs ^ 2))
      = Int.rec (fun n : ℕ => q ^ (n ^ 2)) (fun n : ℕ => q ^ ((n + 1) ^ 2)) := by
    funext m; rcases m with n | n <;> rfl
  unfold theta3
  rw [heq, tsum_int_rec hf hg, hf.tsum_eq_zero_add]
  ring

/-- (4.76): `θ₄(q) = 1 + 2 ∑_{n ≥ 1} (−1)^n q^(n²)`.
@isnad1 id=eq.1h1v.s7.348d86e8b83e from=translated src=- shape=063af113 vocab=ab7f62cf
-/
theorem theta4_eq_one_add (hq : |q| < 1) :
    theta4 q = 1 + 2 * ∑' n : ℕ, (-1) ^ (n + 1) * q ^ ((n + 1) ^ 2) := by
  have hf : Summable fun n : ℕ => (-1 : ℝ) ^ n * q ^ (n ^ 2) :=
    (summable_theta4_term hq).comp_injective (i := fun n : ℕ => (n : ℤ)) Int.ofNat_injective
  have hg : Summable fun n : ℕ => (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2) :=
    (summable_theta4_term hq).comp_injective (i := fun n : ℕ => Int.negSucc n)
      fun a b h => Int.negSucc.inj h
  have heq : (fun m : ℤ => (-1 : ℝ) ^ m.natAbs * q ^ (m.natAbs ^ 2))
      = Int.rec (fun n : ℕ => (-1 : ℝ) ^ n * q ^ (n ^ 2))
        (fun n : ℕ => (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2)) := by
    funext m; rcases m with n | n <;> rfl
  unfold theta4
  rw [heq, tsum_int_rec hf hg, hf.tsum_eq_zero_add]
  simp only [pow_zero, one_mul]
  ring

/-- `θ₄(q) = θ₃(−q)`.
@isnad1 id=eq.0h1v.s3.0e1e615b7237 from=translated src=- shape=98cb13d8 vocab=d3674eda
-/
theorem theta4_eq_theta3_neg (q : ℝ) : theta4 q = theta3 (-q) := by
  unfold theta3 theta4
  refine tsum_congr fun m => ?_
  rw [neg_pow q]
  congr 1
  rcases Nat.even_or_odd m.natAbs with h | h
  · rw [h.neg_one_pow, (Nat.even_pow.mpr ⟨h, two_ne_zero⟩).neg_one_pow]
  · rw [h.neg_one_pow, (Odd.pow h).neg_one_pow]

/--
@isnad1 id=summable.2h1v.s6.435598279027 from=translated src=- shape=6e3a9741 vocab=6c0d0766
-/
theorem summable_pow_mul_succ (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable fun n : ℕ => q ^ (n * (n + 1)) :=
  (summable_geometric_of_lt_one hq0 hq1).of_nonneg_of_le (fun n => by positivity) fun n =>
    pow_le_pow_of_le_one hq0 hq1.le (Nat.le_mul_of_pos_right n n.succ_pos)

/-- (4.74) in the `ℤ`-form: `θ₂(q) = ∑_{n ∈ ℤ} q^((n + 1/2)²)` for `0 < q < 1`.
@isnad1 id=eq.2h1v.s6.446dc1df82dc from=translated src=- shape=f45cd917 vocab=e8bd8088
-/
theorem theta2_eq_tsum_int (hq0 : 0 < q) (hq1 : q < 1) :
    theta2 q = ∑' n : ℤ, q ^ (((n : ℝ) + 1 / 2) ^ 2) := by
  have hterm : ∀ n : ℕ, q ^ (((n : ℝ) + 1 / 2) ^ 2) = q ^ (1 / 4 : ℝ) * q ^ (n * (n + 1)) := by
    intro n
    rw [show ((n : ℝ) + 1 / 2) ^ 2 = 1 / 4 + ((n * (n + 1) : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_add hq0, Real.rpow_natCast]
  have hs := summable_pow_mul_succ hq0.le hq1
  have hf : Summable fun n : ℕ => q ^ (((n : ℝ) + 1 / 2) ^ 2) := by
    simp_rw [hterm]; exact hs.mul_left _
  have hg : Summable fun n : ℕ => q ^ (((Int.negSucc n : ℤ) : ℝ) + 1 / 2) ^ 2 := by
    refine hf.congr fun n => ?_
    rw [Int.cast_negSucc]; congr 1; push_cast; ring
  have heq : (fun n : ℤ => q ^ (((n : ℝ) + 1 / 2) ^ 2))
      = Int.rec (fun n : ℕ => q ^ (((n : ℝ) + 1 / 2) ^ 2))
        (fun n : ℕ => q ^ (((Int.negSucc n : ℤ) : ℝ) + 1 / 2) ^ 2) := by
    funext n; rcases n with n | n <;> rfl
  rw [heq, tsum_int_rec hf hg]
  have h2 : ∑' n : ℕ, q ^ (((Int.negSucc n : ℤ) : ℝ) + 1 / 2) ^ 2
      = ∑' n : ℕ, q ^ (((n : ℝ) + 1 / 2) ^ 2) :=
    tsum_congr fun n => by rw [Int.cast_negSucc]; congr 1; push_cast; ring
  rw [h2]
  simp_rw [hterm]
  rw [tsum_mul_left]
  unfold theta2
  ring

/-! ### The parity split of `ℤ × ℤ` -/

/-- Pairs with `m + n` even.-/
def evenPairs : Set (ℤ × ℤ) := {p | Even (p.1 + p.2)}

/-- `(a, b) ↦ (a + b, a − b)` parameterizes the even pairs.-/
def evenEquiv : ℤ × ℤ ≃ evenPairs where
  toFun p := ⟨(p.1 + p.2, p.1 - p.2), ⟨p.1, by ring⟩⟩
  invFun p := ((p.1.1 + p.1.2) / 2, (p.1.1 - p.1.2) / 2)
  left_inv p := by
    obtain ⟨a, b⟩ := p
    show ((a + b + (a - b)) / 2, (a + b - (a - b)) / 2) = (a, b)
    ext <;> simp only <;> omega
  right_inv p := by
    obtain ⟨⟨m, n⟩, h⟩ := p
    have h' : (m + n) % 2 = 0 := Int.even_iff.mp h
    ext <;> simp only <;> omega

/-- `(a, b) ↦ (a + b + 1, a − b)` parameterizes the odd pairs.-/
def oddEquiv : ℤ × ℤ ≃ (evenPairsᶜ : Set (ℤ × ℤ)) where
  toFun p := ⟨(p.1 + p.2 + 1, p.1 - p.2), by
    show ¬ Even (p.1 + p.2 + 1 + (p.1 - p.2))
    rw [Int.not_even_iff_odd]
    exact ⟨p.1, by ring⟩⟩
  invFun p := ((p.1.1 + p.1.2 - 1) / 2, (p.1.1 - p.1.2 - 1) / 2)
  left_inv p := by
    obtain ⟨a, b⟩ := p
    show ((a + b + 1 + (a - b) - 1) / 2, (a + b + 1 - (a - b) - 1) / 2) = (a, b)
    ext <;> simp only <;> omega
  right_inv p := by
    obtain ⟨⟨m, n⟩, h⟩ := p
    have h' : (m + n) % 2 = 1 := by
      have : ¬ Even (m + n) := h
      rw [Int.not_even_iff_odd] at this
      exact Int.odd_iff.mp this
    ext <;> simp only <;> omega

/-- A summable double series over `ℤ²` splits by the parity of `m + n`.
@isnad1 id=eq.1h1v.s7.fe67db9fb0cd from=translated src=- shape=e990397f vocab=966dbb1a
-/
theorem tsum_prod_int_split {f : ℤ × ℤ → ℝ} (hf : Summable f) :
    ∑' p, f p = ∑' p : ℤ × ℤ, f (p.1 + p.2, p.1 - p.2)
      + ∑' p : ℤ × ℤ, f (p.1 + p.2 + 1, p.1 - p.2) := by
  rw [← Summable.tsum_add_tsum_compl (s := evenPairs) (hf.subtype _) (hf.subtype _),
    ← evenEquiv.tsum_eq, ← oddEquiv.tsum_eq]
  rfl

/-- The involution `(a, b) ↦ (a, −b − 1)`.-/
def flipEquiv : ℤ × ℤ ≃ ℤ × ℤ where
  toFun p := (p.1, -p.2 - 1)
  invFun p := (p.1, -p.2 - 1)
  left_inv p := Prod.ext rfl (by show -(-p.2 - 1) - 1 = p.2; omega)
  right_inv p := Prod.ext rfl (by show -(-p.2 - 1) - 1 = p.2; omega)

/-- A series that is negated by an involution sums to zero.
@isnad1 id=eq.1h1v.s6.a4b0e3039f54 from=translated src=- shape=cf2700a2 vocab=acbec171
-/
theorem tsum_eq_zero_of_neg_comp {g : ℤ × ℤ → ℝ} (h : ∀ p, g (flipEquiv p) = -g p) :
    ∑' p, g p = 0 := by
  have h1 : ∑' p, g p = ∑' p, g (flipEquiv p) := (flipEquiv.tsum_eq g).symm
  have h2 : ∑' p, g (flipEquiv p) = -∑' p, g p := by
    rw [show (fun p => g (flipEquiv p)) = fun p => -g p from funext h, tsum_neg]
  linarith

/-! ### Parity and exponent identities -/

/--
@isnad1 id=eq.0h2v.s6.7994d426286c from=translated src=- shape=40ce51ed vocab=30930677
-/
theorem neg_one_pow_natAbs_mul (m n : ℤ) :
    (-1 : ℝ) ^ m.natAbs * (-1) ^ n.natAbs = if Even (m + n) then 1 else -1 := by
  rw [← pow_add]
  have : Even (m.natAbs + n.natAbs) ↔ Even (m + n) := by
    rw [Nat.even_add, Int.natAbs_even, Int.natAbs_even, Int.even_add]
  split_ifs with h
  · exact (this.mpr h).neg_one_pow
  · exact (Nat.not_even_iff_odd.mp (this.not.mpr h)).neg_one_pow

/--
@isnad1 id=eq.0h2v.s6.980d212348e4 from=translated src=- shape=ac6afc54 vocab=7c1bdc00
-/
theorem natAbs_sq_add_sub (a b : ℤ) :
    (a + b).natAbs ^ 2 + (a - b).natAbs ^ 2 = 2 * (a.natAbs ^ 2 + b.natAbs ^ 2) := by
  zify
  simp only [sq_abs]
  ring

/-! ### The two AGM identities -/

/-- `θ₃(q) θ₄(q) = θ₄(q²)²`.
@isnad1 id=eq.1h1v.s6.625b51208b7f from=translated src=- shape=b36851df vocab=271cdf52
-/
theorem theta3_mul_theta4 (hq : |q| < 1) : theta3 q * theta4 q = theta4 (q ^ 2) ^ 2 := by
  have hq2 : |q ^ 2| < 1 := by rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg q) hq two_ne_zero
  unfold theta3 theta4
  rw [tsum_mul_tsum_of_summable_norm (summable_norm_theta3_term hq) (summable_norm_theta4_term hq),
    sq, tsum_mul_tsum_of_summable_norm (summable_norm_theta4_term hq2)
      (summable_norm_theta4_term hq2)]
  have hs := summable_mul_of_summable_norm (summable_norm_theta3_term hq)
    (summable_norm_theta4_term hq)
  rw [tsum_prod_int_split hs]
  have hodd : ∑' p : ℤ × ℤ, q ^ ((p.1 + p.2 + 1).natAbs ^ 2)
      * ((-1) ^ (p.1 - p.2).natAbs * q ^ ((p.1 - p.2).natAbs ^ 2)) = 0 := by
    refine tsum_eq_zero_of_neg_comp fun p => ?_
    obtain ⟨a, b⟩ := p
    simp only [flipEquiv, Equiv.coe_fn_mk]
    rw [show a + (-b - 1) + 1 = a - b by ring, show a - (-b - 1) = a + b + 1 by ring]
    have h := neg_one_pow_natAbs_mul (a + b + 1) (a - b)
    rw [ite_eq_right (by rw [Int.not_even_iff_odd]; exact ⟨a, by ring⟩)] at h
    have hB : ((-1 : ℝ) ^ (a - b).natAbs) ^ 2 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
    linear_combination (q ^ ((a - b).natAbs ^ 2) * q ^ ((a + b + 1).natAbs ^ 2)
      * (-1 : ℝ) ^ (a - b).natAbs) * h
      - (q ^ ((a - b).natAbs ^ 2) * q ^ ((a + b + 1).natAbs ^ 2)
        * (-1 : ℝ) ^ (a + b + 1).natAbs) * hB
  rw [hodd, add_zero]
  refine tsum_congr fun p => ?_
  obtain ⟨a, b⟩ := p
  simp only
  have hpar : (-1 : ℝ) ^ (a - b).natAbs = (-1) ^ a.natAbs * (-1) ^ b.natAbs := by
    rw [neg_one_pow_natAbs_mul]
    by_cases h : Even (a + b)
    · rw [ite_eq_left h]
      exact (Int.natAbs_even.mpr (Int.even_sub.mpr (Int.even_add.mp h))).neg_one_pow
    · rw [ite_eq_right h]
      have : Odd (a - b).natAbs := by
        rw [Int.natAbs_odd, ← Int.not_even_iff_odd, Int.even_sub]
        rwa [Int.even_add] at h
      exact this.neg_one_pow
  have hexp : q ^ ((a + b).natAbs ^ 2) * q ^ ((a - b).natAbs ^ 2)
      = (q ^ 2) ^ (a.natAbs ^ 2) * (q ^ 2) ^ (b.natAbs ^ 2) := by
    rw [← pow_add, natAbs_sq_add_sub, ← pow_mul, ← pow_mul, ← pow_add, mul_add]
  rw [hpar]
  linear_combination ((-1 : ℝ) ^ a.natAbs * (-1) ^ b.natAbs) * hexp

/-- `(θ₃(q)² + θ₄(q)²)/2 = θ₃(q²)²`.
@isnad1 id=eq.1h1v.s6.b72eb2414f71 from=translated src=- shape=9b4481ee vocab=9b5ad54a
-/
theorem theta3_sq_add_theta4_sq (hq : |q| < 1) :
    (theta3 q ^ 2 + theta4 q ^ 2) / 2 = theta3 (q ^ 2) ^ 2 := by
  have hq2 : |q ^ 2| < 1 := by rw [abs_pow]; exact pow_lt_one₀ (abs_nonneg q) hq two_ne_zero
  unfold theta3 theta4
  rw [sq, sq, sq, tsum_mul_tsum_of_summable_norm (summable_norm_theta3_term hq)
    (summable_norm_theta3_term hq), tsum_mul_tsum_of_summable_norm (summable_norm_theta4_term hq)
    (summable_norm_theta4_term hq), tsum_mul_tsum_of_summable_norm
    (summable_norm_theta3_term hq2) (summable_norm_theta3_term hq2)]
  have hs3 := summable_mul_of_summable_norm (summable_norm_theta3_term hq)
    (summable_norm_theta3_term hq)
  have hs4 := summable_mul_of_summable_norm (summable_norm_theta4_term hq)
    (summable_norm_theta4_term hq)
  rw [← hs3.tsum_add hs4, tsum_prod_int_split (hs3.add hs4)]
  have hodd : ∑' p : ℤ × ℤ, (q ^ ((p.1 + p.2 + 1).natAbs ^ 2) * q ^ ((p.1 - p.2).natAbs ^ 2)
      + (-1) ^ (p.1 + p.2 + 1).natAbs * q ^ ((p.1 + p.2 + 1).natAbs ^ 2)
        * ((-1) ^ (p.1 - p.2).natAbs * q ^ ((p.1 - p.2).natAbs ^ 2))) = 0 := by
    refine (tsum_congr fun p => ?_).trans (tsum_zero (α := ℝ) (β := ℤ × ℤ))
    obtain ⟨a, b⟩ := p
    simp only
    have h := neg_one_pow_natAbs_mul (a + b + 1) (a - b)
    rw [ite_eq_right (by rw [Int.not_even_iff_odd]; exact ⟨a, by ring⟩)] at h
    linear_combination (q ^ ((a + b + 1).natAbs ^ 2) * q ^ ((a - b).natAbs ^ 2)) * h
  rw [hodd, add_zero, div_eq_iff (two_ne_zero' ℝ), ← tsum_mul_right]
  refine tsum_congr fun p => ?_
  obtain ⟨a, b⟩ := p
  simp only
  have h := neg_one_pow_natAbs_mul (a + b) (a - b)
  rw [ite_eq_left ⟨a, by ring⟩] at h
  have hexp : q ^ ((a + b).natAbs ^ 2) * q ^ ((a - b).natAbs ^ 2)
      = (q ^ 2) ^ (a.natAbs ^ 2) * (q ^ 2) ^ (b.natAbs ^ 2) := by
    rw [← pow_add, natAbs_sq_add_sub, ← pow_mul, ← pow_mul, ← pow_add, mul_add]
  linear_combination (q ^ ((a + b).natAbs ^ 2) * q ^ ((a - b).natAbs ^ 2)) * h + 2 * hexp

/-! ### Bounds for `0 ≤ q < 1` -/

/--
@isnad1 id=le.2h1v.s6.719d86e76b3c from=translated src=- shape=bdadff7d vocab=b21514c9
-/
theorem tsum_pow_succ_sq_le (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ∑' n : ℕ, q ^ ((n + 1) ^ 2) ≤ q / (1 - q) := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have hg : Summable fun n : ℕ => q ^ (n + 1) :=
    (summable_nat_add_iff (f := fun n : ℕ => q ^ n) 1).mpr (summable_geometric_of_lt_one hq0 hq1)
  calc ∑' n : ℕ, q ^ ((n + 1) ^ 2) ≤ ∑' n : ℕ, q ^ (n + 1) :=
        (summable_pow_succ_sq hq).tsum_le_tsum (fun n =>
          pow_le_pow_of_le_one hq0 hq1.le (Nat.le_self_pow two_ne_zero _)) hg
    _ = q * ∑' n : ℕ, q ^ n := by simp_rw [pow_succ, mul_comm (q ^ _) q]; exact tsum_mul_left
    _ = q / (1 - q) := by rw [tsum_geometric_of_lt_one hq0 hq1, div_eq_mul_inv]

/--
@isnad1 id=le.1h1v.s6.3ff2842ac81b from=translated src=- shape=373b6479 vocab=dd481a4c
-/
theorem tsum_pow_succ_sq_nonneg (hq0 : 0 ≤ q) : 0 ≤ ∑' n : ℕ, q ^ ((n + 1) ^ 2) :=
  tsum_nonneg fun n => by positivity

/--
@isnad1 id=le.2h1v.s5.6ea7102b1f23 from=translated src=- shape=91c05246 vocab=494980cb
-/
theorem one_le_theta3 (hq0 : 0 ≤ q) (hq1 : q < 1) : 1 ≤ theta3 q := by
  rw [theta3_eq_one_add (by rw [abs_of_nonneg hq0]; exact hq1)]
  linarith [tsum_pow_succ_sq_nonneg hq0]

/--
@isnad1 id=lt.2h1v.s5.a96494d7bdcc from=translated src=- shape=536e06c9 vocab=494980cb
-/
theorem theta3_pos (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < theta3 q :=
  lt_of_lt_of_le one_pos (one_le_theta3 hq0 hq1)

/--
@isnad1 id=le.2h1v.s6.aa3574b337d5 from=translated src=- shape=12092055 vocab=040996dd
-/
theorem theta3_sub_one_le (hq0 : 0 ≤ q) (hq1 : q < 1) : theta3 q - 1 ≤ 2 * q / (1 - q) := by
  rw [theta3_eq_one_add (by rw [abs_of_nonneg hq0]; exact hq1)]
  have h := tsum_pow_succ_sq_le hq0 hq1
  have e : 2 * q / (1 - q) = 2 * (q / (1 - q)) := by ring
  rw [e]
  linarith

/--
@isnad1 id=le.2h1v.s7.0eb7cca9cd0c from=translated src=- shape=c95394f5 vocab=51d0f623
-/
theorem abs_tsum_neg_one_pow_le (hq0 : 0 ≤ q) (hq1 : q < 1) :
    |∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2)| ≤ ∑' n : ℕ, q ^ ((n + 1) ^ 2) := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have hs : Summable fun n : ℕ => ‖(-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2)‖ := by
    refine (summable_pow_succ_sq hq).congr fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg (by positivity)]
  calc |∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2)|
      = ‖∑' n : ℕ, (-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2)‖ := (Real.norm_eq_abs _).symm
    _ ≤ ∑' n : ℕ, ‖(-1 : ℝ) ^ (n + 1) * q ^ ((n + 1) ^ 2)‖ := norm_tsum_le_tsum_norm hs
    _ = ∑' n : ℕ, q ^ ((n + 1) ^ 2) := tsum_congr fun n => by
        rw [Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
          abs_of_nonneg (by positivity)]

/--
@isnad1 id=le.2h1v.s6.79386d1707ad from=translated src=- shape=91a62a31 vocab=4e752c06
-/
theorem one_sub_theta4_le (hq0 : 0 ≤ q) (hq1 : q < 1) : 1 - theta4 q ≤ 2 * q / (1 - q) := by
  rw [theta4_eq_one_add (by rw [abs_of_nonneg hq0]; exact hq1)]
  have h1 := abs_tsum_neg_one_pow_le hq0 hq1
  have h2 := tsum_pow_succ_sq_le hq0 hq1
  rw [abs_le] at h1
  have e : 2 * q / (1 - q) = 2 * (q / (1 - q)) := by ring
  rw [e]
  linarith [h1.1]

/--
@isnad1 id=le.2h1v.s4.72130df688e2 from=translated src=- shape=3abebf8d vocab=92cb3a70
-/
theorem theta4_le_theta3 (hq0 : 0 ≤ q) (hq1 : q < 1) : theta4 q ≤ theta3 q := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  unfold theta3 theta4
  refine (summable_theta4_term hq).tsum_le_tsum (fun m => ?_) (summable_theta3_term hq)
  rcases Nat.even_or_odd m.natAbs with h | h
  · rw [h.neg_one_pow, one_mul]
  · rw [h.neg_one_pow, neg_one_mul]
    linarith [pow_nonneg hq0 (m.natAbs ^ 2)]

/--
@isnad1 id=le.2h1v.s5.6251e8f3dece from=translated src=- shape=91c05246 vocab=0a62633a
-/
theorem theta4_nonneg (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 ≤ theta4 q := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have h := theta3_mul_theta4 hq
  have h3 := theta3_pos hq0 hq1
  have hprod : 0 ≤ theta3 q * theta4 q := by rw [h]; positivity
  by_contra hneg
  have hneg' : theta4 q < 0 := lt_of_not_ge hneg
  nlinarith [mul_pos h3 (neg_pos.mpr hneg')]

/--
@isnad1 id=ne.2h1v.s5.d535642e192d from=translated src=- shape=50c3c46f vocab=45c20023
-/
theorem theta4_ne_zero_of_sq (hq : |q| < 1) (h : theta4 (q ^ 2) ≠ 0) : theta4 q ≠ 0 := by
  intro h0
  have := theta3_mul_theta4 hq
  rw [h0, mul_zero] at this
  exact h (pow_eq_zero_iff two_ne_zero |>.mp this.symm)

/-- `θ₄(r) > 0` for `0 ≤ r < 1/3`, from the series bound.
@isnad1 id=lt.2h1v.s5.fb0fe848a316 from=translated src=- shape=a515fac2 vocab=f86c8ecd
-/
theorem theta4_pos_of_lt_third (hr0 : 0 ≤ q) (hr : q < 1 / 3) : 0 < theta4 q := by
  have h := one_sub_theta4_le hr0 (by linarith)
  have : 2 * q / (1 - q) < 1 := by rw [div_lt_one (by linarith)]; linarith
  linarith

/--
@isnad1 id=lt.2h1v.s5.ddfcbe0e4f39 from=translated src=- shape=536e06c9 vocab=0a62633a
-/
theorem theta4_pos (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < theta4 q := by
  -- `0 < θ₄(q^(2^k))` propagates down to `0 < θ₄(q)`
  have key : ∀ k : ℕ, ∀ q : ℝ, 0 ≤ q → q < 1 → 0 < theta4 (q ^ 2 ^ k) → 0 < theta4 q := by
    intro k
    induction k with
    | zero => intro q _ _ h; simpa using h
    | succ k ih =>
      intro q hq0 hq1 h
      have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
      have h2 : 0 < theta4 (q ^ 2) := by
        refine ih (q ^ 2) (by positivity) (pow_lt_one₀ hq0 hq1 two_ne_zero) ?_
        rwa [← pow_mul, ← pow_succ']
      exact lt_of_le_of_ne (theta4_nonneg hq0 hq1)
        (theta4_ne_zero_of_sq hq h2.ne').symm
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (by norm_num : (0 : ℝ) < 1 / 3) hq1
  refine key n q hq0 hq1 (theta4_pos_of_lt_third (by positivity) ?_)
  calc q ^ 2 ^ n ≤ q ^ n := pow_le_pow_of_le_one hq0 hq1.le Nat.lt_two_pow_self.le
    _ < 1 / 3 := hn

/-! ### The AGM parameterization -/

/-- One AGM step on `(θ₃²(q), θ₄²(q))` gives `(θ₃²(q²), θ₄²(q²))`.
@isnad1 id=eq.2h1v.s7.ea0603998d83 from=translated src=- shape=6aa828de vocab=13a4ee09
-/
theorem AGM_theta_step (hq0 : 0 ≤ q) (hq1 : q < 1) :
    AGM (theta3 q ^ 2) (theta4 q ^ 2) = AGM (theta3 (q ^ 2) ^ 2) (theta4 (q ^ 2) ^ 2) := by
  have hq : |q| < 1 := by rw [abs_of_nonneg hq0]; exact hq1
  have h3 := theta3_pos hq0 hq1
  have h4 := theta4_pos hq0 hq1
  rw [AGM_step (by positivity) (by positivity), theta3_sq_add_theta4_sq hq,
    show theta3 q ^ 2 * theta4 q ^ 2 = (theta3 q * theta4 q) ^ 2 by ring,
    Real.sqrt_sq (by positivity), theta3_mul_theta4 hq]

/--
@isnad1 id=eq.2h2v.s7.9690ed503e19 from=translated src=- shape=29d25238 vocab=13a4ee09
-/
theorem AGM_theta_pow (hq0 : 0 ≤ q) (hq1 : q < 1) (k : ℕ) :
    AGM (theta3 q ^ 2) (theta4 q ^ 2) = AGM (theta3 (q ^ 2 ^ k) ^ 2) (theta4 (q ^ 2 ^ k) ^ 2) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [ih, AGM_theta_step (by positivity) (pow_lt_one₀ hq0 hq1 (by positivity)), ← pow_mul,
      ← pow_succ]

/-- `AGM(θ₃²(q), θ₄²(q)) = 1` for `0 ≤ q < 1`.
@isnad1 id=eq.2h1v.s6.0addabfa7b53 from=translated src=- shape=9b315002 vocab=13a4ee09
-/
theorem AGM_theta (hq0 : 0 ≤ q) (hq1 : q < 1) : AGM (theta3 q ^ 2) (theta4 q ^ 2) = 1 := by
  have hr : Tendsto (fun k : ℕ => q ^ 2 ^ k) atTop (𝓝 0) :=
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1).comp
      (tendsto_pow_atTop_atTop_of_one_lt one_lt_two)
  have hfrac : Tendsto (fun k : ℕ => 2 * q ^ 2 ^ k / (1 - q ^ 2 ^ k)) atTop (𝓝 0) := by
    have := (hr.const_mul 2).div (tendsto_const_nhds.sub hr) (by norm_num : (1 : ℝ) - 0 ≠ 0)
    rw [show (2 : ℝ) * 0 / (1 - 0) = 0 by norm_num] at this
    exact this
  have hup : ∀ k, AGM (theta3 q ^ 2) (theta4 q ^ 2)
      ≤ (1 + 2 * q ^ 2 ^ k / (1 - q ^ 2 ^ k)) ^ 2 := fun k => by
    have hr0 : 0 ≤ q ^ 2 ^ k := by positivity
    have hr1 : q ^ 2 ^ k < 1 := pow_lt_one₀ hq0 hq1 (by positivity)
    have h3 := theta3_pos hr0 hr1
    have h4 := theta4_pos hr0 hr1
    rw [AGM_theta_pow hq0 hq1 k]
    calc AGM (theta3 (q ^ 2 ^ k) ^ 2) (theta4 (q ^ 2 ^ k) ^ 2)
        ≤ max (theta3 (q ^ 2 ^ k) ^ 2) (theta4 (q ^ 2 ^ k) ^ 2) :=
          AGM_le_max (by positivity) (by positivity)
      _ = theta3 (q ^ 2 ^ k) ^ 2 :=
          max_eq_left (pow_le_pow_left₀ h4.le (theta4_le_theta3 hr0 hr1) 2)
      _ ≤ (1 + 2 * q ^ 2 ^ k / (1 - q ^ 2 ^ k)) ^ 2 :=
          pow_le_pow_left₀ h3.le (by linarith [theta3_sub_one_le hr0 hr1]) 2
  have hlow : ∀ᶠ k in atTop, (1 - 2 * q ^ 2 ^ k / (1 - q ^ 2 ^ k)) ^ 2
      ≤ AGM (theta3 q ^ 2) (theta4 q ^ 2) := by
    filter_upwards [hr.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 3))] with k hk
    have hr0 : 0 ≤ q ^ 2 ^ k := by positivity
    have hr1 : q ^ 2 ^ k < 1 := by linarith
    have h3 := theta3_pos hr0 hr1
    have h4 := theta4_pos hr0 hr1
    have hfr : 2 * q ^ 2 ^ k / (1 - q ^ 2 ^ k) < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    rw [AGM_theta_pow hq0 hq1 k]
    calc (1 - 2 * q ^ 2 ^ k / (1 - q ^ 2 ^ k)) ^ 2 ≤ theta4 (q ^ 2 ^ k) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith [one_sub_theta4_le hr0 hr1]) 2
      _ = min (theta3 (q ^ 2 ^ k) ^ 2) (theta4 (q ^ 2 ^ k) ^ 2) :=
          (min_eq_right (pow_le_pow_left₀ h4.le (theta4_le_theta3 hr0 hr1) 2)).symm
      _ ≤ AGM (theta3 (q ^ 2 ^ k) ^ 2) (theta4 (q ^ 2 ^ k) ^ 2) :=
          min_le_AGM (by positivity) (by positivity)
  have hlim_up : Tendsto (fun k : ℕ => (1 + 2 * q ^ 2 ^ k / (1 - q ^ 2 ^ k)) ^ 2) atTop (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).add hfrac).pow 2
    simpa using this
  have hlim_low : Tendsto (fun k : ℕ => (1 - 2 * q ^ 2 ^ k / (1 - q ^ 2 ^ k)) ^ 2) atTop
      (𝓝 1) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hfrac).pow 2
    simpa using this
  exact le_antisymm (ge_of_tendsto' hlim_up hup) (le_of_tendsto hlim_low hlow)

/-! ### The nome and (4.77) -/

/-- The complementary modulus `k' = θ₄²(q)/θ₃²(q)` of the nome `q`.-/
noncomputable def nomeK' (q : ℝ) : ℝ := theta4 q ^ 2 / theta3 q ^ 2

/-- The modulus `k = θ₂²(q)/θ₃²(q)` of the nome `q` (Jacobi's `θ₂⁴ + θ₄⁴ = θ₃⁴` gives
`k² + k'² = 1`; not proven here).-/
noncomputable def nomeK (q : ℝ) : ℝ := theta2 q ^ 2 / theta3 q ^ 2

/--
@isnad1 id=lt.2h1v.s5.cb548a5285cc from=translated src=- shape=536e06c9 vocab=4d864334
-/
theorem nomeK'_pos (hq0 : 0 ≤ q) (hq1 : q < 1) : 0 < nomeK' q := by
  unfold nomeK'
  have := theta4_pos hq0 hq1
  have := theta3_pos hq0 hq1
  positivity

/--
@isnad1 id=le.2h1v.s5.07dca5655ecb from=translated src=- shape=d34e1a3e vocab=4d864334
-/
theorem nomeK'_le_one (hq0 : 0 ≤ q) (hq1 : q < 1) : nomeK' q ≤ 1 := by
  unfold nomeK'
  have h3 := theta3_pos hq0 hq1
  have h4 := theta4_pos hq0 hq1
  rw [div_le_one (by positivity)]
  exact pow_le_pow_left₀ h4.le (theta4_le_theta3 hq0 hq1) 2

/-- `AGM(1, k') = 1/θ₃²(q)`.
@isnad1 id=eq.2h1v.s6.1b164348626c from=translated src=- shape=cec22192 vocab=914fa6d7
-/
theorem AGM_one_nomeK' (hq0 : 0 ≤ q) (hq1 : q < 1) : AGM 1 (nomeK' q) = 1 / theta3 q ^ 2 := by
  have h3 := theta3_pos hq0 hq1
  have hk := nomeK'_pos hq0 hq1
  have h := AGM_smul (c := theta3 q ^ 2) (by positivity) one_pos hk
  rw [mul_one, show theta3 q ^ 2 * nomeK' q = theta4 q ^ 2 by unfold nomeK'; field_simp,
    AGM_theta hq0 hq1] at h
  rw [eq_div_iff (by positivity)]
  linarith

/-- (4.77): `K(k) = (π/2) θ₃²(q)`, where `k = √(1 − k'²)`, `k' = θ₄²(q)/θ₃²(q)`.
@isnad1 id=eq.2h1v.s6.8a07d1694d93 from=translated src=- shape=570449a0 vocab=57896913
-/
theorem ellipticK_nome (hq0 : 0 ≤ q) (hq1 : q < 1) :
    ellipticK (Real.sqrt (1 - nomeK' q ^ 2)) = Real.pi / 2 * theta3 q ^ 2 := by
  have h := one_div_AGM_one (nomeK'_pos hq0 hq1) (nomeK'_le_one hq0 hq1)
  rw [AGM_one_nomeK' hq0 hq1, one_div_one_div] at h
  rw [h]
  field_simp

end BZ

end Azurite
