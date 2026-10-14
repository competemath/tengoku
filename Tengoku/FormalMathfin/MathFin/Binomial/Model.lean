/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

public import Tengoku

/-!
# Binomial-tree option pricing (Cox-Ross-Rubinstein style)

We formalize **discrete-time European option pricing on a binomial tree**.

At each time step, the asset price moves up by factor `u` or down by factor
`d`. Risk-free continuously-compounded rate per step is `r`. Under no-arbitrage
(`d < e^r < u`), there is a unique risk-neutral probability

    q = (e^r - d) / (u - d) ∈ (0, 1),

and the no-arbitrage price of a single-period contingent claim with payoffs
`V_u` (up state) and `V_d` (down state) is

    V_0 = e^{-r} (q · V_u + (1 - q) · V_d).

This file contains:
1. Risk-neutral probability `crrUpProb` and its `(0, 1)`-range bound.
2. Single-period option pricing formula `binomialOptionPriceOnePeriod`.
3. **No-arbitrage replication theorem**: cost of the replicating portfolio
   equals `binomialOptionPriceOnePeriod`.
4. Multi-period (`N`-step) backward-induction price `binomialPrice`.

The bridge to Black-Scholes (CRR convergence) is proved in
`Binomial/CRRCharFun.lean` (`binomialPrice_call_tendsto_bs`).
-/

@[expose] public section

namespace MathFin

/-! ### Risk-neutral up-probability -/

/-- The risk-neutral up-probability `q = (e^r - d) / (u - d)`. -/
noncomputable def crrUpProb (u d r : ℝ) : ℝ :=
  (Real.exp r - d) / (u - d)

/-- No-arbitrage condition for the binomial single-period model:
`d < e^r < u` (and `d > 0`). -/
structure BinomialNoArb (u d r : ℝ) : Prop where
  d_pos : 0 < d
  d_lt : d < Real.exp r
  lt_u : Real.exp r < u

/-- Under no-arbitrage, `u > d`.
@isnad1 id=lt.1h3v.s4.660adfb40ea1 from=translated src=- shape=2f86892d vocab=a4e05443
-/
lemma BinomialNoArb.d_lt_u {u d r : ℝ} (h : BinomialNoArb u d r) : d < u :=
  lt_trans h.d_lt h.lt_u

/-- Under no-arbitrage, `u > 0`.
@isnad1 id=lt.1h3v.s4.e3bd1b2647e7 from=translated src=- shape=5cc5ac7a vocab=a4e05443
-/
lemma BinomialNoArb.u_pos {u d r : ℝ} (h : BinomialNoArb u d r) : 0 < u :=
  lt_trans h.d_pos h.d_lt_u

/-- Under no-arbitrage, the risk-neutral up-probability is in `(0, 1)`.
@isnad1 id=mem.1h3v.s5.64a46ddc2952 from=translated src=- shape=49725960 vocab=6932bfcf
-/
lemma crrUpProb_mem_Ioo {u d r : ℝ} (h : BinomialNoArb u d r) :
    crrUpProb u d r ∈ Set.Ioo 0 1 := by
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  refine ⟨?_, ?_⟩
  · unfold crrUpProb
    exact div_pos (by linarith [h.d_lt]) h_ud
  · unfold crrUpProb
    rw [div_lt_one h_ud]; linarith [h.lt_u]

/-- The probability `1 - q = (u - e^r) / (u - d)`.
@isnad1 id=eq.1h3v.s5.73847cf51699 from=translated src=- shape=9fd6d358 vocab=7a35854b
-/
lemma one_sub_crrUpProb {u d r : ℝ} (h : BinomialNoArb u d r) :
    1 - crrUpProb u d r = (u - Real.exp r) / (u - d) := by
  unfold crrUpProb
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  field_simp
  ring

/-! ### Single-period option pricing -/

/-- Single-period European option price via the risk-neutral expectation:
`V_0 = e^{-r}(q · V_u + (1-q) · V_d)`. -/
noncomputable def binomialOptionPriceOnePeriod (u d r V_u V_d : ℝ) : ℝ :=
  Real.exp (-r) *
    (crrUpProb u d r * V_u + (1 - crrUpProb u d r) * V_d)

/-- **No-arbitrage single-period replication.** For an asset with spot `S_0`
and `BinomialNoArb u d r`, any contingent claim with payoffs `V_u` (in the up
state `S_0 · u`) and `V_d` (down state `S_0 · d`) is replicated by

    Δ = (V_u - V_d) / (S_0 (u - d))  shares of stock,
    B = e^{-r}(u · V_d - d · V_u) / (u - d)  in bonds (at time 0 value).

The cost of this replicating portfolio at time 0 equals
`binomialOptionPriceOnePeriod`.
@isnad1 id=other.2h6v.s7.451033c741c8 from=translated src=- shape=7a97958c vocab=00110e1c
-/
theorem replicating_portfolio_cost {S_0 u d r V_u V_d : ℝ}
    (hS_0 : 0 < S_0) (h : BinomialNoArb u d r) :
    let Δ : ℝ := (V_u - V_d) / (S_0 * (u - d))
    let B : ℝ := Real.exp (-r) * (u * V_d - d * V_u) / (u - d)
    Δ * S_0 + B = binomialOptionPriceOnePeriod u d r V_u V_d := by
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  have h_ud_ne : u - d ≠ 0 := h_ud.ne'
  have hS_0_ne : S_0 ≠ 0 := hS_0.ne'
  have h_exp_id : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  unfold binomialOptionPriceOnePeriod crrUpProb
  simp only
  field_simp
  linear_combination -(V_u - V_d) * h_exp_id

/-- **Replication payoff: up state.** The replicating portfolio pays `V_u`
when the asset goes up.
@isnad1 id=other.2h6v.s7.4249d62d0c82 from=translated src=- shape=68b3b937 vocab=cdf6ee61
-/
theorem replicating_payoff_up {S_0 u d r V_u V_d : ℝ}
    (hS_0 : 0 < S_0) (h : BinomialNoArb u d r) :
    let Δ : ℝ := (V_u - V_d) / (S_0 * (u - d))
    let B : ℝ := Real.exp (-r) * (u * V_d - d * V_u) / (u - d)
    Δ * (S_0 * u) + B * Real.exp r = V_u := by
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  have h_ud_ne : u - d ≠ 0 := h_ud.ne'
  have hS_0_ne : S_0 ≠ 0 := hS_0.ne'
  have h_exp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
  have h_exp_inv : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  simp only
  field_simp
  linear_combination (u * V_d - d * V_u) * h_exp_inv

/-- **Replication payoff: down state.** The replicating portfolio pays `V_d`
when the asset goes down.
@isnad1 id=other.2h6v.s7.b09c5bf0f5f9 from=translated src=- shape=199ad449 vocab=cdf6ee61
-/
theorem replicating_payoff_down {S_0 u d r V_u V_d : ℝ}
    (hS_0 : 0 < S_0) (h : BinomialNoArb u d r) :
    let Δ : ℝ := (V_u - V_d) / (S_0 * (u - d))
    let B : ℝ := Real.exp (-r) * (u * V_d - d * V_u) / (u - d)
    Δ * (S_0 * d) + B * Real.exp r = V_d := by
  have h_ud : 0 < u - d := by linarith [h.d_lt_u]
  have h_ud_ne : u - d ≠ 0 := h_ud.ne'
  have hS_0_ne : S_0 ≠ 0 := hS_0.ne'
  have h_exp_ne : Real.exp r ≠ 0 := (Real.exp_pos r).ne'
  have h_exp_inv : Real.exp (-r) * Real.exp r = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  simp only
  field_simp
  linear_combination (u * V_d - d * V_u) * h_exp_inv

/-! ### Multi-period (N-step) backward-induction pricing -/

/-- Backward-induction binomial tree price.

`binomialPrice u d r g n S` returns the time-0 option value with `n` time steps
remaining, current asset price `S`, and payoff function `g : ℝ → ℝ` (applied at
maturity). At each step, the price is the risk-neutral expectation discounted
by `e^{-r}`. -/
noncomputable def binomialPrice (u d r : ℝ) (g : ℝ → ℝ) : ℕ → ℝ → ℝ
  | 0, S => g S
  | n + 1, S =>
      Real.exp (-r) *
        (crrUpProb u d r * binomialPrice u d r g n (S * u) +
         (1 - crrUpProb u d r) * binomialPrice u d r g n (S * d))

/-- At maturity (`n = 0`) the binomial price is the payoff `g S`.
@isnad1 id=eq.0h5v.s4.17b35ad0997d from=translated src=- shape=04d361bc vocab=eb36e9c7
-/
@[simp]
lemma binomialPrice_zero (u d r : ℝ) (g : ℝ → ℝ) (S : ℝ) :
    binomialPrice u d r g 0 S = g S := rfl

/-- One-step backward recursion: the price at `n+1` is the discounted risk-neutral
average of the prices at the up/down successors.
@isnad1 id=eq.0h6v.s6.fcd5aa54f571 from=translated src=- shape=99f0c0e0 vocab=edabe10d
-/
lemma binomialPrice_succ (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r g (n + 1) S =
      Real.exp (-r) *
        (crrUpProb u d r * binomialPrice u d r g n (S * u) +
         (1 - crrUpProb u d r) * binomialPrice u d r g n (S * d)) := rfl

/-- **One-step consistency**: `binomialPrice u d r g (n+1) S` equals
`binomialOptionPriceOnePeriod u d r V_u V_d` where `V_u, V_d` are the
sub-tree prices for `n` more steps starting from `S·u` and `S·d`.
@isnad1 id=eq.0h6v.s6.9aa185bed224 from=translated src=- shape=3d4c7bbd vocab=bc8076b1
-/
theorem binomialPrice_succ_eq_onePeriod (u d r : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r g (n + 1) S =
      binomialOptionPriceOnePeriod u d r
        (binomialPrice u d r g n (S * u))
        (binomialPrice u d r g n (S * d)) := by
  rw [binomialPrice_succ, binomialOptionPriceOnePeriod]

/-- **Linearity of the binomial price** in the payoff function.
@isnad1 id=eq.0h7v.s5.884852b57632 from=translated src=- shape=66e9e0fc vocab=eb2166de
-/
lemma binomialPrice_add (u d r : ℝ) (g h : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r (fun x ↦ g x + h x) n S =
      binomialPrice u d r g n S + binomialPrice u d r h n S := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rw [binomialPrice_succ, binomialPrice_succ, binomialPrice_succ]
    rw [ih (S * u), ih (S * d)]
    ring

/-- **Scalar homogeneity of the binomial price** in the payoff function.
@isnad1 id=eq.0h7v.s5.1bf1b83c43de from=translated src=- shape=f3b59018 vocab=abd099d3
-/
lemma binomialPrice_smul (u d r c : ℝ) (g : ℝ → ℝ) (n : ℕ) (S : ℝ) :
    binomialPrice u d r (fun x ↦ c * g x) n S = c * binomialPrice u d r g n S := by
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rw [binomialPrice_succ, binomialPrice_succ]
    rw [ih (S * u), ih (S * d)]
    ring

/-- **Constant-payoff price**: a deterministic payoff `c` at maturity has time-0
price `e^{-rn} · c` for `n` steps.
@isnad1 id=eq.1h6v.s5.f1adc05d0f09 from=translated src=- shape=720d8c94 vocab=6e90d912
-/
theorem binomialPrice_const (u d r c : ℝ) (_h : BinomialNoArb u d r) (n : ℕ) (S : ℝ) :
    binomialPrice u d r (fun _ ↦ c) n S = Real.exp (-(n : ℝ) * r) * c := by
  induction n generalizing S with
  | zero => simp
  | succ n ih =>
    rw [binomialPrice_succ, ih (S * u), ih (S * d)]
    have h_q_complement : crrUpProb u d r + (1 - crrUpProb u d r) = 1 := by ring
    have h_factor : Real.exp (-r) * Real.exp (-(n : ℝ) * r) = Real.exp (-((n + 1 : ℕ) : ℝ) * r) := by
      rw [← Real.exp_add]
      congr 1
      push_cast
      ring
    calc Real.exp (-r) *
          (crrUpProb u d r * (Real.exp (-(n : ℝ) * r) * c) +
            (1 - crrUpProb u d r) * (Real.exp (-(n : ℝ) * r) * c))
        = Real.exp (-r) * Real.exp (-(n : ℝ) * r) * c *
            (crrUpProb u d r + (1 - crrUpProb u d r)) := by ring
      _ = Real.exp (-r) * Real.exp (-(n : ℝ) * r) * c * 1 := by rw [h_q_complement]
      _ = Real.exp (-((n + 1 : ℕ) : ℝ) * r) * c := by rw [mul_one, h_factor]

/-- **One-step risk-neutral martingale identity** for the binomial up-probability:
`p · u + (1 − p) · d = eʳ`.
@isnad1 id=eq.1h3v.s5.a17c2d9fed31 from=translated src=- shape=8fdea789 vocab=11296364
-/
lemma crrUpProb_mul_up_add (u d r : ℝ) (h : BinomialNoArb u d r) :
    crrUpProb u d r * u + (1 - crrUpProb u d r) * d = Real.exp r := by
  have hud : u - d ≠ 0 := sub_ne_zero.mpr h.d_lt_u.ne'
  rw [crrUpProb]
  field_simp
  ring

/-- **Stock-price martingale value**: pricing the payoff `g(S) = S` (the underlying
itself) returns `S` — the discounted stock price is a martingale under the
risk-neutral probability.
@isnad1 id=eq.1h5v.s4.85e3b1942f92 from=translated src=- shape=ec0d6f4d vocab=bfb40e18
-/
theorem binomialPrice_id (u d r : ℝ) (h : BinomialNoArb u d r) (n : ℕ) (S : ℝ) :
    binomialPrice u d r (fun x ↦ x) n S = S := by
  have hmart := crrUpProb_mul_up_add u d r h
  induction n generalizing S with
  | zero => rfl
  | succ n ih =>
    rw [binomialPrice_succ, ih (S * u), ih (S * d),
        show crrUpProb u d r * (S * u) + (1 - crrUpProb u d r) * (S * d)
          = S * (crrUpProb u d r * u + (1 - crrUpProb u d r) * d) from by ring, hmart,
        show Real.exp (-r) * (S * Real.exp r) = S * (Real.exp (-r) * Real.exp r) from by ring,
        ← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]

end MathFin
