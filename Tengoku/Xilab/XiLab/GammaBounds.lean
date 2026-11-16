import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms XiLab.log_Gamma_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Gamma_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.log_Gamma_le_rpow` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.log_Gamma_shift_le` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.GammaBounds — an explicit Stirling-type upper envelope for `Real.Gamma`

-/

namespace XiLab

open Real

/-! ### Elementary logarithm inequalities -/

/-- `u/(1+u) ≤ log (1+u)` for `u ≥ 0`.-/
theorem self_div_add_one_le_log_add_one {u : ℝ} (hu : 0 ≤ u) :
    u / (1 + u) ≤ Real.log (1 + u) := by
  have h1 : (0 : ℝ) < 1 + u := by linarith
  have h2 := Real.log_le_sub_one_of_pos (x := 1 / (1 + u)) (by positivity)
  rw [Real.log_div one_ne_zero h1.ne', Real.log_one, zero_sub] at h2
  have h3 : 1 / (1 + u) - 1 = -(u / (1 + u)) := by field_simp; ring
  rw [h3] at h2
  linarith

/-- The key "gap" inequality: `t ≤ (a+t) * (log (a+t) - log a)` for `a > 0`, `t ≥ 0`.
This is exactly the amount by which `x ↦ x log x - x` outruns the chord of `log Γ`.-/
theorem le_mul_log_sub_log {a t : ℝ} (ha : 0 < a) (ht : 0 ≤ t) :
    t ≤ (a + t) * (Real.log (a + t) - Real.log a) := by
  have hat : (0 : ℝ) < a + t := by linarith
  have key : t / (a + t) ≤ Real.log (a + t) - Real.log a := by
    have h := self_div_add_one_le_log_add_one (u := t / a) (by positivity)
    have e1 : 1 + t / a = (a + t) / a := by field_simp
    rw [e1, Real.log_div hat.ne' ha.ne'] at h
    have e2 : t / a / ((a + t) / a) = t / (a + t) := by
      field_simp
    rwa [e2] at h
  calc t = (a + t) * (t / (a + t)) := by field_simp
    _ ≤ (a + t) * (Real.log (a + t) - Real.log a) :=
        mul_le_mul_of_nonneg_left key hat.le

/-! ### The bound at integer arguments -/

/-- `log (n !) = log Γ(n+1) ≤ (n+1) log (n+1) - (n+1) + 1`.
Proved by induction; the inductive step is exactly `le_mul_log_sub_log` with `t = 1`,
i.e. the fact that `(1 + 1/n)^(n+1) ≥ e`.-/
theorem log_Gamma_natCast_add_one_le (n : ℕ) :
    Real.log (Real.Gamma ((n : ℝ) + 1)) ≤ ((n : ℝ) + 1) * Real.log ((n : ℝ) + 1) - (n + 1) + 1 := by
  induction n with
  | zero => norm_num
  | succ m ih =>
    have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hpos : 0 < Real.Gamma ((m : ℝ) + 1) := Real.Gamma_pos_of_pos hm
    have hlog : Real.log (Real.Gamma ((m : ℝ) + 1 + 1))
        = Real.log ((m : ℝ) + 1) + Real.log (Real.Gamma ((m : ℝ) + 1)) := by
      rw [Real.Gamma_add_one hm.ne', Real.log_mul hm.ne' hpos.ne']
    have hgap := le_mul_log_sub_log (a := (m : ℝ) + 1) (t := 1) hm zero_le_one
    push_cast
    rw [hlog]
    linarith

/-- `log Γ(n) ≤ n log n - n + 1` for a positive natural `n`.-/
theorem log_Gamma_natCast_le {n : ℕ} (hn : 1 ≤ n) :
    Real.log (Real.Gamma (n : ℝ)) ≤ (n : ℝ) * Real.log (n : ℝ) - n + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have := log_Gamma_natCast_add_one_le m
  push_cast
  exact this

/-! ### The main envelope -/

/-- **Stirling-type upper envelope for `Real.Gamma`.**

For `x ≥ 1`,
`log Γ(x) ≤ x log x - x + 1`.

The constant `1` is sharp — equality holds at `x = 1`, since `Γ(1) = 1`.  (Remark, NOT
formalised here: the slack `x log x - x + 1 - log Γ(x)` is strictly increasing on `[1,∞)`,
because its derivative is `log x - ψ(x) > 0`.  Mathlib's `Real.digamma` is the complex
`logDeriv Gamma` with no such estimate attached, so that route is unavailable; the proof
below goes through log-convexity instead.)

Proof: the bound holds at integers by induction, and log-convexity of `Γ`
(`Real.convexOn_log_Gamma`) interpolates it between consecutive integers, with the slack
supplied by `le_mul_log_sub_log`.-/
theorem log_Gamma_le {x : ℝ} (hx : 1 ≤ x) :
    Real.log (Real.Gamma x) ≤ x * Real.log x - x + 1 := by
  have hx0 : (0 : ℝ) < x := by linarith
  obtain ⟨n, hn1, hnx, hxn⟩ : ∃ n : ℕ, 1 ≤ n ∧ (n : ℝ) ≤ x ∧ x < (n : ℝ) + 1 :=
    ⟨⌊x⌋₊, (Nat.one_le_floor_iff x).2 hx, Nat.floor_le hx0.le, Nat.lt_floor_add_one x⟩
  have hnR : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hn0 : (0 : ℝ) < (n : ℝ) := by linarith
  -- log-convexity of `Γ` on the segment `[n, n+1]`, evaluated at `x = n + (x - n)`
  have ha : (0 : ℝ) ≤ 1 - (x - (n : ℝ)) := by linarith
  have hb : (0 : ℝ) ≤ x - (n : ℝ) := by linarith
  have hab : (1 - (x - (n : ℝ))) + (x - (n : ℝ)) = 1 := by ring
  have hconv := Real.convexOn_log_Gamma.2 (Set.mem_Ioi.mpr hn0)
      (Set.mem_Ioi.mpr (by linarith : (0 : ℝ) < (n : ℝ) + 1)) ha hb hab
  simp only [Function.comp_apply, smul_eq_mul] at hconv
  have harg : (1 - (x - (n : ℝ))) * (n : ℝ) + (x - (n : ℝ)) * ((n : ℝ) + 1) = x := by ring
  rw [harg] at hconv
  -- `Γ(n+1) = n Γ(n)` collapses the right-hand endpoint
  have hgpos : 0 < Real.Gamma (n : ℝ) := Real.Gamma_pos_of_pos hn0
  have hGn : Real.log (Real.Gamma ((n : ℝ) + 1))
      = Real.log (n : ℝ) + Real.log (Real.Gamma (n : ℝ)) := by
    rw [Real.Gamma_add_one hn0.ne', Real.log_mul hn0.ne' hgpos.ne']
  rw [hGn] at hconv
  -- the integer bound and the gap inequality
  have hint := log_Gamma_natCast_le hn1
  have hgap := le_mul_log_sub_log hn0 hb
  have hsum : (n : ℝ) + (x - (n : ℝ)) = x := by ring
  rw [hsum] at hgap
  nlinarith [hconv, hint, hgap]

/-! ### Consequences: the shapes the order-`≤ 1` argument consumes -/

/-- Multiplicative form of `log_Gamma_le`: `Γ(x) ≤ e · x^x · e^(-x)` for `x ≥ 1`
(`x ^ x` is `Real.rpow`).  This is the "Stirling without the `√x`" envelope; the missing
`√(2π/x)` factor is exactly the slack that makes the constant `e` instead of `√(2π)`.-/
theorem Gamma_le {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ Real.exp 1 * x ^ x * Real.exp (-x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hg : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
  calc Real.Gamma x = Real.exp (Real.log (Real.Gamma x)) := (Real.exp_log hg).symm
    _ ≤ Real.exp (x * Real.log x - x + 1) := Real.exp_le_exp.mpr (log_Gamma_le hx)
    _ = Real.exp 1 * x ^ x * Real.exp (-x) := by
        rw [Real.rpow_def_of_pos hx0, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring

/-- The crude form that is all the order computation actually needs: `log Γ(x) ≤ x log x`.-/
theorem log_Gamma_le_mul_log {x : ℝ} (hx : 1 ≤ x) :
    Real.log (Real.Gamma x) ≤ x * Real.log x := by
  have := log_Gamma_le hx
  linarith

/-- `Γ(x) ≤ exp (x log x)` for `x ≥ 1`.-/
theorem Gamma_le_exp_mul_log {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ Real.exp (x * Real.log x) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hg : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
  calc Real.Gamma x = Real.exp (Real.log (Real.Gamma x)) := (Real.exp_log hg).symm
    _ ≤ _ := Real.exp_le_exp.mpr (log_Gamma_le_mul_log hx)

/-- **Order `≤ 1` in growth form.** For every `ε > 0` and every `x ≥ 1`,
`log Γ(x) ≤ x^(1+ε) / ε`.

This is the statement Proposition 3.2 of the tempered-`ξ` paper needs: the envelope
`|F(w)| ≤ (C₁/2) Γ(r/2 + 9/4) / π^(r/2+9/4)` combined with this gives
`log max_{|w|=r} |F| = O(r^(1+ε))` for every `ε > 0`, i.e. order at most one.-/
theorem log_Gamma_le_rpow {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    Real.log (Real.Gamma x) ≤ x ^ (1 + ε) / ε := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : Real.log x ≤ x ^ ε / ε := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 ε)
    rw [Real.log_rpow hx0] at h
    rw [le_div_iff₀ hε]
    nlinarith [h]
  have hxr : x ^ (1 + ε) = x * x ^ ε := by rw [Real.rpow_add hx0, Real.rpow_one]
  refine le_trans (log_Gamma_le_mul_log hx) ?_
  rw [hxr]
  calc x * Real.log x ≤ x * (x ^ ε / ε) := mul_le_mul_of_nonneg_left hlog hx0.le
    _ = x * x ^ ε / ε := by ring

/-- Multiplicative form of `log_Gamma_le_rpow`.-/
theorem Gamma_le_exp_rpow {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    Real.Gamma x ≤ Real.exp (x ^ (1 + ε) / ε) := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hg : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx0
  calc Real.Gamma x = Real.exp (Real.log (Real.Gamma x)) := (Real.exp_log hg).symm
    _ ≤ _ := Real.exp_le_exp.mpr (log_Gamma_le_rpow hε hx)

/-- A variant valid on all of `(0, ∞)`, obtained from `Γ(x) = Γ(x+1)/x`.
Needed only if a downstream argument hits an argument in `(0,1)`; the paper's
`Γ(r/2 + 9/4)` never does.-/
theorem log_Gamma_le_of_pos {x : ℝ} (hx : 0 < x) :
    Real.log (Real.Gamma x) ≤ (x + 1) * Real.log (x + 1) - x - Real.log x := by
  have h := log_Gamma_le (x := x + 1) (by linarith)
  have hg : 0 < Real.Gamma x := Real.Gamma_pos_of_pos hx
  have hsplit : Real.log (Real.Gamma (x + 1)) = Real.log x + Real.log (Real.Gamma x) := by
    rw [Real.Gamma_add_one hx.ne', Real.log_mul hx.ne' hg.ne']
  rw [hsplit] at h
  linarith

/-! ### The Proposition 3.2 interface

The paper's envelope is `|F(w)| ≤ (C₁/2) · Γ(r/2 + 9/4) / π^(r/2 + 9/4)` with `r = |w|`.
These two lemmas are that `Γ` factor, already specialised, so `XiLab/Kernel.lean` can use
them without redoing the `1 ≤ x` side condition. -/

/-- The envelope at the paper's argument `r/2 + 9/4`, `r ≥ 0`.-/
theorem log_Gamma_shift_le {r : ℝ} (hr : 0 ≤ r) :
    Real.log (Real.Gamma (r / 2 + 9 / 4))
      ≤ (r / 2 + 9 / 4) * Real.log (r / 2 + 9 / 4) - (r / 2 + 9 / 4) + 1 :=
  log_Gamma_le (by linarith)

/-- The order-`≤ 1` form at the paper's argument `r/2 + 9/4`, `r ≥ 0`.-/
theorem log_Gamma_shift_le_rpow {ε : ℝ} (hε : 0 < ε) {r : ℝ} (hr : 0 ≤ r) :
    Real.log (Real.Gamma (r / 2 + 9 / 4)) ≤ (r / 2 + 9 / 4) ^ (1 + ε) / ε :=
  log_Gamma_le_rpow hε (by linarith)

end XiLab

/-! ### Axiom audit -/

