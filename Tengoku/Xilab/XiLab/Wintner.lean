import Tengoku
import Tengoku.Xilab.XiLab.Kernel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms XiLab.hasDerivAt_phiTerm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.abs_phiTerm'_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.hasDerivAt_Phi` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.deriv_Phi` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.deriv_Phi_neg` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Phi_strictAntiOn_Ici` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Phi_strictAntiOn_Ici_inv_four_hundred` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Phi_antitoneOn_Ici_inv_four_hundred` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.SineTransform.block_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.SineTransform.sin_transform_nonneg` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.SineTransform.sin_transform_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.integrableOn_Phi` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.F_ofReal_mul_I` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.F_ne_zero_of_imag_of_strictAntiOn` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.Wintner — monotonicity of `Φ` and sine-transform positivity

Consumes `XiLab/Kernel.lean`
(`phiTerm`, `Phi`, `F`, `summable_phiTerm_succ`, `continuous_Phi`, `cast_le_sq`,
`norm_exp_neg_pi_exp_lt_one`, `abs_Phi_le`, `phiConst`, `integrableOn_of_le_envelope`).
There is no `sorry`, no `native_decide` and no custom `axiom` in this file, and no FRONTIER
lemma was needed.

## Main results

* `XiLab.hasDerivAt_Phi` — **`Φ` may be differentiated term by term** at every real point,
  `Φ'(u) = ∑_{n≥1} phiTerm' n u`, together with `differentiable_Phi` and `deriv_Phi`.
* `XiLab.deriv_Phi_neg` — `Φ'(x) < 0` for `x ≥ c` whenever `π e^{2c} ≥ 3.156`.
* `XiLab.Phi_strictAntiOn_Ici` — **Wintner's monotonicity theorem**, general form:
  `StrictAntiOn Φ (Ici c)` under the same hypothesis on `c`.
* `XiLab.Phi_strictAntiOn_Ici_inv_four_hundred` — the concrete instance
  `StrictAntiOn Φ (Ici (1/400))`, and `Phi_antitoneOn_Ici_inv_four_hundred` non-strict.
* `XiLab.SineTransform.sin_transform_nonneg` / `sin_transform_pos` — the classical
  half-period pairing lemma for a general kernel `g`: nonincreasing gives `≥ 0`, strictly
  decreasing gives `> 0`.  Wintner (1947); the draft's Lemma 6.5 calls it classical.
* `XiLab.F_ofReal_mul_I` — `F(it) = 2i ∫₀^∞ Φ(u) sin(tu) du`, and
  `XiLab.F_ne_zero_of_imag_of_strictAntiOn` — imaginary-axis nonvanishing, **conditional**
  on `StrictAntiOn Φ (Ici 0)`.

## What is NOT proved, and why

`StrictAntiOn Φ (Set.Ici 0)` is **true but not delivered**.  `Φ` is even, so `Φ'(0) = 0`
exactly; the `n = 1` summand of `Φ` is strictly *increasing* on `[0, c₀)` with
`c₀ = ½ log((30+√420)/(16π)) = 0.00226697…`, and at `u = 0` the first two summands of `Φ'`
sum to `+8.265e−8`, cancelled to exactly zero only by the `n ≥ 3` tail.  No finite truncation
of the series has nonpositive derivative at `0`, so `Ici 0` needs the Jacobi theta functional
equation, not a sharper estimate.  The closing note of this file spells this out.

Consequently `F_ne_zero_of_imag` is delivered only in the conditional form: the sine-transform
pairing must be anchored at `0`, where the sine's zeros are, so `StrictAntiOn Φ (Ici (1/400))`
does not feed it.

`Wintner` does not occur anywhere in Mathlib (case-insensitive grep over the whole tree);
the termwise-derivative apparatus here is built from scratch on
`Mathlib/Analysis/Calculus/SmoothSeries.lean`'s `hasDerivAt_tsum_of_isPreconnected`.
-/

open scoped Real
open MeasureTheory Set Filter Topology

namespace XiLab

/-! ### The termwise derivative -/

/-- `d/du` of `XiLab.phiTerm n`.

Writing `q = π n²` and `x = q e^{2u}`, the `n`-th summand of `Φ` is
`2q(2q e^{2u} − 3) e^{5u/2} e^{−x}` and its derivative is
`−q e^{5u/2} e^{−x} (8x² − 30x + 15)`.

The quadratic `8x² − 30x + 15` is the whole story: it is **positive** exactly for
`x < (30−√420)/16 = 0.594…` or `x > (30+√420)/16 = 3.155874…`, so the summand is
strictly decreasing precisely on that range of `x`.-/
noncomputable def phiTerm' (n : ℕ) (u : ℝ) : ℝ :=
  -(π * (n : ℝ) ^ 2) * Real.exp (5 * u / 2) *
      Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
    (8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 -
      30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 15)

lemma exp_nine_halves (u : ℝ) :
    Real.exp (9 * u / 2) = Real.exp (2 * u) * Real.exp (5 * u / 2) := by
  rw [← Real.exp_add]; ring_nf

lemma hasDerivAt_phiTerm (n : ℕ) (u : ℝ) : HasDerivAt (phiTerm n) (phiTerm' n u) u := by
  have h2 : HasDerivAt (fun v : ℝ => 2 * v) (2 : ℝ) u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have h5 : HasDerivAt (fun v : ℝ => 5 * v / 2) (5 / 2 : ℝ) u := by
    simpa using ((hasDerivAt_id u).const_mul (5 : ℝ)).div_const 2
  have h9 : HasDerivAt (fun v : ℝ => 9 * v / 2) (9 / 2 : ℝ) u := by
    simpa using ((hasDerivAt_id u).const_mul (9 : ℝ)).div_const 2
  have e2 : HasDerivAt (fun v : ℝ => Real.exp (2 * v)) (Real.exp (2 * u) * 2) u := h2.exp
  have e5 : HasDerivAt (fun v : ℝ => Real.exp (5 * v / 2))
      (Real.exp (5 * u / 2) * (5 / 2)) u := h5.exp
  have e9 : HasDerivAt (fun v : ℝ => Real.exp (9 * v / 2))
      (Real.exp (9 * u / 2) * (9 / 2)) u := h9.exp
  have hb : HasDerivAt (fun v : ℝ => Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * v))))
      (Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
        (-(π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2)))) u :=
    ((e2.const_mul (π * (n : ℝ) ^ 2)).neg).exp
  have ha : HasDerivAt
      (fun v : ℝ => 4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * v / 2) -
        6 * π * (n : ℝ) ^ 2 * Real.exp (5 * v / 2))
      (4 * π ^ 2 * (n : ℝ) ^ 4 * (Real.exp (9 * u / 2) * (9 / 2)) -
        6 * π * (n : ℝ) ^ 2 * (Real.exp (5 * u / 2) * (5 / 2))) u :=
    (e9.const_mul _).sub (e5.const_mul _)
  have hfun : phiTerm n = fun v : ℝ =>
      (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * v / 2) -
        6 * π * (n : ℝ) ^ 2 * Real.exp (5 * v / 2)) *
      Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * v))) := rfl
  have heq :
      (4 * π ^ 2 * (n : ℝ) ^ 4 * (Real.exp (9 * u / 2) * (9 / 2)) -
        6 * π * (n : ℝ) ^ 2 * (Real.exp (5 * u / 2) * (5 / 2))) *
        Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) +
      (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
        6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
        (Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
          (-(π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2))))
      = phiTerm' n u := by
    rw [phiTerm', exp_nine_halves]; ring
  rw [hfun, ← heq]
  exact ha.mul hb

/-! ### A locally uniform majorant for the differentiated series -/

lemma sq_le_pow_six (n : ℕ) : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 6 := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · norm_num
  · exact pow_le_pow_right₀ (by exact_mod_cast h) (by norm_num)

lemma pow_four_le_pow_six (n : ℕ) : (n : ℝ) ^ 4 ≤ (n : ℝ) ^ 6 := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · norm_num
  · exact pow_le_pow_right₀ (by exact_mod_cast h) (by norm_num)

/-- Majorant for `|phiTerm' n u|`, uniform for `u ∈ [a,b]`: `C(a,b) · n⁶ · r(a)^n` with
`r(a) = e^{−π e^{2a}} < 1`.  Same shape as the bound `Kernel.lean` uses for `Φ` itself
(`abs_phiTerm_le_of_mem_Icc`), with `n⁴` upgraded to `n⁶` because differentiating pulls
down one more factor of `π n² e^{2u}`.-/
noncomputable def derivBound (a b : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (5 * b / 2) *
      (8 * π ^ 3 * Real.exp (4 * b) + 30 * π ^ 2 * Real.exp (2 * b) + 15 * π)) *
    ((n : ℝ) ^ 6 * Real.exp (-(π * Real.exp (2 * a))) ^ n)

theorem summable_derivBound (a b : ℝ) : Summable (derivBound a b) :=
  (summable_pow_mul_geometric_of_norm_lt_one 6 (norm_exp_neg_pi_exp_lt_one a)).mul_left _

lemma abs_phiTerm'_le {a b : ℝ} (n : ℕ) {u : ℝ} (hau : a ≤ u) (hub : u ≤ b) :
    |phiTerm' n u| ≤ derivBound a b n := by
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hEu : (0 : ℝ) < Real.exp (2 * u) := Real.exp_pos _
  have hx0 : (0 : ℝ) ≤ π * (n : ℝ) ^ 2 * Real.exp (2 * u) := by positivity
  -- Rewrite `phiTerm'` as `-(positive · quadratic)`.
  have hrw : phiTerm' n u =
      -((π * (n : ℝ) ^ 2 * (Real.exp (5 * u / 2) *
          Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))))) *
        (8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 -
          30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 15)) := by
    rw [phiTerm']; ring
  have hAnn : (0 : ℝ) ≤ π * (n : ℝ) ^ 2 * (Real.exp (5 * u / 2) *
      Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))) := by positivity
  rw [hrw, abs_neg, abs_mul, abs_of_nonneg hAnn]
  -- Step 1: `|8x² − 30x + 15| ≤ 8x² + 30x + 15`.
  have hP : |8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 -
      30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 15| ≤
      8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 +
        30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 15 := by
    refine abs_le.mpr ⟨by nlinarith [sq_nonneg (π * (n : ℝ) ^ 2 * Real.exp (2 * u))],
      by nlinarith⟩
  -- Step 2: monotone replacements `u → b` in the polynomial factor.
  have hEb : Real.exp (2 * u) ≤ Real.exp (2 * b) := Real.exp_le_exp.mpr (by linarith)
  have hQ : 8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 +
      30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 15 ≤
      8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 +
        30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) + 15 := by
    have h1 : (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ≤ (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) := by
      have : (0 : ℝ) ≤ π * (n : ℝ) ^ 2 := by positivity
      nlinarith
    nlinarith [hx0]
  -- Step 3: monotone replacements in the prefactor.
  have h5b : Real.exp (5 * u / 2) ≤ Real.exp (5 * b / 2) := Real.exp_le_exp.mpr (by linarith)
  have hEa : Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) ≤
      Real.exp (-(π * Real.exp (2 * a))) ^ n := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have ha' : Real.exp (2 * a) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
    have hnn : (n : ℝ) ≤ (n : ℝ) ^ 2 := cast_le_sq n
    have s1 : (n : ℝ) * (π * Real.exp (2 * a)) ≤ (n : ℝ) ^ 2 * (π * Real.exp (2 * a)) :=
      mul_le_mul_of_nonneg_right hnn (by positivity)
    have s2 : π * (n : ℝ) ^ 2 * Real.exp (2 * a) ≤ π * (n : ℝ) ^ 2 * Real.exp (2 * u) :=
      mul_le_mul_of_nonneg_left ha' (by positivity)
    nlinarith [s1, s2]
  have hpre : π * (n : ℝ) ^ 2 * (Real.exp (5 * u / 2) *
        Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))) ≤
      π * (n : ℝ) ^ 2 * (Real.exp (5 * b / 2) * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by
    have hpow : (0 : ℝ) ≤ Real.exp (-(π * Real.exp (2 * a))) ^ n :=
      pow_nonneg (Real.exp_pos _).le n
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact mul_le_mul h5b hEa (Real.exp_pos _).le (Real.exp_pos _).le
  -- Combine.
  calc (π * (n : ℝ) ^ 2 * (Real.exp (5 * u / 2) *
          Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))))) *
        |8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 -
          30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 15|
      ≤ (π * (n : ℝ) ^ 2 * (Real.exp (5 * b / 2) *
            Real.exp (-(π * Real.exp (2 * a))) ^ n)) *
          (8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 +
            30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) + 15) := by
        refine mul_le_mul hpre (hP.trans hQ) (abs_nonneg _) ?_
        positivity
    _ ≤ derivBound a b n := by
        have hpow : (0 : ℝ) ≤ Real.exp (-(π * Real.exp (2 * a))) ^ n :=
          pow_nonneg (Real.exp_pos _).le n
        have h2 := sq_le_pow_six n
        have h4 := pow_four_le_pow_six n
        have hEb0 : (0 : ℝ) < Real.exp (2 * b) := Real.exp_pos _
        have h5b0 : (0 : ℝ) < Real.exp (5 * b / 2) := Real.exp_pos _
        rw [derivBound]
        have key : π * (n : ℝ) ^ 2 *
              (8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 +
                30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) + 15) ≤
            (8 * π ^ 3 * Real.exp (4 * b) + 30 * π ^ 2 * Real.exp (2 * b) + 15 * π) *
              (n : ℝ) ^ 6 := by
          have hsq : Real.exp (2 * b) ^ 2 = Real.exp (4 * b) := by
            rw [← Real.exp_nat_mul]; ring_nf
          rw [← hsq]
          have t1 : 30 * π ^ 2 * Real.exp (2 * b) * (n : ℝ) ^ 4 ≤
              30 * π ^ 2 * Real.exp (2 * b) * (n : ℝ) ^ 6 :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
          have t2 : 15 * π * (n : ℝ) ^ 2 ≤ 15 * π * (n : ℝ) ^ 6 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          nlinarith [t1, t2]
        calc (π * (n : ℝ) ^ 2 * (Real.exp (5 * b / 2) *
                Real.exp (-(π * Real.exp (2 * a))) ^ n)) *
              (8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 +
                30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) + 15)
            = (π * (n : ℝ) ^ 2 *
                (8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 +
                  30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) + 15)) *
                (Real.exp (5 * b / 2) * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by ring
          _ ≤ ((8 * π ^ 3 * Real.exp (4 * b) + 30 * π ^ 2 * Real.exp (2 * b) + 15 * π) *
                (n : ℝ) ^ 6) *
                (Real.exp (5 * b / 2) * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by
              refine mul_le_mul_of_nonneg_right key ?_
              positivity
          _ = (Real.exp (5 * b / 2) *
                (8 * π ^ 3 * Real.exp (4 * b) + 30 * π ^ 2 * Real.exp (2 * b) + 15 * π)) *
                ((n : ℝ) ^ 6 * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by ring

theorem summable_phiTerm' (x : ℝ) : Summable (fun n : ℕ => phiTerm' n x) := by
  refine Summable.of_norm_bounded (summable_derivBound (x - 1) (x + 1)) (fun n => ?_)
  simpa [Real.norm_eq_abs] using
    abs_phiTerm'_le n (by linarith : x - 1 ≤ x) (by linarith : x ≤ x + 1)

theorem summable_phiTerm'_succ (x : ℝ) : Summable (fun n : ℕ => phiTerm' (n + 1) x) :=
  (summable_nat_add_iff 1).mpr (summable_phiTerm' x)

/-! ### Termwise differentiation of the series defining `Φ` -/

/-- **`Φ` may be differentiated term by term**, at every real point.

`Kernel.lean` established continuity by `continuousOn_tsum` on compact `Icc`s, because the
termwise majorant is `u`-dependent (the geometric ratio `e^{−π e^{2u}}` degenerates as
`u → −∞`).  The same restriction applies here, so the differentiation theorem used is
`hasDerivAt_tsum_of_isPreconnected` applied on the *bounded open* interval
`Ioo (x−1) (x+1)`, where `derivBound (x−1) (x+1)` is a genuine uniform majorant.-/
theorem hasDerivAt_Phi (x : ℝ) : HasDerivAt Phi (∑' n : ℕ, phiTerm' (n + 1) x) x := by
  have hmem : x ∈ Ioo (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
  have hsum : Summable (fun n : ℕ => derivBound (x - 1) (x + 1) (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_derivBound _ _)
  exact hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => derivBound (x - 1) (x + 1) (n + 1))
    (g := fun n : ℕ => phiTerm (n + 1)) (g' := fun (n : ℕ) (v : ℝ) => phiTerm' (n + 1) v)
    hsum isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hasDerivAt_phiTerm (n + 1) y)
    (fun n y hy => by
      rw [Real.norm_eq_abs]
      exact abs_phiTerm'_le (n + 1) hy.1.le hy.2.le)
    hmem (summable_phiTerm_succ x) hmem

theorem differentiable_Phi : Differentiable ℝ Phi := fun x => (hasDerivAt_Phi x).differentiableAt

theorem deriv_Phi (x : ℝ) : deriv Phi x = ∑' n : ℕ, phiTerm' (n + 1) x := (hasDerivAt_Phi x).deriv

/-! ### Sign of the derivative -/

/-- The `n`-th summand of `Φ` (`n ≥ 1`) is strictly decreasing as soon as
`π n² e^{2u} > (30+√420)/16 = 3.155874…`.  The threshold `3.156` used here is a rational
upper bound for that root.-/
lemma phiTerm'_neg {n : ℕ} (hn : 1 ≤ n) {c u : ℝ} (hc : (3.156 : ℝ) ≤ π * Real.exp (2 * c))
    (hu : c ≤ u) : phiTerm' n u < 0 := by
  have hpi := Real.pi_pos
  have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hEc : (0 : ℝ) < Real.exp (2 * c) := Real.exp_pos _
  have hEmono : Real.exp (2 * c) ≤ Real.exp (2 * u) := Real.exp_le_exp.mpr (by linarith)
  have hx : (3.156 : ℝ) ≤ π * (n : ℝ) ^ 2 * Real.exp (2 * u) := by
    have s1 : π * Real.exp (2 * c) ≤ π * Real.exp (2 * u) :=
      mul_le_mul_of_nonneg_left hEmono hpi.le
    have s2 : 1 * (π * Real.exp (2 * u)) ≤ (n : ℝ) ^ 2 * (π * Real.exp (2 * u)) :=
      mul_le_mul_of_nonneg_right hn2 (by positivity)
    nlinarith [s1, s2]
  have hP : 0 < 8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 -
      30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 15 := by
    nlinarith [sq_nonneg (π * (n : ℝ) ^ 2 * Real.exp (2 * u) - 3.156)]
  have hpos : 0 < π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
      Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
      (8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 -
        30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 15) :=
    mul_pos (mul_pos (mul_pos (by positivity) (Real.exp_pos _)) (Real.exp_pos _)) hP
  rw [phiTerm']
  nlinarith [hpos]

/-- `Φ' < 0` on `[c, ∞)` whenever `π e^{2c} ≥ 3.156`.-/
theorem deriv_Phi_neg {c : ℝ} (hc : (3.156 : ℝ) ≤ π * Real.exp (2 * c)) {x : ℝ} (hx : c ≤ x) :
    deriv Phi x < 0 := by
  rw [deriv_Phi]
  have hterm : ∀ n : ℕ, phiTerm' (n + 1) x < 0 := fun n =>
    phiTerm'_neg (Nat.le_add_left 1 n) hc hx
  have hsneg : Summable (fun n : ℕ => -phiTerm' (n + 1) x) := (summable_phiTerm'_succ x).neg
  have h1 : -phiTerm' (0 + 1) x ≤ ∑' n : ℕ, -phiTerm' (n + 1) x :=
    hsneg.le_tsum 0 (fun j _ => by linarith [hterm j])
  rw [tsum_neg] at h1
  linarith [hterm 0]

/-! ### Wintner's monotonicity theorem -/

/-- **Wintner monotonicity, general form.**  `Φ` is strictly decreasing on `[c, ∞)` for every
`c` with `π e^{2c} ≥ 3.156`.

A. Wintner, *A note on the Riemann ξ-function*, J. London Math. Soc. 10 (1935).  Mathlib has
nothing under this name (searched: `Wintner`, `wintner`); the entire termwise-derivative
apparatus above is built here.

**Sharpness of the hypothesis.**  `3.156` is a rational upper bound for
`(30+√420)/16 = 3.1558688…`, the larger root of `8x²−30x+15`.  The hypothesis therefore
holds for every `c > c₀ := ½ log((30+√420)/(16π)) = 0.00226697…` and for no smaller `c`,
and `c₀` is exactly where the *termwise* argument stops: for `0 ≤ u < c₀` the `n = 1`
summand of `Φ` is strictly **increasing**, and the sum is decreasing only because the
`n = 2` summand's decrease outweighs it.  See the module-level note at the bottom of this
file for why that last step cannot be recovered by any finite truncation.-/
theorem Phi_strictAntiOn_Ici {c : ℝ} (hc : (3.156 : ℝ) ≤ π * Real.exp (2 * c)) :
    StrictAntiOn Phi (Ici c) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici c) continuous_Phi.continuousOn (fun x hx => ?_)
  rw [interior_Ici] at hx
  exact deriv_Phi_neg hc (le_of_lt hx)

lemma le_pi_mul_exp_inv_four_hundred :
    (3.156 : ℝ) ≤ π * Real.exp (2 * (1 / 400 : ℝ)) := by
  have h1 : (201 / 200 : ℝ) ≤ Real.exp (2 * (1 / 400 : ℝ)) := by
    have := Real.add_one_le_exp (2 * (1 / 400) : ℝ); linarith
  have h2 : (3.14159265358979323846 : ℝ) < π := Real.pi_gt_d20
  have h3 : (3.14159265358979323846 : ℝ) * (201 / 200) ≤ π * Real.exp (2 * (1 / 400 : ℝ)) :=
    mul_le_mul h2.le h1 (by norm_num) (by linarith)
  have h4 : (3.156 : ℝ) ≤ (3.14159265358979323846 : ℝ) * (201 / 200) := by norm_num
  linarith

/-- **Wintner monotonicity, concrete form:** `Φ` is strictly decreasing on `[1/400, ∞)`.

`1/400 = 0.0025`, against a true threshold of `0.00226697…` for this method.-/
theorem Phi_strictAntiOn_Ici_inv_four_hundred : StrictAntiOn Phi (Ici (1 / 400 : ℝ)) :=
  Phi_strictAntiOn_Ici le_pi_mul_exp_inv_four_hundred

/-- Non-strict corollary.-/
theorem Phi_antitoneOn_Ici_inv_four_hundred : AntitoneOn Phi (Ici (1 / 400 : ℝ)) :=
  Phi_strictAntiOn_Ici_inv_four_hundred.antitoneOn

/-! ### The classical sine-transform positivity lemma

For a nonincreasing kernel on `[0,∞)` the sine transform is nonnegative, and for a
*strictly* decreasing one it is strictly positive.  This is Wintner (1947); the draft
paper's Lemma 6.5 (via Lagarias–Montague 2011) records it as classical.  It is proved
here for a general `g`, not for `Φ`.

**The strict-decrease hypothesis is not decoration.**  With `AntitoneOn` alone the strict
conclusion is *false*.  Fix `t > 0`, put `L = π/t`, and let `g` be the nonincreasing step
function equal to `4^{-k}` on `[2kL, 2(k+1)L)`.  Then `g` is strictly positive, antitone
on `[0,∞)` and integrable on `(0,∞)`, but `g` is constant on each full period of
`sin(t·)`, so every block integral vanishes and `∫₀^∞ g(u) sin(tu) du = 0` exactly.
Hence `sin_transform_nonneg` below is sharp, and `sin_transform_pos` needs `StrictAntiOn`.

Note also that positivity of `g` is never used: only monotonicity and integrability. -/

namespace SineTransform

open intervalIntegral

variable {g : ℝ → ℝ}

lemma antitoneOn_shift (hanti : AntitoneOn g (Ici (0 : ℝ))) {c : ℝ} (hc : 0 ≤ c) :
    AntitoneOn (fun s => g (s + c)) (Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  exact hanti (mem_Ici.mpr (by have := mem_Ici.mp hx; linarith))
    (mem_Ici.mpr (by have := mem_Ici.mp hy; linarith)) (by linarith)

/-- A monotone function is integrable on every compact subinterval of its domain.-/
lemma integrableOn_Icc_of_antitoneOn (hanti : AntitoneOn g (Ici (0 : ℝ))) {a b : ℝ}
    (ha : 0 ≤ a) : IntegrableOn g (Icc a b) volume := by
  rcases le_or_gt a b with hab | hab
  · exact (hanti.mono (fun x hx => le_trans ha hx.1)).integrableOn_isCompact isCompact_Icc
  · rw [Icc_eq_empty (not_le.mpr hab)]
    exact integrableOn_empty

lemma integrableOn_mul_sin {h : ℝ → ℝ} {S : Set ℝ} (hh : IntegrableOn h S volume) (t : ℝ) :
    IntegrableOn (fun u => h u * Real.sin (t * u)) S volume := by
  refine Integrable.mono' hh.abs
    (hh.aestronglyMeasurable.mul (Continuous.aestronglyMeasurable (by fun_prop))) ?_
  filter_upwards with u
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_sin_le_one _)

lemma intervalIntegrable_shift_mul_sin (hanti : AntitoneOn g (Ici (0 : ℝ))) (t : ℝ)
    {c a b : ℝ} (hc : 0 ≤ c) (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun s => g (s + c) * Real.sin (t * s)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact integrableOn_mul_sin (integrableOn_Icc_of_antitoneOn (antitoneOn_shift hanti hc) ha) t

lemma intervalIntegrable_mul_sin (hanti : AntitoneOn g (Ici (0 : ℝ))) (t : ℝ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun u => g u * Real.sin (t * u)) volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
  exact integrableOn_mul_sin (integrableOn_Icc_of_antitoneOn hanti ha) t

lemma intervalIntegrable_diff (hanti : AntitoneOn g (Ici (0 : ℝ))) {t : ℝ} (ht : 0 < t)
    {c : ℝ} (hc : 0 ≤ c) :
    IntervalIntegrable
      (fun s => (g (s + c) - g (s + π / t + c)) * Real.sin (t * s)) volume 0 (π / t) := by
  have hL : (0 : ℝ) < π / t := div_pos Real.pi_pos ht
  have h1 : IntervalIntegrable (fun s : ℝ => g (s + c) * Real.sin (t * s)) volume 0 (π / t) :=
    intervalIntegrable_shift_mul_sin hanti t hc le_rfl hL.le
  have h2 : IntervalIntegrable
      (fun s : ℝ => g (s + π / t + c) * Real.sin (t * s)) volume 0 (π / t) := by
    have h := intervalIntegrable_shift_mul_sin (g := g) hanti t (c := π / t + c)
      (by linarith) le_rfl hL.le
    simpa [add_assoc] using h
  have := h1.sub h2
  refine this.congr ?_
  intro s _
  ring

/-- **Folding a full period.**  If `sin (t(s+c)) = sin (ts)` — i.e. `c` is a whole number of
periods — then the integral of `g(u) sin(tu)` over the period starting at `c` collapses to a
single half-period integral of the nonnegative difference `g(s+c) − g(s+L+c)`.-/
lemma block_eq (hanti : AntitoneOn g (Ici (0 : ℝ))) {t : ℝ} (ht : 0 < t)
    {c : ℝ} (hc : 0 ≤ c) (hsin : ∀ s : ℝ, Real.sin (t * (s + c)) = Real.sin (t * s)) :
    (∫ u in c..(c + (π / t + π / t)), g u * Real.sin (t * u))
      = ∫ s in (0 : ℝ)..(π / t),
          (g (s + c) - g (s + π / t + c)) * Real.sin (t * s) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  set L : ℝ := π / t with hLdef
  have hL : (0 : ℝ) < L := div_pos Real.pi_pos ht
  have htL : t * L = π := by rw [hLdef]; field_simp
  -- A. translate the whole period back to the origin
  have hA : (∫ u in c..(c + (L + L)), g u * Real.sin (t * u))
      = ∫ s in (0 : ℝ)..(L + L), g (s + c) * Real.sin (t * s) := by
    have h1 := intervalIntegral.integral_comp_add_right
      (f := fun u : ℝ => g u * Real.sin (t * u)) (a := (0 : ℝ)) (b := L + L) c
    simp only [zero_add] at h1
    rw [show c + (L + L) = L + L + c by ring, ← h1]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    simp only [hsin s]
  -- B. split at the half period
  have hii1 : IntervalIntegrable (fun s : ℝ => g (s + c) * Real.sin (t * s)) volume 0 L :=
    intervalIntegrable_shift_mul_sin hanti t hc le_rfl hL.le
  have hii2 : IntervalIntegrable (fun s : ℝ => g (s + c) * Real.sin (t * s)) volume L (L + L) :=
    intervalIntegrable_shift_mul_sin hanti t hc hL.le (by linarith)
  have hB : (∫ s in (0 : ℝ)..(L + L), g (s + c) * Real.sin (t * s))
      = (∫ s in (0 : ℝ)..L, g (s + c) * Real.sin (t * s))
        + ∫ s in L..(L + L), g (s + c) * Real.sin (t * s) :=
    (intervalIntegral.integral_add_adjacent_intervals hii1 hii2).symm
  -- C. fold the negative half-period onto the positive one
  have hC : (∫ s in L..(L + L), g (s + c) * Real.sin (t * s))
      = ∫ r in (0 : ℝ)..L, -(g (r + L + c) * Real.sin (t * r)) := by
    have h1 := intervalIntegral.integral_comp_add_right
      (f := fun s : ℝ => g (s + c) * Real.sin (t * s)) (a := (0 : ℝ)) (b := L) L
    simp only [zero_add] at h1
    rw [← h1]
    refine intervalIntegral.integral_congr (fun r _ => ?_)
    show g (r + L + c) * Real.sin (t * (r + L)) = -(g (r + L + c) * Real.sin (t * r))
    rw [show t * (r + L) = t * r + π by rw [mul_add, htL], Real.sin_add_pi]
    ring
  -- D. recombine
  have hii3 : IntervalIntegrable
      (fun r : ℝ => -(g (r + L + c) * Real.sin (t * r))) volume 0 L := by
    have h := intervalIntegrable_shift_mul_sin (g := g) hanti t (c := L + c)
      (by linarith) le_rfl hL.le
    exact (by simpa [add_assoc] using h : IntervalIntegrable
      (fun r : ℝ => g (r + L + c) * Real.sin (t * r)) volume 0 L).neg
  have hD : (∫ s in (0 : ℝ)..L, g (s + c) * Real.sin (t * s))
        + (∫ r in (0 : ℝ)..L, -(g (r + L + c) * Real.sin (t * r)))
      = ∫ s in (0 : ℝ)..L, (g (s + c) - g (s + L + c)) * Real.sin (t * s) := by
    rw [← intervalIntegral.integral_add hii1 hii3]
    refine intervalIntegral.integral_congr (fun s _ => ?_)
    show g (s + c) * Real.sin (t * s) + -(g (s + L + c) * Real.sin (t * s))
      = (g (s + c) - g (s + L + c)) * Real.sin (t * s)
    ring
  rw [hA, hB, hC, hD]

lemma sin_nonneg_on (ht : 0 < t) {s : ℝ} (hs0 : 0 ≤ s) (hsL : s ≤ π / t) :
    0 ≤ Real.sin (t * s) := by
  refine Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) ?_
  have : t * s ≤ t * (π / t) := by nlinarith
  rwa [mul_div_cancel₀ _ (ne_of_gt ht)] at this

lemma sin_pos_on (ht : 0 < t) {s : ℝ} (hs0 : 0 < s) (hsL : s < π / t) :
    0 < Real.sin (t * s) := by
  refine Real.sin_pos_of_pos_of_lt_pi (by positivity) ?_
  have : t * s < t * (π / t) := by nlinarith
  rwa [mul_div_cancel₀ _ (ne_of_gt ht)] at this

lemma block_nonneg (hanti : AntitoneOn g (Ici (0 : ℝ))) {t : ℝ} (ht : 0 < t)
    {c : ℝ} (hc : 0 ≤ c) (hsin : ∀ s : ℝ, Real.sin (t * (s + c)) = Real.sin (t * s)) :
    0 ≤ ∫ u in c..(c + (π / t + π / t)), g u * Real.sin (t * u) := by
  have hL : (0 : ℝ) < π / t := div_pos Real.pi_pos ht
  rw [block_eq hanti ht hc hsin]
  refine intervalIntegral.integral_nonneg hL.le (fun s hs => ?_)
  obtain ⟨hs0, hsL⟩ := hs
  have h1 : g (s + π / t + c) ≤ g (s + c) :=
    hanti (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (by linarith)
  have h2 : 0 ≤ Real.sin (t * s) := sin_nonneg_on ht hs0 hsL
  have : 0 ≤ g (s + c) - g (s + π / t + c) := by linarith
  exact mul_nonneg this h2

lemma block_zero_pos (hstrict : StrictAntiOn g (Ici (0 : ℝ))) {t : ℝ} (ht : 0 < t) :
    0 < ∫ u in (0 : ℝ)..(0 + (π / t + π / t)), g u * Real.sin (t * u) := by
  have hanti := hstrict.antitoneOn
  have hL : (0 : ℝ) < π / t := div_pos Real.pi_pos ht
  rw [block_eq hanti ht le_rfl (fun s => by rw [add_zero])]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (intervalIntegrable_diff hanti ht le_rfl) (fun s hs => ?_) hL
  obtain ⟨hs0, hsL⟩ := hs
  have h1 : g (s + π / t + 0) < g (s + 0) :=
    hstrict (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (by linarith)
  have h2 : 0 < Real.sin (t * s) := sin_pos_on ht hs0 hsL
  have : 0 < g (s + 0) - g (s + π / t + 0) := by linarith
  exact mul_pos this h2

/-- Every period-block of `g(u) sin(tu)` starting at `k` full periods is nonnegative.-/
lemma block_k_nonneg (hanti : AntitoneOn g (Ici (0 : ℝ))) {t : ℝ} (ht : 0 < t) (k : ℕ) :
    0 ≤ ∫ u in ((k : ℝ) * (π / t + π / t))..(((k : ℝ) + 1) * (π / t + π / t)),
          g u * Real.sin (t * u) := by
  have ht0 : t ≠ 0 := ne_of_gt ht
  have hL : (0 : ℝ) < π / t := div_pos Real.pi_pos ht
  have hc : (0 : ℝ) ≤ (k : ℝ) * (π / t + π / t) := by positivity
  have hsin : ∀ s : ℝ,
      Real.sin (t * (s + (k : ℝ) * (π / t + π / t))) = Real.sin (t * s) := by
    intro s
    have hrw : t * (s + (k : ℝ) * (π / t + π / t)) = t * s + (k : ℝ) * (2 * π) := by
      field_simp; ring
    rw [hrw]
    exact Real.sin_periodic.nat_mul k (t * s)
  have := block_nonneg hanti ht hc hsin
  rwa [show (k : ℝ) * (π / t + π / t) + (π / t + π / t)
      = ((k : ℝ) + 1) * (π / t + π / t) by ring] at this

/-- The partial integral over `n` full periods dominates the very first block.-/
lemma first_block_le_partial (hanti : AntitoneOn g (Ici (0 : ℝ))) {t : ℝ} (ht : 0 < t)
    {n : ℕ} (hn : 1 ≤ n) :
    (∫ u in (0 : ℝ)..(0 + (π / t + π / t)), g u * Real.sin (t * u))
      ≤ ∫ u in (0 : ℝ)..((n : ℝ) * (π / t + π / t)), g u * Real.sin (t * u) := by
  have hL : (0 : ℝ) < π / t := div_pos Real.pi_pos ht
  have hii : ∀ k : ℕ, IntervalIntegrable (fun u : ℝ => g u * Real.sin (t * u)) volume
      ((k : ℝ) * (π / t + π / t)) (((k : ℕ) + 1 : ℕ) * (π / t + π / t)) := by
    intro k
    refine intervalIntegrable_mul_sin hanti t (by positivity) ?_
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    push_cast
    nlinarith
  have hsum := intervalIntegral.sum_integral_adjacent_intervals
    (f := fun u : ℝ => g u * Real.sin (t * u)) (μ := volume)
    (a := fun k : ℕ => (k : ℝ) * (π / t + π / t)) (n := n) (fun k _ => hii k)
  simp only [Nat.cast_zero, zero_mul] at hsum
  rw [← hsum]
  have hnonneg : ∀ k ∈ Finset.range n, (0 : ℝ) ≤
      ∫ u in ((k : ℝ) * (π / t + π / t))..(((k : ℕ) + 1 : ℕ) * (π / t + π / t)),
        g u * Real.sin (t * u) := by
    intro k _
    have := block_k_nonneg hanti ht k
    rwa [show (((k : ℕ) + 1 : ℕ) : ℝ) = (k : ℝ) + 1 by push_cast; ring]
  have h0 : (0 : ℕ) ∈ Finset.range n := Finset.mem_range.mpr hn
  have := Finset.single_le_sum hnonneg h0
  simpa using this

/-- **Sine-transform nonnegativity.**  For `g` nonincreasing on `[0,∞)` and integrable on
`(0,∞)`, and every `t > 0`, `∫₀^∞ g(u) sin(tu) du ≥ 0`.  Positivity of `g` is not needed.-/
theorem sin_transform_nonneg (hanti : AntitoneOn g (Ici (0 : ℝ)))
    (hint : IntegrableOn g (Ioi (0 : ℝ)) volume) {t : ℝ} (ht : 0 < t) :
    0 ≤ ∫ u in Ioi (0 : ℝ), g u * Real.sin (t * u) := by
  have hL : (0 : ℝ) < π / t := div_pos Real.pi_pos ht
  have hfi : IntegrableOn (fun u => g u * Real.sin (t * u)) (Ioi (0 : ℝ)) volume :=
    integrableOn_mul_sin hint t
  have hb : Tendsto (fun n : ℕ => (n : ℝ) * (π / t + π / t)) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (by linarith) tendsto_natCast_atTop_atTop
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hfi hb
  refine ge_of_tendsto hlim ?_
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  refine le_trans ?_ (first_block_le_partial hanti ht hn)
  simpa using block_nonneg hanti ht le_rfl (fun s => by rw [add_zero])

/-- **Sine-transform positivity (Wintner 1947; classical).**  For `g` *strictly* decreasing on
`[0,∞)` and integrable on `(0,∞)`, and every `t > 0`, `∫₀^∞ g(u) sin(tu) du > 0`.

The half-period pairing: on `[2kL, (2k+1)L]` and `[(2k+1)L, (2k+2)L]` (with `L = π/t`) the
sine lobes are mirror images, so the block integral equals
`∫₀^L (g(s+2kL) − g(s+(2k+1)L)) sin(ts) ds`, which is nonnegative because `g` decreases —
and strictly positive for `k = 0` because `g` decreases *strictly*.-/
theorem sin_transform_pos (hstrict : StrictAntiOn g (Ici (0 : ℝ)))
    (hint : IntegrableOn g (Ioi (0 : ℝ)) volume) {t : ℝ} (ht : 0 < t) :
    0 < ∫ u in Ioi (0 : ℝ), g u * Real.sin (t * u) := by
  have hanti := hstrict.antitoneOn
  have hL : (0 : ℝ) < π / t := div_pos Real.pi_pos ht
  have hfi : IntegrableOn (fun u => g u * Real.sin (t * u)) (Ioi (0 : ℝ)) volume :=
    integrableOn_mul_sin hint t
  have hb : Tendsto (fun n : ℕ => (n : ℝ) * (π / t + π / t)) atTop atTop :=
    Filter.Tendsto.atTop_mul_const (by linarith) tendsto_natCast_atTop_atTop
  have hlim := MeasureTheory.intervalIntegral_tendsto_integral_Ioi (0 : ℝ) hfi hb
  refine lt_of_lt_of_le (block_zero_pos hstrict ht) (ge_of_tendsto hlim ?_)
  filter_upwards [Filter.eventually_ge_atTop 1] with n hn
  exact first_block_le_partial hanti ht hn

end SineTransform

/-! ### Imaginary-axis nonvanishing — conditional on the `[0,∞)` upgrade

`F(it) = 2i ∫₀^∞ Φ(u) sin(tu) du`, so `sin_transform_pos` converts strict monotonicity of `Φ`
on `[0,∞)` directly into "no zero of `F` is purely imaginary".  What this file proves is
strict monotonicity on `[1/400, ∞)`, which is **not** enough: the half-period pairing must be
anchored at `0`, where the sine's zeros are, so no shifted version of the argument applies.
The theorem is therefore stated with `StrictAntiOn Phi (Ici 0)` as an explicit hypothesis —
it is fully proved, with no `sorry`, from that hypothesis. -/

theorem integrableOn_Phi : IntegrableOn Phi (Ioi (0 : ℝ)) volume := by
  refine integrableOn_of_le_envelope Phi (9 / 2) phiConst
    continuous_Phi.aestronglyMeasurable (fun u hu => ?_)
  rw [Real.norm_eq_abs, show (9 : ℝ) / 2 * u = 9 * u / 2 by ring]
  exact abs_Phi_le hu.le

/-- On the imaginary axis the odd channel is `2i` times the sine transform of `Φ`:
`sinh(itu) = i sin(tu)`.-/
theorem F_ofReal_mul_I (t : ℝ) :
    F ((t : ℂ) * Complex.I)
      = 2 * Complex.I * ((∫ u in Ioi (0 : ℝ), Phi u * Real.sin (t * u) : ℝ) : ℂ) := by
  have hpt : ∀ u : ℝ, ((Phi u : ℝ) : ℂ) * Complex.sinh ((t : ℂ) * Complex.I * (u : ℂ))
      = Complex.I * ((Phi u * Real.sin (t * u) : ℝ) : ℂ) := by
    intro u
    have h1 : (t : ℂ) * Complex.I * (u : ℂ) = ((t * u : ℝ) : ℂ) * Complex.I := by
      push_cast; ring
    rw [h1, Complex.sinh_mul_I, ← Complex.ofReal_sin]
    push_cast; ring
  rw [F]
  simp_rw [hpt]
  have hcast : (∫ a in Ioi (0 : ℝ), ((Phi a * Real.sin (t * a) : ℝ) : ℂ))
      = ((∫ u in Ioi (0 : ℝ), Phi u * Real.sin (t * u) : ℝ) : ℂ) := integral_ofReal
  rw [MeasureTheory.integral_const_mul, hcast]
  ring

lemma sin_transform_neg (t : ℝ) :
    (∫ u in Ioi (0 : ℝ), Phi u * Real.sin (-t * u))
      = -∫ u in Ioi (0 : ℝ), Phi u * Real.sin (t * u) := by
  rw [← MeasureTheory.integral_neg]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun u _ => ?_)
  rw [show -t * u = -(t * u) by ring, Real.sin_neg]
  ring

/-- **No zero of `F` is purely imaginary** — conditional on Wintner's theorem holding all the
way down to `0`.  Everything except that hypothesis is proved here.-/
theorem F_ne_zero_of_imag_of_strictAntiOn (h : StrictAntiOn Phi (Ici (0 : ℝ)))
    {t : ℝ} (ht : t ≠ 0) : F ((t : ℂ) * Complex.I) ≠ 0 := by
  have hJ : (∫ u in Ioi (0 : ℝ), Phi u * Real.sin (t * u)) ≠ 0 := by
    rcases lt_or_gt_of_ne ht with hneg | hpos
    · have hp := SineTransform.sin_transform_pos h integrableOn_Phi
        (show (0 : ℝ) < -t by linarith)
      rw [sin_transform_neg] at hp
      linarith
    · exact ne_of_gt (SineTransform.sin_transform_pos h integrableOn_Phi hpos)
  rw [F_ofReal_mul_I]
  exact mul_ne_zero (mul_ne_zero two_ne_zero Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr hJ)

/-! ### Why `StrictAntiOn Phi (Ici 0)` is not reachable termwise

`Φ` is **even** (`Φ(−u) = Φ(u)`), a consequence of the Jacobi theta functional equation, so
`Φ'(0) = 0` exactly.  Numerically, `Φ'(0) = 0` to 60 digits and `Φ''(0) = −16.73…`; `Φ` really
is strictly decreasing on all of `(0,∞)`, but the derivative *vanishes* at the endpoint.

The termwise data at `u = 0`, with `Φ'(u) = −e^{5u/2} ∑_{n≥1} πn² e^{−x_n}(8x_n²−30x_n+15)`
and `x_n = πn² e^{2u}`:

| `n` | contribution to `Φ'(0)` |
|---|---|
| 1 | `+0.0394977…` (positive: `8π²−30π+15 = −0.29094… < 0`) |
| 2 | `−0.0394982…` |
| ≥3 | `−8.265…e−8` |

The `n = 1` summand is strictly *increasing* on `[0, c₀)`, `c₀ = 0.00226697…`, and the sum of
the first two terms at `u = 0` is `+8.265e−8 > 0`: it is only the `n ≥ 3` tail that cancels it
to exactly zero.  So **no finite truncation** of the series has nonpositive derivative at `0`,
and the identity `Φ'(0) = 0` cannot be obtained by estimating — it must be *derived*, from the
functional equation.  Mathlib has `jacobiTheta_S_smul` (one-variable, complex `τ`, first
`z`-derivatives only); `Φ` needs the **second** `τ`-derivative series, which Mathlib does not
have (`Kernel.lean`'s implementation notes reach the same conclusion for a different reason).
That is the concrete remaining work for `Ici 0`, and it is a substantial piece in its own
right, not a missing tactic call. -/

end XiLab

/-! ### Axiom audit -/
section AxiomAudit
end AxiomAudit
