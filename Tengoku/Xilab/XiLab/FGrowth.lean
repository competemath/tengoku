import Tengoku
import Tengoku.Xilab.XiLab.Growth
import Tengoku.Xilab.XiLab.Kernel
import Tengoku.Xilab.XiLab.GammaBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms XiLab.exp_envelope_sharp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.mul_log_le_rpow` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.norm_F_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.hasOrderLeOne_F` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.hasOrderLeOne_of_gamma_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.F_neg` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.FGrowth — the odd channel `F` has order at most one

This is the *join* between
`XiLab/Kernel.lean` (which supplies `Φ`, its decay envelope, and entirety of `F`) and
`XiLab/GammaBounds.lean` (which supplies the Stirling-type `x log x` envelope).

## Main results

* `XiLab.exp_envelope_sharp` — the sharp replacement for `Kernel.exp_envelope_le`:
  for `b ≥ 1` and **every** real `u`,
  `e^{(b-1)u} e^{−π e^{2u}} ≤ e^{(b/2) log b} · e^{−u}`.
* `XiLab.norm_F_le` — `‖F w‖ ≤ 2 C exp ((b/2) log b)` with `b = 11/2 + ‖w‖`,
  `C = phiConst`.  This is `log M(r) ≤ (r/2) log r + O(r)`.
* `XiLab.hasOrderLeOne_F` — `XiLab.HasOrderLeOne XiLab.F`.
* `XiLab.F_neg` — `F` is odd, `F (-w) = -F w`.

## Why the route below and not the substitution `y = e^{2u}`

The intended path was
`∫₀^∞ e^{(9/2+r)u} e^{−π e^{2u}} du = ½ ∫₁^∞ y^{(r/2+9/4)−1} e^{−πy} dy
   ≤ ½ Γ(r/2+9/4) / π^{r/2+9/4}`,
then `GammaBounds.log_Gamma_shift_le_rpow`.  Mathematically that is the sharp
statement, and it is what the paper records.  In Lean the change of variables costs a
genuine `integral_comp_mul_deriv`-style argument on a *non-compact* interval, and then
a second argument to recognise the truncated integral as a `Real.GammaIntegral`.

The route taken here is the same estimate with the maximisation done *pointwise before*
integrating rather than *after*: `exp_envelope_sharp` is exactly the statement that
`sup_{u} (b u − π e^{2u}) = (b/2) log (b/(2π)) − b/2`, which is the Laplace-method value
of the same integral, and it is proved from `Real.log_le_sub_one_of_pos` alone — the
Legendre-transform identity `log s ≤ s − 1`.  Since the residual factor is `e^{−u}`,
which integrates to `1` on `(0,∞)`, the constant is not even lost.  Compare
`Kernel.exp_envelope_le`, which uses `e^{2u} ≥ 2u²` and therefore only certifies the
*quadratic* exponent `(a+1)²/(8π)`, i.e. order ≤ 2.  Replacing `e^{2u} ≥ 2u²` by the
exact Legendre transform is precisely the missing half.

`GammaBounds` still supplies the shape of the last step (`x log x ≤ x^{1+ε}/ε`); it is
restated here as `XiLab.mul_log_le_rpow` because the version in `GammaBounds` is fused
to `Real.log ∘ Real.Gamma`.
-/

open scoped Real
open MeasureTheory Set Filter Topology

namespace XiLab

/-! ### The sharp exponential envelope

`Kernel.exp_envelope_le` bounds `e^{au} e^{−π e^{2u}}` by `e^{(a+1)²/(8π)} e^{−u}`,
which is quadratic in `a` and hence only gives order ≤ 2.  The true supremum of
`b u − π e^{2u}` over `u ∈ ℝ` is `(b/2) log (b/(2π)) − b/2`, attained at
`e^{2u} = b/(2π)`.  The proof is the substitution `s = 2π e^{2u} / b`, which turns the
claim into `log s ≤ s − 1`. -/

/-- **The sharp envelope.**  For `b ≥ 1` and every real `u`,
`e^{(b−1)u} · e^{−π e^{2u}} ≤ e^{(b/2) log b} · e^{−u}`.

Only `Real.log_le_sub_one_of_pos` is used; the slack discarded at the end is
`(b/2) log (2π) + b/2 ≥ 0`, i.e. the difference between `(b/2) log b` and the exact
supremum `(b/2) log (b/(2π)) − b/2`.-/
theorem exp_envelope_sharp {b : ℝ} (hb : 1 ≤ b) (u : ℝ) :
    Real.exp ((b - 1) * u) * Real.exp (-(π * Real.exp (2 * u))) ≤
      Real.exp (b / 2 * Real.log b) * Real.exp (-u) := by
  have hpi := Real.pi_pos
  have hb0 : (0 : ℝ) < b := by linarith
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  set s : ℝ := 2 * π * Real.exp (2 * u) / b with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  have hlog : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
  have hlogs : Real.log s = Real.log (2 * π) + 2 * u - Real.log b := by
    rw [hsdef, Real.log_div (by positivity) hb0.ne',
      Real.log_mul (by positivity) (Real.exp_ne_zero _), Real.log_exp]
  have hsval : b / 2 * s = π * Real.exp (2 * u) := by
    rw [hsdef]; field_simp
  have hmul : b / 2 * Real.log s ≤ b / 2 * (s - 1) :=
    mul_le_mul_of_nonneg_left hlog (by positivity)
  rw [hlogs] at hmul
  have hlog2pi : 0 ≤ Real.log (2 * π) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  nlinarith [hmul, hsval, mul_nonneg hb0.le hlog2pi]

/-! ### The `x log x ≤ x^{1+ε}/ε` step

This is the inner content of `GammaBounds.log_Gamma_le_rpow`, restated for a bare real
argument. -/

/-- `x log x ≤ x^{1+ε} / ε` for `x ≥ 1` and `ε > 0`.-/
theorem mul_log_le_rpow {ε : ℝ} (hε : 0 < ε) {x : ℝ} (hx : 1 ≤ x) :
    x * Real.log x ≤ x ^ (1 + ε) / ε := by
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : Real.log x ≤ x ^ ε / ε := by
    have h := Real.log_le_sub_one_of_pos (Real.rpow_pos_of_pos hx0 ε)
    rw [Real.log_rpow hx0] at h
    rw [le_div_iff₀ hε]
    nlinarith [h]
  have hxr : x ^ (1 + ε) = x * x ^ ε := by rw [Real.rpow_add hx0, Real.rpow_one]
  rw [hxr]
  calc x * Real.log x ≤ x * (x ^ ε / ε) := mul_le_mul_of_nonneg_left hlog hx0.le
    _ = x * x ^ ε / ε := by ring

/-! ### The growth bound for `F` -/

/-- **Proposition 3.2 (growth of the odd channel).**  With `r = ‖w‖` and
`b = 11/2 + r`,
`‖F(w)‖ ≤ 2 · phiConst · exp ((b/2) log b)`.

Since `(b/2) log b = (r/2) log r + O(r)`, this is exactly the paper's
`log max_{‖w‖ = r} ‖F‖ ≤ (r/2) log r + O(r)`.  The `9/2` in the exponent of the kernel
envelope and the `+1` absorbed to leave an integrable `e^{−u}` are what turn `r` into
`11/2 + r`; the paper's `Γ(r/2 + 9/4)` has the same leading behaviour.-/
theorem norm_F_le (w : ℂ) :
    ‖F w‖ ≤ 2 * phiConst *
      Real.exp ((11 / 2 + ‖w‖) / 2 * Real.log (11 / 2 + ‖w‖)) := by
  have hw : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  have hb1 : (1 : ℝ) ≤ 11 / 2 + ‖w‖ := by linarith
  set K : ℝ := (11 / 2 + ‖w‖) / 2 * Real.log (11 / 2 + ‖w‖) with hKdef
  -- pointwise domination of the integrand by an integrable exponential
  have hbound : ∀ᵐ u ∂(volume.restrict (Ioi (0 : ℝ))),
      ‖(Phi u : ℂ) * Complex.sinh (w * u)‖ ≤
        phiConst * Real.exp K * Real.exp (-1 * u) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
    have hu0 : (0 : ℝ) < u := mem_Ioi.mp hu
    have h1 : ‖(Phi u : ℂ) * Complex.sinh (w * u)‖ ≤
        phiConst *
          (Real.exp ((9 / 2 + ‖w‖) * u) * Real.exp (-(π * Real.exp (2 * u)))) := by
      refine norm_Phi_mul_le hu0 ‖w‖ _ ?_
      refine (norm_complex_sinh_le _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul_ofReal w hu0.le]
    have h2 := exp_envelope_sharp hb1 u
    rw [show 11 / 2 + ‖w‖ - 1 = 9 / 2 + ‖w‖ by ring, ← hKdef] at h2
    calc ‖(Phi u : ℂ) * Complex.sinh (w * u)‖
        ≤ phiConst *
            (Real.exp ((9 / 2 + ‖w‖) * u) * Real.exp (-(π * Real.exp (2 * u)))) := h1
      _ ≤ phiConst * (Real.exp K * Real.exp (-u)) :=
          mul_le_mul_of_nonneg_left h2 phiConst_nonneg
      _ = phiConst * Real.exp K * Real.exp (-1 * u) := by rw [neg_one_mul]; ring
  have hg : Integrable (fun u : ℝ => phiConst * Real.exp K * Real.exp (-1 * u))
      (volume.restrict (Ioi (0 : ℝ))) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).const_mul _
  have hle := norm_integral_le_of_norm_le hg hbound
  have hval : (∫ u in Ioi (0 : ℝ), phiConst * Real.exp K * Real.exp (-1 * u))
      = phiConst * Real.exp K := by
    simp only [neg_one_mul]
    rw [integral_const_mul, integral_exp_neg_Ioi_zero, mul_one]
  rw [hval] at hle
  calc ‖F w‖ = 2 * ‖∫ u in Ioi (0 : ℝ), (Phi u : ℂ) * Complex.sinh (w * u)‖ := by
        simp only [F, norm_mul]
        norm_num
    _ ≤ 2 * (phiConst * Real.exp K) := by linarith
    _ = 2 * phiConst * Real.exp K := by ring

/-- Elementary splitting bound: `(c + r)^p ≤ (2c)^p + 2^p r^p` for `c, r ≥ 0`, `p ≥ 0`.
Split at `r = c`: below it `c + r ≤ 2c`, above it `c + r ≤ 2r`.  This is what turns a
bound in `‖w‖ + const` into a bound in `‖w‖` with an `ε`-dependent constant.-/
theorem rpow_add_const_le {c p r : ℝ} (hc : 0 ≤ c) (hp : 0 ≤ p) (hr : 0 ≤ r) :
    (c + r) ^ p ≤ (2 * c) ^ p + 2 ^ p * r ^ p := by
  have h2p : (0 : ℝ) ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num) p
  have hrp : (0 : ℝ) ≤ r ^ p := Real.rpow_nonneg hr p
  have hcp : (0 : ℝ) ≤ (2 * c) ^ p := Real.rpow_nonneg (by linarith) p
  rcases le_or_gt r c with h | h
  · have : (c + r) ^ p ≤ (2 * c) ^ p :=
      Real.rpow_le_rpow (by linarith) (by linarith) hp
    nlinarith
  · have hmul : (c + r) ^ p ≤ (2 * r) ^ p :=
      Real.rpow_le_rpow (by linarith) (by linarith) hp
    rw [Real.mul_rpow (by norm_num) hr] at hmul
    linarith

/-- The specialisation used below: `(11/2 + r)^p ≤ 11^p + 2^p r^p`.-/
theorem rpow_shift_le {p r : ℝ} (hp : 0 ≤ p) (hr : 0 ≤ r) :
    (11 / 2 + r) ^ p ≤ (11 : ℝ) ^ p + 2 ^ p * r ^ p := by
  have := rpow_add_const_le (c := 11 / 2) (p := p) (r := r) (by norm_num) hp hr
  rw [show (2 : ℝ) * (11 / 2) = 11 by norm_num] at this
  exact this

/-- **Theorem 3.3 (growth half).**  `F` has order at most one.-/
theorem hasOrderLeOne_F : HasOrderLeOne F := by
  intro ε hε
  set p : ℝ := 1 + ε with hpdef
  have hp1 : (1 : ℝ) ≤ p := by rw [hpdef]; linarith
  have hp0 : (0 : ℝ) ≤ p := by linarith
  set A : ℝ := (11 : ℝ) ^ p / (2 * ε) with hAdef
  set B : ℝ := (2 : ℝ) ^ p / (2 * ε) with hBdef
  have hB0 : 0 ≤ B := by
    rw [hBdef]; positivity
  set C : ℝ := max (2 * phiConst * Real.exp A) B + 1 with hCdef
  have hCpos : 0 < C := by
    have h1 : (0 : ℝ) ≤ 2 * phiConst * Real.exp A := by
      have := phiConst_nonneg; positivity
    have : (0 : ℝ) ≤ max (2 * phiConst * Real.exp A) B := le_trans h1 (le_max_left _ _)
    rw [hCdef]; linarith
  refine ⟨C, hCpos, fun z => ?_⟩
  have hr : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hb1 : (1 : ℝ) ≤ 11 / 2 + ‖z‖ := by linarith
  set b : ℝ := 11 / 2 + ‖z‖ with hbdef
  -- Step 1: the kernel bound
  have h1 := norm_F_le z
  rw [← hbdef] at h1
  -- Step 2: (b/2) log b ≤ b^p / (2ε)
  have h2 : b / 2 * Real.log b ≤ b ^ p / (2 * ε) := by
    have := mul_log_le_rpow hε hb1
    rw [← hpdef] at this
    have h2ε : (0 : ℝ) < 2 * ε := by linarith
    rw [le_div_iff₀ h2ε]
    have hbp : b * Real.log b ≤ b ^ p / ε := this
    rw [le_div_iff₀ hε] at hbp
    nlinarith [hbp]
  -- Step 3: b^p ≤ 11^p + 2^p ‖z‖^p
  have h3 : b ^ p ≤ (11 : ℝ) ^ p + 2 ^ p * ‖z‖ ^ p := by
    rw [hbdef]; exact rpow_shift_le hp0 hr
  have h2ε : (0 : ℝ) < 2 * ε := by linarith
  have h4 : b / 2 * Real.log b ≤ A + B * ‖z‖ ^ p := by
    have : b ^ p / (2 * ε) ≤ ((11 : ℝ) ^ p + 2 ^ p * ‖z‖ ^ p) / (2 * ε) := by
      gcongr
    rw [hAdef, hBdef]
    calc b / 2 * Real.log b ≤ b ^ p / (2 * ε) := h2
      _ ≤ ((11 : ℝ) ^ p + 2 ^ p * ‖z‖ ^ p) / (2 * ε) := this
      _ = (11 : ℝ) ^ p / (2 * ε) + 2 ^ p / (2 * ε) * ‖z‖ ^ p := by ring
  -- Step 4: assemble
  have hrp : (0 : ℝ) ≤ ‖z‖ ^ p := Real.rpow_nonneg hr p
  have hBC : B ≤ C := by
    have : B ≤ max (2 * phiConst * Real.exp A) B := le_max_right _ _
    rw [hCdef]; linarith
  have hAC : 2 * phiConst * Real.exp A ≤ C := by
    have : 2 * phiConst * Real.exp A ≤ max (2 * phiConst * Real.exp A) B := le_max_left _ _
    rw [hCdef]; linarith
  calc ‖F z‖ ≤ 2 * phiConst * Real.exp (b / 2 * Real.log b) := h1
    _ ≤ 2 * phiConst * Real.exp (A + B * ‖z‖ ^ p) := by
        have hnn : (0 : ℝ) ≤ 2 * phiConst := by have := phiConst_nonneg; positivity
        exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr h4) hnn
    _ = 2 * phiConst * Real.exp A * Real.exp (B * ‖z‖ ^ p) := by
        rw [Real.exp_add]; ring
    _ ≤ C * Real.exp (C * ‖z‖ ^ p) := by
        refine mul_le_mul hAC (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hCpos.le
        exact mul_le_mul_of_nonneg_right hBC hrp

/-! ### The paper's Gamma-form envelope also lands (the `GammaBounds` route)

`norm_F_le` bypasses `Real.Gamma` entirely.  The paper states the envelope in the Gamma
form `‖F(w)‖ ≤ M · Γ(r/2 + 9/4) / π^{r/2 + 9/4}`, which follows from the same kernel
bound after the substitution `y = e^{2u}`.  That substitution is *not* formalised here
(see the module docstring for why), but the implication from it is — so the Gamma route
is one change-of-variables lemma away from `hasOrderLeOne_F`, and this is where
`XiLab/GammaBounds.lean` is consumed. -/

/-- **The Gamma envelope implies order ≤ 1.**  If `‖f w‖ ≤ M Γ(‖w‖/2 + 9/4) / π^{‖w‖/2+9/4}`
for every `w`, then `f` has order at most one.  Uses `GammaBounds.Gamma_le_exp_rpow`.-/
theorem hasOrderLeOne_of_gamma_bound {f : ℂ → ℂ} {M : ℝ} (hM : 0 < M)
    (h : ∀ w : ℂ, ‖f w‖ ≤ M * (Real.Gamma (‖w‖ / 2 + 9 / 4) / π ^ (‖w‖ / 2 + 9 / 4))) :
    HasOrderLeOne f := by
  intro ε hε
  set p : ℝ := 1 + ε with hpdef
  have hp0 : (0 : ℝ) ≤ p := by rw [hpdef]; linarith
  set A : ℝ := ((9 : ℝ) / 2) ^ p / ε with hAdef
  set B : ℝ := (2 : ℝ) ^ p / ε with hBdef
  have hB0 : 0 ≤ B := by rw [hBdef]; positivity
  set C : ℝ := max (M * Real.exp A) B + 1 with hCdef
  have hCpos : 0 < C := by
    have h1 : (0 : ℝ) ≤ M * Real.exp A := by positivity
    have : (0 : ℝ) ≤ max (M * Real.exp A) B := le_trans h1 (le_max_left _ _)
    rw [hCdef]; linarith
  have hBC : B ≤ C := by
    have : B ≤ max (M * Real.exp A) B := le_max_right _ _
    rw [hCdef]; linarith
  have hAC : M * Real.exp A ≤ C := by
    have : M * Real.exp A ≤ max (M * Real.exp A) B := le_max_left _ _
    rw [hCdef]; linarith
  refine ⟨C, hCpos, fun z => ?_⟩
  have hr : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
  have hrp : (0 : ℝ) ≤ ‖z‖ ^ p := Real.rpow_nonneg hr p
  set x : ℝ := ‖z‖ / 2 + 9 / 4 with hxdef
  have hx1 : (1 : ℝ) ≤ x := by rw [hxdef]; linarith
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hgam : Real.Gamma x ≤ Real.exp (x ^ p / ε) := by
    have hg := Gamma_le_exp_rpow hε hx1
    rw [← hpdef] at hg
    exact hg
  have hpi1 : (1 : ℝ) ≤ π ^ x := Real.one_le_rpow (by linarith [Real.pi_gt_three]) hx0
  have hgpos : 0 ≤ Real.Gamma x := (Real.Gamma_pos_of_pos (by linarith)).le
  have hdiv : Real.Gamma x / π ^ x ≤ Real.Gamma x := div_le_self hgpos hpi1
  have hxp : x ^ p ≤ ((9 : ℝ) / 2) ^ p + 2 ^ p * ‖z‖ ^ p := by
    have hle : x ≤ 9 / 4 + ‖z‖ := by rw [hxdef]; linarith
    have h1 : x ^ p ≤ (9 / 4 + ‖z‖) ^ p := Real.rpow_le_rpow hx0 hle hp0
    have h2 := rpow_add_const_le (c := (9 : ℝ) / 4) (p := p) (r := ‖z‖) (by norm_num) hp0 hr
    rw [show (2 : ℝ) * (9 / 4) = 9 / 2 by norm_num] at h2
    linarith
  have hexpo : x ^ p / ε ≤ A + B * ‖z‖ ^ p := by
    have hd : x ^ p / ε ≤ (((9 : ℝ) / 2) ^ p + 2 ^ p * ‖z‖ ^ p) / ε := by gcongr
    rw [hAdef, hBdef]
    calc x ^ p / ε ≤ (((9 : ℝ) / 2) ^ p + 2 ^ p * ‖z‖ ^ p) / ε := hd
      _ = ((9 : ℝ) / 2) ^ p / ε + (2 : ℝ) ^ p / ε * ‖z‖ ^ p := by ring
  calc ‖f z‖ ≤ M * (Real.Gamma x / π ^ x) := by
        have hz := h z; rw [← hxdef] at hz; exact hz
    _ ≤ M * Real.exp (x ^ p / ε) := mul_le_mul_of_nonneg_left (hdiv.trans hgam) hM.le
    _ ≤ M * Real.exp (A + B * ‖z‖ ^ p) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexpo) hM.le
    _ = M * Real.exp A * Real.exp (B * ‖z‖ ^ p) := by rw [Real.exp_add]; ring
    _ ≤ C * Real.exp (C * ‖z‖ ^ p) := by
        refine mul_le_mul hAC (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le hCpos.le
        exact mul_le_mul_of_nonneg_right hBC hrp

/-! ### Oddness of `F`

Cheap, and the downstream quartet-symmetry argument wants it. -/

/-- `F` is odd: `F (-w) = -F w`.  Immediate from `sinh (-z) = -sinh z`.-/
theorem F_neg (w : ℂ) : F (-w) = -F w := by
  have hpt : ∀ u : ℝ,
      (Phi u : ℂ) * Complex.sinh (-w * u) = -((Phi u : ℂ) * Complex.sinh (w * u)) := by
    intro u
    rw [neg_mul, Complex.sinh_neg, mul_neg]
  simp only [F, hpt, integral_neg, mul_neg]

end XiLab

/-! ### Target signature, pinned verbatim -/

/-! ### Axiom audit -/

