import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms XiLab.summable_phiTerm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Phi_eq_tsum` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.continuous_Phi` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Phi_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.summable_envTerm` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.abs_Phi_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.exp_envelope_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.abs_Phi_mul_exp_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.tendsto_Phi_mul_exp_atTop` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.integrableOn_exp_envelope` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.integrableOn_Phi_mul_sinh` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.integrableOn_Phi_mul_rsinh` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.differentiableAt_integral_Phi_sinh` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.differentiable_F` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.Kernel — the Riemann–Titchmarsh kernel `Φ` and the odd channel `F`

## Contents

* `XiLab.Phi : ℝ → ℝ` — the kernel
  `Φ(u) = ∑_{n≥1} (4π²n⁴ e^{9u/2} − 6πn² e^{5u/2}) e^{−π n² e^{2u}}`
  of Titchmarsh's integral representation, in the normalization of Spira (1971) and
  Lagarias–Montague (2011).
* `XiLab.summable_phiTerm` — the defining series converges for **every** real `u`.
* `XiLab.continuous_Phi` — `Φ` is continuous on `ℝ`.
* `XiLab.Phi_pos` — `0 < Φ u` for `u ≥ 0` (every summand is already positive there).
* `XiLab.abs_Phi_le` — the decay envelope
  `|Φ(u)| ≤ C e^{9u/2} e^{−π e^{2u}}` for `u ≥ 0`, with `C = XiLab.phiConst`.
* `XiLab.abs_Phi_mul_exp_le`, `XiLab.tendsto_Phi_mul_exp_atTop` — the superexponential
  decay in explicit `e^{−u}` form, and `Φ(u)e^{au} → 0` for every real `a`.
* `XiLab.integrableOn_Phi_mul_sinh` — `u ↦ Φ(u) sinh(wu)` is integrable on `(0, ∞)` for
  every `w : ℂ`.  This is what makes the odd channel converge.
* `XiLab.F : ℂ → ℂ`, `F w = 2 ∫_{(0,∞)} Φ(u) sinh(wu) du`, and
  `XiLab.differentiable_F : Differentiable ℂ F` — `F` is entire.

## Implementation notes

Everything is done on the **raw series**, not through Mathlib's `jacobiTheta`.  Both
routes were assessed against the actual Mathlib source; the raw route won, but not for
the reason one might guess, so the evidence is recorded here.

*What Mathlib's theta API does have.*  `Mathlib/NumberTheory/ModularForms/JacobiTheta/`
supplies `jacobiTheta`, `hasSum_nat_jacobiTheta`, `jacobiTheta_S_smul`,
`differentiableAt_jacobiTheta`, and — for the two-variable theta — a genuine termwise
**first**-derivative series: `jacobiTheta₂_term_fderiv`, `hasSum_jacobiTheta₂_term_fderiv`,
`jacobiTheta₂_fderiv`, `hasFDerivAt_jacobiTheta₂`.  Moreover
`HurwitzKernelBounds.summable_f_nat` in `JacobiTheta/Bounds.lean` states exactly that
`n ↦ (n+a)^k e^{−π(n+a)² t}` is summable for `t > 0`, which covers the summability
deliverable on its own.

*Where it stops.*  `Φ` needs `∑ n⁴ e^{−π n² x}` as well as `∑ n² e^{−π n² x}` — that is
the **second** derivative in `τ`, and Mathlib has no second-`τ`-derivative series
(`jacobiTheta₂''` in `LSeries/HurwitzZetaOdd.lean` is a combination of `z`-derivatives,
not that).  The theta objects also live in `ℂ` on the half-plane `0 < im τ`, while `Φ` is
a real function of `u`, so every estimate would be recast through `τ = i e^{2u}`.

*The deciding factor.*  A single inequality, `abs_phiTerm_le`
(`|phiTerm n u| ≤ C(u) · n⁴ · r(u)^n` with `r(u) = e^{−π e^{2u}} < 1`), serves **all three**
of summability, local-uniform continuity on `Icc a b`, and — in the sharpened form
`abs_phiTerm_le_envTerm` — the `e^{9u/2} e^{−π e^{2u}}` decay envelope.  Mathlib's theta
bounds are asymptotics in `im τ → ∞`; none of them has that shape, so the theta route
would supply at most the summability and leave the other two to be done here anyway.

The `n = 0` summand `phiTerm 0 u` vanishes identically, so `∑' n : ℕ, phiTerm n u` and
`∑' n : ℕ, phiTerm (n+1) u` agree (`XiLab.Phi_eq_tsum`).  `Phi` is *defined* with the
`n+1` shift, matching the paper's `∑_{n≥1}`; estimates use the unshifted form.
-/

open scoped Real
open MeasureTheory Set Filter Topology

namespace XiLab

/-- The `n`-th summand of the Riemann–Titchmarsh kernel series.-/
noncomputable def phiTerm (n : ℕ) (u : ℝ) : ℝ :=
  (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
      6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
    Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))

/--
@isnad1 id=eq.0h1v.s4.99ae5907bd70 from=translated src=- shape=a0dd47fb vocab=10e4e59c
-/
@[simp] lemma phiTerm_zero (u : ℝ) : phiTerm 0 u = 0 := by simp [phiTerm]

/--
@isnad1 id=continuo.0h1v.s4.90ba27f7af28 from=translated src=- shape=8735051e vocab=1e01c515
-/
lemma continuous_phiTerm (n : ℕ) : Continuous (phiTerm n) := by
  unfold phiTerm; fun_prop

/--
@isnad1 id=le.0h1v.s5.804a20e5adaa from=translated src=- shape=00a8e044 vocab=ef525443
-/
lemma cast_sq_le_pow_four (n : ℕ) : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    nlinarith [sq_nonneg ((n:ℝ)^2 - 1), sq_nonneg ((n:ℝ) - 1)]

/--
@isnad1 id=le.0h1v.s4.198a9fe3ed27 from=translated src=- shape=c03bf12e vocab=ef525443
-/
lemma cast_le_sq (n : ℕ) : (n : ℝ) ≤ (n : ℝ) ^ 2 := by
  rcases Nat.eq_zero_or_pos n with h | h
  · simp [h]
  · have : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast h
    nlinarith

/-- Crude termwise bound: replace the difference of the two positive pieces by their sum.
@isnad1 id=le.0h2v.s8.66116abeba05 from=translated src=- shape=f159e038 vocab=e3910967
-/
lemma abs_phiTerm_le_aux (n : ℕ) (u : ℝ) :
    |phiTerm n u| ≤
      (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) +
        6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
      Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) := by
  have hpi := Real.pi_pos
  have hA : (0:ℝ) ≤ 4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) := by positivity
  have hB : (0:ℝ) ≤ 6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) := by positivity
  have habs : |4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
      6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)| ≤
      4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) +
      6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  calc |phiTerm n u|
      = |4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) -
          6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)| *
            Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) := by
        rw [phiTerm, abs_mul, abs_of_pos (Real.exp_pos _)]
    _ ≤ _ := mul_le_mul_of_nonneg_right habs (Real.exp_pos _).le

/-- Master termwise bound, valid for every real `u`: the `n`-th term is dominated by
`C(u) * n^4 * r(u)^n` with `r(u) = exp (-π e^{2u}) ∈ (0,1)`.
@isnad1 id=le.0h2v.s7.2a73d4eede71 from=translated src=- shape=960742ff vocab=e3910967
-/
lemma abs_phiTerm_le (n : ℕ) (u : ℝ) :
    |phiTerm n u| ≤
      (4 * π ^ 2 * Real.exp (9 * u / 2) + 6 * π * Real.exp (5 * u / 2)) *
        ((n : ℝ) ^ 4 * Real.exp (-(π * Real.exp (2 * u))) ^ n) := by
  have hpi := Real.pi_pos
  have hx0 : (0:ℝ) < Real.exp (2 * u) := Real.exp_pos _
  have hsq := cast_sq_le_pow_four n
  have hE : Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) ≤
      Real.exp (-(π * Real.exp (2 * u))) ^ n := by
    rw [← Real.exp_nat_mul]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_right (cast_le_sq n) (le_of_lt (mul_pos hpi hx0))]
  have hA : (0:ℝ) ≤ 4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) := by positivity
  have hB : (0:ℝ) ≤ 6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) := by positivity
  calc |phiTerm n u|
      ≤ (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) +
          6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
            Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) := abs_phiTerm_le_aux n u
    _ ≤ (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) +
          6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
            Real.exp (-(π * Real.exp (2 * u))) ^ n :=
        mul_le_mul_of_nonneg_left hE (by linarith)
    _ ≤ (4 * π ^ 2 * Real.exp (9 * u / 2) + 6 * π * Real.exp (5 * u / 2)) *
          ((n : ℝ) ^ 4 * Real.exp (-(π * Real.exp (2 * u))) ^ n) := by
        have hpow : (0:ℝ) ≤ Real.exp (-(π * Real.exp (2 * u))) ^ n :=
          pow_nonneg (Real.exp_pos _).le n
        have h5 : (0:ℝ) < Real.exp (5 * u / 2) := Real.exp_pos _
        nlinarith [mul_le_mul_of_nonneg_left hsq
          (by positivity : (0:ℝ) ≤ 6 * π * Real.exp (5 * u / 2))]

/--
@isnad1 id=lt.0h1v.s5.7b3a3ed6a969 from=translated src=- shape=368bd6bf vocab=92d2f1ee
-/
lemma norm_exp_neg_pi_exp_lt_one (u : ℝ) :
    ‖Real.exp (-(π * Real.exp (2 * u)))‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  rw [Real.exp_lt_one_iff]
  have : (0:ℝ) < π * Real.exp (2 * u) := mul_pos Real.pi_pos (Real.exp_pos _)
  linarith

/-- **Summability of the defining series of `Φ`**, for every real `u`.
@isnad1 id=summable.0h1v.s4.305d40ae9d27 from=translated src=- shape=0b46e227 vocab=9d84262b
-/
theorem summable_phiTerm (u : ℝ) : Summable (fun n : ℕ => phiTerm n u) := by
  have hs :=
    (summable_pow_mul_geometric_of_norm_lt_one 4 (norm_exp_neg_pi_exp_lt_one u)).mul_left
      (4 * π ^ 2 * Real.exp (9 * u / 2) + 6 * π * Real.exp (5 * u / 2))
  refine Summable.of_norm_bounded hs (fun n => ?_)
  simpa [Real.norm_eq_abs] using abs_phiTerm_le n u

/-- **Riemann's / Titchmarsh's kernel.**

`Φ(u) = ∑_{n ≥ 1} (4 π² n⁴ e^{9u/2} − 6 π n² e^{5u/2}) e^{−π n² e^{2u}}`

This is the kernel of Titchmarsh's integral representation
`Ξ(t) = 2 ∫_0^∞ Φ(u) cos(ut) du`, in the normalization of Spira (1971) and
Lagarias–Montague (2011).  Equivalently `Φ(u) = 4 e^{2u} M(e^{2u})`, where
`M(x) = π x^{1/4} ∑_{n≥1} n² (π n² x − 3/2) e^{−π n² x}` is the weight in Yang's
representation of the tempered xi function; the series above is that substitution with
`x = e^{2u}` carried out.

The normalizing property, which pins the constants down and which this definition was
checked against numerically to 25 decimal places at `w ∈ {1, 0.3, 0.7i, 0.2+1.1i}`, is
`ξ(½ + w) = 2 ∫_0^∞ Φ(u) cosh(wu) du` with `ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)`;
in particular `2 ∫_0^∞ Φ = ξ(½) = 0.4971207781883141099…`.  The companion odd channel
`2 ∫_0^∞ Φ(u) sinh(wu) du` is `XiLab.F`.

The sum is over the *positive* integers; the summand is written `phiTerm (n+1) u`.-/
noncomputable def Phi (u : ℝ) : ℝ := ∑' n : ℕ, phiTerm (n + 1) u

/--
@isnad1 id=summable.0h1v.s4.a3d1de756b92 from=translated src=- shape=7f8378ff vocab=c971c625
-/
lemma summable_phiTerm_succ (u : ℝ) : Summable (fun n : ℕ => phiTerm (n + 1) u) :=
  (summable_nat_add_iff 1).mpr (summable_phiTerm u)

/-- The `n = 0` summand vanishes identically, so summing over all of `ℕ` gives the same
value as summing over `n ≥ 1`.  This is the convenient form for estimates.
@isnad1 id=eq.0h1v.s4.7af0e3117d54 from=translated src=- shape=53cec0e6 vocab=f206c33b
-/
lemma Phi_eq_tsum (u : ℝ) : Phi u = ∑' n : ℕ, phiTerm n u := by
  rw [(summable_phiTerm u).tsum_eq_zero_add, phiTerm_zero, zero_add]
  rfl

/-! ### Continuity -/

/-- Uniform termwise bound on a compact interval `[a, b]`.
@isnad1 id=le.1h4v.s7.b2342a383efe from=translated src=- shape=e15a9ca2 vocab=138e31ec
-/
lemma abs_phiTerm_le_of_mem_Icc {a b : ℝ} (n : ℕ) {x : ℝ} (hx : x ∈ Icc a b) :
    |phiTerm n x| ≤
      (4 * π ^ 2 * Real.exp (9 * b / 2) + 6 * π * Real.exp (5 * b / 2)) *
        ((n : ℝ) ^ 4 * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by
  obtain ⟨hax, hxb⟩ := hx
  have hpi := Real.pi_pos
  refine (abs_phiTerm_le n x).trans ?_
  have h1 : Real.exp (9 * x / 2) ≤ Real.exp (9 * b / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h2 : Real.exp (5 * x / 2) ≤ Real.exp (5 * b / 2) :=
    Real.exp_le_exp.mpr (by linarith)
  have h3 : Real.exp (-(π * Real.exp (2 * x))) ≤ Real.exp (-(π * Real.exp (2 * a))) := by
    apply Real.exp_le_exp.mpr
    have : Real.exp (2 * a) ≤ Real.exp (2 * x) := Real.exp_le_exp.mpr (by linarith)
    nlinarith
  have h4 : Real.exp (-(π * Real.exp (2 * x))) ^ n ≤ Real.exp (-(π * Real.exp (2 * a))) ^ n :=
    pow_le_pow_left₀ (Real.exp_pos _).le h3 n
  have hn4 : (0:ℝ) ≤ (n : ℝ) ^ 4 := by positivity
  have hpow : (0:ℝ) ≤ Real.exp (-(π * Real.exp (2 * x))) ^ n := pow_nonneg (Real.exp_pos _).le n
  have hC : (0:ℝ) ≤ 4 * π ^ 2 * Real.exp (9 * x / 2) + 6 * π * Real.exp (5 * x / 2) := by
    positivity
  calc (4 * π ^ 2 * Real.exp (9 * x / 2) + 6 * π * Real.exp (5 * x / 2)) *
        ((n : ℝ) ^ 4 * Real.exp (-(π * Real.exp (2 * x))) ^ n)
      ≤ (4 * π ^ 2 * Real.exp (9 * x / 2) + 6 * π * Real.exp (5 * x / 2)) *
        ((n : ℝ) ^ 4 * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by
        exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h4 hn4) hC
    _ ≤ (4 * π ^ 2 * Real.exp (9 * b / 2) + 6 * π * Real.exp (5 * b / 2)) *
        ((n : ℝ) ^ 4 * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        nlinarith

/--
@isnad1 id=continuo.0h2v.s4.f14bc494c887 from=translated src=- shape=384c6439 vocab=fba3ebf4
-/
theorem continuousOn_Phi_Icc (a b : ℝ) : ContinuousOn Phi (Icc a b) := by
  have hr : ‖Real.exp (-(π * Real.exp (2 * a)))‖ < 1 := norm_exp_neg_pi_exp_lt_one a
  have hgeo : Summable
      (fun m : ℕ => (m : ℝ) ^ 4 * Real.exp (-(π * Real.exp (2 * a))) ^ m) :=
    summable_pow_mul_geometric_of_norm_lt_one 4 hr
  have hshift : Summable (fun n : ℕ =>
      ((n + 1 : ℕ) : ℝ) ^ 4 * Real.exp (-(π * Real.exp (2 * a))) ^ (n + 1)) :=
    (summable_nat_add_iff
      (f := fun m : ℕ => (m : ℝ) ^ 4 * Real.exp (-(π * Real.exp (2 * a))) ^ m) 1).mpr hgeo
  have hsum := hshift.mul_left
    (4 * π ^ 2 * Real.exp (9 * b / 2) + 6 * π * Real.exp (5 * b / 2))
  have main : ContinuousOn (fun x => ∑' n : ℕ, phiTerm (n + 1) x) (Icc a b) :=
    continuousOn_tsum (fun n => (continuous_phiTerm (n + 1)).continuousOn) hsum
      (fun n x hx => by
        simpa [Real.norm_eq_abs] using abs_phiTerm_le_of_mem_Icc (n + 1) hx)
  exact main

/-- `Φ` is continuous on all of `ℝ`.
@isnad1 id=continuo.0h0v.s3.3d8ca295975b from=translated src=- shape=e3d48bcb vocab=99c18247
-/
theorem continuous_Phi : Continuous Phi := by
  rw [continuous_iff_continuousAt]
  intro u₀
  exact (continuousOn_Phi_Icc (u₀ - 1) (u₀ + 1)).continuousAt
    (Icc_mem_nhds (by linarith) (by linarith))

/-! ### Positivity on `[0, ∞)` -/

/-- Every summand of `Φ` is strictly positive for `u ≥ 0` and `n ≥ 1`: the factor
`4π²n⁴e^{2u} − 6πn²` is positive because `4π² > 6π` and `n²e^{2u} ≥ 1`.
@isnad1 id=lt.2h2v.s5.52bef21e52e7 from=translated src=- shape=6d285e58 vocab=518b922c
-/
theorem phiTerm_pos {n : ℕ} (hn : 1 ≤ n) {u : ℝ} (hu : 0 ≤ u) : 0 < phiTerm n u := by
  have hpi3 : (3:ℝ) < π := Real.pi_gt_three
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : (1:ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hn4 : (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 4 := cast_sq_le_pow_four n
  have hx : (1:ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hsplit : Real.exp (9 * u / 2) = Real.exp (5 * u / 2) * Real.exp (2 * u) := by
    rw [← Real.exp_add]; ring_nf
  have h5 : (0:ℝ) < Real.exp (5 * u / 2) := Real.exp_pos _
  -- `4π² > 6π` (because `π > 3/2`), and `n⁴ e^{2u} ≥ n² ≥ 1`.
  have step1 : 6 * π * (n : ℝ) ^ 2 < 4 * π ^ 2 * (n : ℝ) ^ 2 := by
    nlinarith [mul_pos (mul_pos (by linarith : (0:ℝ) < 2 * π) (by linarith : (0:ℝ) < 2 * π - 3))
      (by linarith : (0:ℝ) < (n : ℝ) ^ 2)]
  have step2 : 4 * π ^ 2 * (n : ℝ) ^ 2 ≤ 4 * π ^ 2 * (n : ℝ) ^ 4 :=
    mul_le_mul_of_nonneg_left hn4 (by positivity)
  have step3 : 4 * π ^ 2 * (n : ℝ) ^ 4 ≤ 4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (2 * u) := by
    nlinarith [mul_le_mul_of_nonneg_left hx (by positivity : (0:ℝ) ≤ 4 * π ^ 2 * (n : ℝ) ^ 4)]
  have key : 6 * π * (n : ℝ) ^ 2 < 4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (2 * u) := by
    linarith
  rw [phiTerm, hsplit]
  refine mul_pos ?_ (Real.exp_pos _)
  have hfac : 4 * π ^ 2 * (n : ℝ) ^ 4 * (Real.exp (5 * u / 2) * Real.exp (2 * u)) -
      6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) =
      Real.exp (5 * u / 2) * (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (2 * u) -
        6 * π * (n : ℝ) ^ 2) := by ring
  rw [hfac]
  exact mul_pos h5 (by linarith)

/-- **Positivity of `Φ` on the half line.**
@isnad1 id=lt.1h1v.s4.fac8a6435291 from=translated src=- shape=a8dc2df9 vocab=acc932ab
-/
theorem Phi_pos {u : ℝ} (hu : 0 ≤ u) : 0 < Phi u := by
  have hterm : ∀ n : ℕ, 0 < phiTerm (n + 1) u := fun n =>
    phiTerm_pos (Nat.le_add_left 1 n) hu
  have := (summable_phiTerm_succ u).le_tsum 0 (fun j _ => (hterm j).le)
  exact lt_of_lt_of_le (hterm 0) this

/--
@isnad1 id=le.1h1v.s4.692b3e0f3e8a from=translated src=- shape=35bd48ee vocab=18273a3d
-/
theorem Phi_nonneg {u : ℝ} (hu : 0 ≤ u) : 0 ≤ Phi u := (Phi_pos hu).le

/-! ### The decay envelope on `[0, ∞)`

For `u ≥ 0`, `|Φ(u)| ≤ phiConst · e^{9u/2} · e^{−π e^{2u}}`.  This is the paper's envelope
`2Φ(u) ≤ C₁ e^{9u/2} e^{−π e^{2u}}` with a deliberately cruder constant: the paper drops
the negative term outright and gets `C₁ = 8π² ∑_{n≥1} n⁴ e^{−π(n²−1)} = 79.058784…`
(i.e. `39.5294…` as a bound on `Φ` itself), whereas we bound `|4π²n⁴e^{9u/2} −
6πn²e^{5u/2}|` by the *sum* of the two pieces, giving
`phiConst = ∑_{n≥1} (4π²n⁴ + 6πn²) e^{−π(n²−1)} = 58.3850…`.  The larger constant costs
nothing downstream — only the shape `e^{9u/2} e^{−π e^{2u}}` is used — and it removes the
need for any sign analysis of the summand.

The mechanism is `e^{−π n² e^{2u}} ≤ e^{−π e^{2u}} e^{−π(n²−1)}` for `u ≥ 0` and `n ≥ 1`,
which is exactly `(n²−1)(e^{2u}−1) ≥ 0`. -/

/-- The `n`-th term of the envelope constant.-/
noncomputable def envTerm (n : ℕ) : ℝ :=
  (4 * π ^ 2 * (n : ℝ) ^ 4 + 6 * π * (n : ℝ) ^ 2) * Real.exp (-(π * ((n : ℝ) ^ 2 - 1)))

/--
@isnad1 id=le.0h1v.s3.3ac355ee02dc from=translated src=- shape=b9369acb vocab=694c495d
-/
lemma envTerm_nonneg (n : ℕ) : 0 ≤ envTerm n := by
  have := Real.pi_pos; unfold envTerm; positivity

/--
@isnad1 id=summable.0h0v.s3.959e01107376 from=translated src=- shape=ef4b497d vocab=30d41dd8
-/
theorem summable_envTerm : Summable envTerm := by
  have hpi := Real.pi_pos
  have hr : ‖Real.exp (-π)‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]; linarith
  have hs := (summable_pow_mul_geometric_of_norm_lt_one 4 hr).mul_left
    (Real.exp π * (4 * π ^ 2 + 6 * π))
  refine Summable.of_norm_bounded hs (fun n => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (envTerm_nonneg n)]
  have hexp : Real.exp (-(π * ((n : ℝ) ^ 2 - 1))) ≤ Real.exp π * Real.exp (-π) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_le_mul_of_nonneg_left (cast_le_sq n) hpi.le]
  have hcoef : 4 * π ^ 2 * (n : ℝ) ^ 4 + 6 * π * (n : ℝ) ^ 2 ≤ (4 * π ^ 2 + 6 * π) * (n : ℝ) ^ 4 := by
    nlinarith [mul_le_mul_of_nonneg_left (cast_sq_le_pow_four n)
      (by positivity : (0:ℝ) ≤ 6 * π)]
  calc envTerm n
      ≤ ((4 * π ^ 2 + 6 * π) * (n : ℝ) ^ 4) * (Real.exp π * Real.exp (-π) ^ n) := by
        refine mul_le_mul hcoef hexp (Real.exp_pos _).le (by positivity)
    _ = Real.exp π * (4 * π ^ 2 + 6 * π) * ((n : ℝ) ^ 4 * Real.exp (-π) ^ n) := by ring

/-- The envelope constant `C = ∑_{n≥1} (4π²n⁴ + 6πn²) e^{−π(n²−1)} = 58.3850…` (finite);
the `n = 0` term of the sum vanishes, so summing over all of `ℕ` is the same thing.-/
noncomputable def phiConst : ℝ := ∑' n : ℕ, envTerm n

/--
@isnad1 id=le.0h0v.s3.0b3a61e8f0c3 from=translated src=- shape=ff3a10fc vocab=e6deb665
-/
theorem phiConst_nonneg : 0 ≤ phiConst :=
  tsum_nonneg envTerm_nonneg

/-- Termwise form of the envelope bound.
@isnad1 id=le.1h2v.s6.1df09d372ed1 from=translated src=- shape=ab660646 vocab=2fb1e34c
-/
lemma abs_phiTerm_le_envTerm (n : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    |phiTerm n u| ≤
      envTerm n * (Real.exp (9 * u / 2) * Real.exp (-(π * Real.exp (2 * u)))) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [envTerm]
  have hpi := Real.pi_pos
  have hn1 : (1:ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn2 : (1:ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hx : (1:ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hA : Real.exp (5 * u / 2) ≤ Real.exp (9 * u / 2) := Real.exp_le_exp.mpr (by linarith)
  have hB : Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) ≤
      Real.exp (-(π * ((n : ℝ) ^ 2 - 1))) * Real.exp (-(π * Real.exp (2 * u))) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [mul_nonneg hpi.le
      (mul_nonneg (sub_nonneg.mpr hn2) (sub_nonneg.mpr hx))]
  have hcoef : 4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) +
      6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) ≤
      (4 * π ^ 2 * (n : ℝ) ^ 4 + 6 * π * (n : ℝ) ^ 2) * Real.exp (9 * u / 2) := by
    nlinarith [mul_le_mul_of_nonneg_left hA (by positivity : (0:ℝ) ≤ 6 * π * (n : ℝ) ^ 2)]
  calc |phiTerm n u|
      ≤ (4 * π ^ 2 * (n : ℝ) ^ 4 * Real.exp (9 * u / 2) +
          6 * π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2)) *
            Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) := abs_phiTerm_le_aux n u
    _ ≤ ((4 * π ^ 2 * (n : ℝ) ^ 4 + 6 * π * (n : ℝ) ^ 2) * Real.exp (9 * u / 2)) *
          (Real.exp (-(π * ((n : ℝ) ^ 2 - 1))) * Real.exp (-(π * Real.exp (2 * u)))) :=
        mul_le_mul hcoef hB (Real.exp_pos _).le (by positivity)
    _ = envTerm n * (Real.exp (9 * u / 2) * Real.exp (-(π * Real.exp (2 * u)))) := by
        unfold envTerm; ring

/-- **Superexponential decay of `Φ`.**  For `u ≥ 0`,
`Φ(u) ≤ C · e^{9u/2} · e^{−π e^{2u}}` with `C = phiConst`.
@isnad1 id=le.1h1v.s6.9c9830ad2800 from=translated src=- shape=b601d6cd vocab=e36c51c4
-/
theorem abs_Phi_le {u : ℝ} (hu : 0 ≤ u) :
    |Phi u| ≤ phiConst * (Real.exp (9 * u / 2) * Real.exp (-(π * Real.exp (2 * u)))) := by
  have hsum : Summable (fun n : ℕ => phiTerm n u) := summable_phiTerm u
  have hA : Summable (fun n : ℕ => |phiTerm n u|) := hsum.abs
  have hbound : Summable (fun n : ℕ =>
      envTerm n * (Real.exp (9 * u / 2) * Real.exp (-(π * Real.exp (2 * u))))) :=
    summable_envTerm.mul_right _
  calc |Phi u| = |∑' n : ℕ, phiTerm n u| := by rw [Phi_eq_tsum]
    _ ≤ ∑' n : ℕ, |phiTerm n u| := by
        simpa [Real.norm_eq_abs] using
          norm_tsum_le_tsum_norm (f := fun n : ℕ => phiTerm n u)
            (by simpa [Real.norm_eq_abs] using hA)
    _ ≤ ∑' n : ℕ, envTerm n * (Real.exp (9 * u / 2) * Real.exp (-(π * Real.exp (2 * u)))) :=
        hA.tsum_le_tsum (fun n => abs_phiTerm_le_envTerm n hu) hbound
    _ = phiConst * (Real.exp (9 * u / 2) * Real.exp (-(π * Real.exp (2 * u)))) :=
        tsum_mul_right

/--
@isnad1 id=le.1h1v.s6.312a5b5323c2 from=translated src=- shape=c823d203 vocab=c488ed9b
-/
theorem Phi_le {u : ℝ} (hu : 0 ≤ u) :
    Phi u ≤ phiConst * (Real.exp (9 * u / 2) * Real.exp (-(π * Real.exp (2 * u)))) :=
  (le_abs_self _).trans (abs_Phi_le hu)

/-! ### Integrability of `Φ(u) · (anything of exponential type)` on `(0, ∞)` -/

/--
@isnad1 id=le.1h1v.s6.b8892dbaeb32 from=translated src=- shape=d9816f30 vocab=fc917557
-/
lemma two_sq_le_exp_two_mul {u : ℝ} (hu : 0 ≤ u) : 2 * u ^ 2 ≤ Real.exp (2 * u) := by
  have h : (1:ℝ) + 2 * u + (2 * u) ^ 2 / 2 ≤ Real.exp (2 * u) := by
    have := Real.sum_le_exp_of_nonneg (show (0:ℝ) ≤ 2 * u by linarith) 3
    simpa [Finset.sum_range_succ, Nat.factorial] using this
  nlinarith

/-- **The envelope beats every exponential.**  For `u ≥ 0` and any real `a`,
`e^{a u} e^{−π e^{2u}} ≤ e^{(a+1)²/(8π)} · e^{−u}`.

The mechanism: `π e^{2u} ≥ 2π u²`, and then `(a+1)u − 2πu² ≤ (a+1)²/(8π)` by completing
the square (`2π(u − (a+1)/(4π))² ≥ 0`).
@isnad1 id=le.1h2v.s7.c3f450d887cb from=translated src=- shape=21b4f62a vocab=03fd11bb
-/
theorem exp_envelope_le (a : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    Real.exp (a * u) * Real.exp (-(π * Real.exp (2 * u))) ≤
      Real.exp ((a + 1) ^ 2 / (8 * π)) * Real.exp (-u) := by
  have hpi := Real.pi_pos
  rw [← Real.exp_add, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have h1 : 2 * π * u ^ 2 ≤ π * Real.exp (2 * u) := by
    nlinarith [two_sq_le_exp_two_mul hu]
  have hq : (0:ℝ) ≤ 2 * π * (u - (a + 1) / (4 * π)) ^ 2 := by positivity
  have he : 2 * π * (u - (a + 1) / (4 * π)) ^ 2 =
      2 * π * u ^ 2 - (a + 1) * u + (a + 1) ^ 2 / (8 * π) := by
    field_simp; ring
  rw [he] at hq
  linarith

/-- The scalar envelope `e^{a u} e^{−π e^{2u}}` is integrable on `(0, ∞)` for **every**
real exponent `a`: this is the superexponential decay doing its job.
@isnad1 id=integrab.0h1v.s6.c27bcc16d1d5 from=translated src=- shape=e76bdb11 vocab=f0963662
-/
theorem integrableOn_exp_envelope (a : ℝ) :
    IntegrableOn
      (fun u : ℝ => Real.exp (a * u) * Real.exp (-(π * Real.exp (2 * u)))) (Ioi (0:ℝ)) := by
  have hint : IntegrableOn
      (fun u : ℝ => Real.exp ((a + 1) ^ 2 / (8 * π)) * Real.exp (-1 * u)) (Ioi (0:ℝ)) :=
    (exp_neg_integrableOn_Ioi 0 one_pos).const_mul _
  refine Integrable.mono' hint (Continuous.aestronglyMeasurable (by fun_prop)) ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu
  rw [Real.norm_eq_abs, abs_of_pos (by positivity)]
  simpa [neg_one_mul] using exp_envelope_le a (le_of_lt hu)

/-- Comparison criterion: anything dominated on `(0, ∞)` by `C e^{a u} e^{−π e^{2u}}` is
integrable there.
@isnad1 id=integrab.2h4v.s7.f01165829623 from=translated src=- shape=48f1a9e0 vocab=8b29ca83
-/
theorem integrableOn_of_le_envelope {E : Type*} [NormedAddCommGroup E]
    (f : ℝ → E) (a C : ℝ)
    (hf : AEStronglyMeasurable f (volume.restrict (Ioi (0:ℝ))))
    (hb : ∀ u : ℝ, 0 < u →
      ‖f u‖ ≤ C * (Real.exp (a * u) * Real.exp (-(π * Real.exp (2 * u))))) :
    IntegrableOn f (Ioi (0:ℝ)) := by
  refine Integrable.mono' ((integrableOn_exp_envelope a).const_mul C) hf ?_
  filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu using hb u hu

/-- **The decay envelope in explicit `e^{−u}` form.**  For `u ≥ 0` and every real `a`,
`|Φ(u)| e^{a u} ≤ (C · e^{(11/2+a)²/(8π)}) · e^{−u}`.  Combining the superexponential
envelope with `exp_envelope_le`.
@isnad1 id=le.1h2v.s7.138023688dab from=translated src=- shape=a0b95982 vocab=0d164f7d
-/
theorem abs_Phi_mul_exp_le (a : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    |Phi u| * Real.exp (a * u) ≤
      phiConst * Real.exp ((9 / 2 + a + 1) ^ 2 / (8 * π)) * Real.exp (-u) := by
  have h1 : |Phi u| * Real.exp (a * u) ≤
      phiConst * (Real.exp ((9 / 2 + a) * u) * Real.exp (-(π * Real.exp (2 * u)))) := by
    calc |Phi u| * Real.exp (a * u)
        ≤ (phiConst * (Real.exp (9 * u / 2) * Real.exp (-(π * Real.exp (2 * u))))) *
            Real.exp (a * u) :=
          mul_le_mul_of_nonneg_right (abs_Phi_le hu) (Real.exp_pos _).le
      _ = phiConst * (Real.exp ((9 / 2 + a) * u) * Real.exp (-(π * Real.exp (2 * u)))) := by
          rw [show (9 / 2 + a) * u = 9 * u / 2 + a * u by ring, Real.exp_add]; ring
  refine h1.trans ?_
  calc phiConst * (Real.exp ((9 / 2 + a) * u) * Real.exp (-(π * Real.exp (2 * u))))
      ≤ phiConst * (Real.exp ((9 / 2 + a + 1) ^ 2 / (8 * π)) * Real.exp (-u)) :=
        mul_le_mul_of_nonneg_left (exp_envelope_le (9 / 2 + a) hu) phiConst_nonneg
    _ = phiConst * Real.exp ((9 / 2 + a + 1) ^ 2 / (8 * π)) * Real.exp (-u) := by ring

/-- **`Φ(u) e^{au} → 0` as `u → ∞`, for every real `a`** — the superexponential decay
outruns every exponential.
@isnad1 id=tendsto.0h1v.s5.afa51ab25db5 from=translated src=- shape=dfa5335b vocab=91b0c8db
-/
theorem tendsto_Phi_mul_exp_atTop (a : ℝ) :
    Tendsto (fun u : ℝ => Phi u * Real.exp (a * u)) atTop (𝓝 0) := by
  have hupper : Tendsto
      (fun u : ℝ => phiConst * Real.exp ((9 / 2 + a + 1) ^ 2 / (8 * π)) * Real.exp (-u))
      atTop (𝓝 0) := by
    simpa using Real.tendsto_exp_neg_atTop_nhds_zero.const_mul
      (phiConst * Real.exp ((9 / 2 + a + 1) ^ 2 / (8 * π)))
  refine squeeze_zero' (Filter.eventually_atTop.2 ⟨0, fun u hu => ?_⟩)
    (Filter.eventually_atTop.2 ⟨0, fun u hu => ?_⟩) hupper
  · exact mul_nonneg (Phi_nonneg hu) (Real.exp_pos _).le
  · exact le_trans (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le)
      (abs_Phi_mul_exp_le a hu)

/-- In particular `Φ(u) → 0` as `u → ∞`.
@isnad1 id=tendsto.0h0v.s4.adba9a9df2d0 from=translated src=- shape=95bb6042 vocab=2c906f69
-/
theorem tendsto_Phi_atTop : Tendsto Phi atTop (𝓝 0) := by
  simpa using tendsto_Phi_mul_exp_atTop 0

/-! ### The odd channel `F(w) = 2 ∫₀^∞ Φ(u) sinh(wu) du` -/

/--
@isnad1 id=le.0h1v.s3.c8222a081966 from=translated src=- shape=a5850310 vocab=16332d8d
-/
lemma norm_complex_sinh_le (z : ℂ) : ‖Complex.sinh z‖ ≤ Real.exp ‖z‖ := by
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have e1 : Real.exp z.re ≤ Real.exp ‖z‖ := Real.exp_le_exp.mpr ((le_abs_self _).trans hre)
  have e2 : Real.exp (-z.re) ≤ Real.exp ‖z‖ := Real.exp_le_exp.mpr ((neg_le_abs _).trans hre)
  have h1 : ‖Complex.exp z‖ = Real.exp z.re := Complex.norm_exp z
  have h2 : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by rw [Complex.norm_exp]; simp
  have hdef : Complex.sinh z = (Complex.exp z - Complex.exp (-z)) / 2 := rfl
  have htri := norm_sub_le (Complex.exp z) (Complex.exp (-z))
  rw [h1, h2] at htri
  rw [hdef, norm_div, show ‖(2:ℂ)‖ = 2 by norm_num]
  linarith

/--
@isnad1 id=le.0h1v.s3.df4e5ef9fb2f from=translated src=- shape=a5850310 vocab=44af43b6
-/
lemma norm_complex_cosh_le (z : ℂ) : ‖Complex.cosh z‖ ≤ Real.exp ‖z‖ := by
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have e1 : Real.exp z.re ≤ Real.exp ‖z‖ := Real.exp_le_exp.mpr ((le_abs_self _).trans hre)
  have e2 : Real.exp (-z.re) ≤ Real.exp ‖z‖ := Real.exp_le_exp.mpr ((neg_le_abs _).trans hre)
  have h1 : ‖Complex.exp z‖ = Real.exp z.re := Complex.norm_exp z
  have h2 : ‖Complex.exp (-z)‖ = Real.exp (-z.re) := by rw [Complex.norm_exp]; simp
  have hdef : Complex.cosh z = (Complex.exp z + Complex.exp (-z)) / 2 := rfl
  have htri := norm_add_le (Complex.exp z) (Complex.exp (-z))
  rw [h1, h2] at htri
  rw [hdef, norm_div, show ‖(2:ℂ)‖ = 2 by norm_num]
  linarith

/--
@isnad1 id=eq.1h2v.s5.db1e13f5a1ae from=translated src=- shape=6e57ac6c vocab=3b209a6d
-/
lemma norm_mul_ofReal (w : ℂ) {u : ℝ} (hu : 0 ≤ u) : ‖w * (u : ℂ)‖ = ‖w‖ * u := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu]

/-- If `‖v‖ ≤ e^{r u}` then `Φ(u) v` obeys the integrable envelope with exponent `9/2 + r`.
@isnad1 id=le.2h3v.s7.c074b15edfe5 from=translated src=- shape=afb2f345 vocab=1a3671d8
-/
lemma norm_Phi_mul_le {u : ℝ} (hu : 0 < u) (r : ℝ) (v : ℂ) (hv : ‖v‖ ≤ Real.exp (r * u)) :
    ‖(Phi u : ℂ) * v‖ ≤
      phiConst * (Real.exp ((9 / 2 + r) * u) * Real.exp (-(π * Real.exp (2 * u)))) := by
  have hu0 : (0:ℝ) ≤ u := hu.le
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  calc |Phi u| * ‖v‖
      ≤ (phiConst * (Real.exp (9 * u / 2) * Real.exp (-(π * Real.exp (2 * u))))) *
          Real.exp (r * u) :=
        mul_le_mul (abs_Phi_le hu0) hv (norm_nonneg _)
          (mul_nonneg phiConst_nonneg (by positivity))
    _ = phiConst * (Real.exp ((9 / 2 + r) * u) * Real.exp (-(π * Real.exp (2 * u)))) := by
        rw [show (9 / 2 + r) * u = 9 * u / 2 + r * u by ring, Real.exp_add]; ring

/--
@isnad1 id=continuo.0h1v.s5.502d29ac1b35 from=translated src=- shape=c0804c4d vocab=a26dea61
-/
lemma continuous_Phi_mul_sinh (w : ℂ) :
    Continuous (fun u : ℝ => (Phi u : ℂ) * Complex.sinh (w * u)) := by
  have h1 : Continuous (fun u : ℝ => ((Phi u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_Phi
  have h2 : Continuous (fun u : ℝ => Complex.sinh (w * (u : ℂ))) :=
    Complex.differentiable_sinh.continuous.comp
      (continuous_const.mul Complex.continuous_ofReal)
  exact h1.mul h2

/--
@isnad1 id=continuo.0h1v.s5.6ce36db22b0f from=translated src=- shape=ab3e6c76 vocab=f6b0f3ab
-/
lemma continuous_Phi_mul_cosh_mul (w : ℂ) :
    Continuous (fun u : ℝ => (Phi u : ℂ) * (Complex.cosh (w * u) * (u : ℂ))) := by
  have h1 : Continuous (fun u : ℝ => ((Phi u : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp continuous_Phi
  have h2 : Continuous (fun u : ℝ => Complex.cosh (w * (u : ℂ))) :=
    Complex.differentiable_cosh.continuous.comp
      (continuous_const.mul Complex.continuous_ofReal)
  exact h1.mul (h2.mul Complex.continuous_ofReal)

/-- **Integrability of the odd-channel integrand**, for every complex `w`.  This is what
makes `F(w) = 2∫₀^∞ Φ(u) sinh(wu) du` converge.
@isnad1 id=integrab.0h1v.s6.4309071c3591 from=translated src=- shape=ee480d7b vocab=deb3f44f
-/
theorem integrableOn_Phi_mul_sinh (w : ℂ) :
    IntegrableOn (fun u : ℝ => (Phi u : ℂ) * Complex.sinh (w * u)) (Ioi (0:ℝ)) := by
  refine integrableOn_of_le_envelope _ (9 / 2 + ‖w‖) phiConst
    ((continuous_Phi_mul_sinh w).aestronglyMeasurable) (fun u hu => ?_)
  refine norm_Phi_mul_le hu ‖w‖ _ ?_
  refine (norm_complex_sinh_le _).trans (Real.exp_le_exp.mpr ?_)
  rw [norm_mul_ofReal w hu.le]

/-- The real-variable version: `u ↦ Φ(u) sinh(a u)` is integrable on `(0, ∞)` for real `a`
(the special case `w = a` of `integrableOn_Phi_mul_sinh`, recorded for convenience).
@isnad1 id=integrab.0h1v.s5.018295a58c60 from=translated src=- shape=cf72b6df vocab=8ab72ea6
-/
theorem integrableOn_Phi_mul_rsinh (a : ℝ) :
    IntegrableOn (fun u : ℝ => Phi u * Real.sinh (a * u)) (Ioi (0:ℝ)) := by
  have hcont : Continuous (fun u : ℝ => Phi u * Real.sinh (a * u)) := by
    exact continuous_Phi.mul (Real.continuous_sinh.comp (continuous_const.mul continuous_id))
  refine integrableOn_of_le_envelope _ (9 / 2 + |a|) phiConst hcont.aestronglyMeasurable
    (fun u hu => ?_)
  have hu0 : (0:ℝ) ≤ u := hu.le
  have hsinh : |Real.sinh (a * u)| ≤ Real.exp (|a| * u) := by
    have h := norm_complex_sinh_le ((a * u : ℝ) : ℂ)
    rw [← Complex.ofReal_sinh, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
      Real.norm_eq_abs, abs_mul] at h
    exact h.trans (Real.exp_le_exp.mpr (by rw [abs_of_nonneg hu0]))
  have := norm_Phi_mul_le hu |a| ((Real.sinh (a * u) : ℝ) : ℂ)
    (by rw [Complex.norm_real, Real.norm_eq_abs]; exact hsinh)
  rwa [← Complex.ofReal_mul, Complex.norm_real, Real.norm_eq_abs] at this

/-- **`F(w) = 2 ∫₀^∞ Φ(u) sinh(wu) du`**, the odd channel of Titchmarsh's kernel.

In the paper's notation this is `F(w) = ξ̂(½ + w)`, Yang's tempered xi function
recentred at the critical point; the integral converges for every `w ∈ ℂ` by
`integrableOn_Phi_mul_sinh`.-/
noncomputable def F (w : ℂ) : ℂ :=
  2 * ∫ u in Ioi (0:ℝ), (Phi u : ℂ) * Complex.sinh (w * u)

/-- The parametric integral defining `F` is complex-differentiable at every point.
@isnad1 id=differen.0h1v.s6.60d6e946e15f from=translated src=- shape=bdf93391 vocab=7ee45d18
-/
theorem differentiableAt_integral_Phi_sinh (w₀ : ℂ) :
    DifferentiableAt ℂ
      (fun w : ℂ => ∫ u in Ioi (0:ℝ), (Phi u : ℂ) * Complex.sinh (w * u)) w₀ := by
  set μ : Measure ℝ := volume.restrict (Ioi (0:ℝ)) with hμ
  set R : ℝ := ‖w₀‖ + 1 with hRdef
  set bnd : ℝ → ℝ := fun u =>
    phiConst * (Real.exp ((9 / 2 + (R + 1)) * u) * Real.exp (-(π * Real.exp (2 * u)))) with hbnd
  have hbnd_int : Integrable bnd μ := (integrableOn_exp_envelope _).const_mul _
  have h_diff : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball w₀ 1,
      HasDerivAt (fun z : ℂ => (Phi u : ℂ) * Complex.sinh (z * u))
        ((Phi u : ℂ) * (Complex.cosh (w * u) * (u : ℂ))) w := by
    filter_upwards with u w _
    exact (((hasDerivAt_mul_const (u : ℂ)).csinh).const_mul ((Phi u : ℝ) : ℂ))
  have h_bound : ∀ᵐ u ∂μ, ∀ w ∈ Metric.ball w₀ 1,
      ‖(Phi u : ℂ) * (Complex.cosh (w * u) * (u : ℂ))‖ ≤ bnd u := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with u hu w hw
    have hu0 : (0:ℝ) ≤ u := (mem_Ioi.mp hu).le
    have hwR : ‖w‖ ≤ R := by
      have hd : ‖w - w₀‖ < 1 := by
        rw [← dist_eq_norm]; exact Metric.mem_ball.mp hw
      have := norm_sub_norm_le w w₀
      rw [hRdef]; linarith
    refine norm_Phi_mul_le (mem_Ioi.mp hu) (R + 1) _ ?_
    have hc : ‖Complex.cosh (w * (u : ℂ))‖ ≤ Real.exp (R * u) := by
      refine (norm_complex_cosh_le _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul_ofReal w hu0]
      exact mul_le_mul_of_nonneg_right hwR hu0
    have hue : u ≤ Real.exp u := by linarith [Real.add_one_le_exp u]
    calc ‖Complex.cosh (w * (u : ℂ)) * (u : ℂ)‖
        = ‖Complex.cosh (w * (u : ℂ))‖ * u := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hu0]
      _ ≤ Real.exp (R * u) * Real.exp u :=
          mul_le_mul hc hue hu0 (Real.exp_pos _).le
      _ = Real.exp ((R + 1) * u) := by rw [← Real.exp_add]; ring_nf
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (bound := bnd)
    (F := fun (z : ℂ) (u : ℝ) => (Phi u : ℂ) * Complex.sinh (z * u))
    (F' := fun (z : ℂ) (u : ℝ) => (Phi u : ℂ) * (Complex.cosh (z * u) * (u : ℂ)))
    (x₀ := w₀) (s := Metric.ball w₀ 1)
    (Metric.ball_mem_nhds w₀ one_pos)
    (Filter.Eventually.of_forall
      (fun z => (continuous_Phi_mul_sinh z).aestronglyMeasurable))
    (integrableOn_Phi_mul_sinh w₀)
    ((continuous_Phi_mul_cosh_mul w₀).aestronglyMeasurable)
    h_bound hbnd_int h_diff
  exact key.2.differentiableAt

/-- **`F` is entire.**
@isnad1 id=differen.0h0v.s6.bbe11de42f6e from=translated src=- shape=aa9fb30a vocab=19048c1c
-/
theorem differentiable_F : Differentiable ℂ F := by
  intro w
  exact ((differentiableAt_integral_Phi_sinh w).const_mul 2)

end XiLab

/-! ### Axiom audit

Every main result of this file depends only on `propext`, `Classical.choice`,
`Quot.sound`.  There is no `sorry`, no `native_decide`, and no custom `axiom` anywhere in
the file; in particular no FRONTIER lemma was needed (Wintner's monotonicity theorem is
*not* used — positivity of `Φ` on `[0,∞)` is proved directly, since every summand is
already positive there). -/
section AxiomAudit
end AxiomAudit
