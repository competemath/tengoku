import Tengoku
import Tengoku.Xilab.XiLab.Kernel
import Tengoku.Xilab.XiLab.Wintner

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms XiLab.hasDerivAt_T` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.theta_FE` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Phi_eq_T` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.theta_FE_I` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.theta_FE_II` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Phi_eq_thQR` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Phi_even` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.deriv_Phi_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.hasDerivAt_phiTerm'` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.abs_phiTerm''_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.hasDerivAt_PhiD` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.PhiDD_split` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.phiTerm''_one_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.phiTerm''_two_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.tail_tsum_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.PhiDD_neg` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.PhiD_neg_of_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms XiLab.Phi_strictAntiOn_Ici_zero` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# XiLab.Evenness — `Φ` is even, and Wintner's theorem down to the origin

Consumes `XiLab/Kernel.lean` (`phiTerm`, `Phi`,
`cast_le_sq`, `norm_exp_neg_pi_exp_lt_one`, `continuous_Phi`) and `XiLab/Wintner.lean`
(`phiTerm'`, `hasDerivAt_Phi`, `deriv_Phi`, `deriv_Phi_neg`, `summable_phiTerm'_succ`,
`le_pi_mul_exp_inv_four_hundred`).  There is no `sorry`, no `native_decide` and no custom
`axiom` in this file, and no FRONTIER lemma was needed.

## Main results

* `XiLab.Phi_even` — **`Φ(−u) = Φ(u)`**, from the Jacobi theta functional equation
  differentiated twice in `u`.
* `XiLab.deriv_Phi_zero` — `Φ'(0) = 0` exactly.
* `XiLab.hasDerivAt_PhiD` — `Φ'` may itself be differentiated term by term.
* `XiLab.PhiDD_neg` — `Φ'' < 0` on `[0, 1/400]`, with explicit constants.
* `XiLab.Phi_strictAntiOn_Ici_zero` — **Wintner's theorem on `Ici 0`**, closing the last gap
  in the library.

## The reduction

Put `T k u = ∑_{n≥1} (πn²)^k e^{−πn²e^{2u}}`.  Then `T k' = −2e^{2u} T (k+1)` — differentiating
in `u` just moves `k` up by one — and the kernel is the two-term combination

  `Φ(u) = 4 e^{9u/2} T₂(u) − 6 e^{5u/2} T₁(u)`      (`Phi_eq_T`),

which is a pure `tsum` rearrangement of `Kernel.phiTerm`, no analysis.  Packaging
`thP = 1 + 2T₀ = θ(e^{2u})`, `thQ = thP'`, `thR = thQ'` gives `Φ = ½ e^{u/2}(thQ + thR)`
(`Phi_eq_thQR`), and Jacobi's equation is `thP(−u) = e^u thP(u)` (`theta_FE_P`).
Differentiating that twice (`theta_FE_I`, `theta_FE_II`) and eliminating gives
`thQ(−u) + thR(−u) = e^u (thQ(u) + thR(u))`, i.e. `Φ(−u) = Φ(u)`.

Keeping the exponentials packaged inside `thQ`/`thR` is what makes the final step a single
`linear_combination`: the only exponential identity needed is `e^{−u/2} e^{u} = e^{u/2}`.

## Route taken to the functional equation, and why

**Route B (direct Poisson summation), not route A (`jacobiTheta`).**  Mathlib's Gaussian
Poisson summation is already instantiated in exactly the shape needed:
`Real.tsum_exp_neg_mul_int_sq` (`Mathlib/Analysis/SpecialFunctions/Gaussian/PoissonSummation.lean:123`)
states `∑_{n∈ℤ} e^{−πan²} = a^{−1/2} ∑_{n∈ℤ} e^{−(π/a)n²}` for real `a > 0`.  With `a = e^{2u}`
that *is* `thP(−u) = e^u thP(u)` after one `tsum_of_add_one_of_neg_add_one` (ℤ-sum to
`1 + 2·(ℕ-sum)`, using that the summand is even in `n`) and `Real.rpow_def_of_pos` for
`(e^{2u})^{1/2} = e^u`.  Total cost: `tsum_int_thTerm` + `rpow_half_exp` + `theta_FE`, about
30 lines.

Route A would have gone through `jacobiTheta`/`jacobiTheta_S_smul`, which live in `ℂ` on
`0 < im τ`; every statement would have to be transported back along `τ = i e^{2u}` and then
re-realified, and `hasSum_nat_jacobiTheta` would still only replace the ℤ→ℕ step that
`tsum_of_add_one_of_neg_add_one` does in three lines.  As `Kernel.lean` already records,
Mathlib has no second-`τ`-derivative theta series either way — but that turns out not to
matter, because the derivatives are taken *after* transporting to the real variable `u`,
where `T k' = −2e^{2u} T (k+1)` is elementary.

## Why `[0, 1/400]` needs the second derivative

`Φ` is even, so `Φ'(0) = 0` exactly and no finite truncation of `Φ'` is `≤ 0` at the origin
(see the closing note of `Wintner.lean`).  But `Φ''` has no such cancellation: at `u = 0` the
`n = 1` block is `−17.44`, the `n = 2` block is `+0.71`, and `n ≥ 3` contributes `< 4·10⁻⁶`.
The estimate here is deliberately lossy — `n = 1` bounded by `−5.7`, `n = 2` by `+2.9`, the
tail by `1.2` — which still leaves `Φ'' ≤ −1.6` and keeps every numeric step inside
`nlinarith`'s reach.  With `Φ'(0) = 0` and `Φ'' < 0`, `strictAntiOn_of_deriv_neg` applied to
`Φ'` on `Icc 0 (1/400)` gives `Φ' < 0` on `(0, 1/400]`; splicing in Wintner's
`deriv_Phi_neg` past `1/400` gives `Φ' < 0` on all of `Ioi 0`, and one more
`strictAntiOn_of_deriv_neg` — on `Ici 0` directly, never gluing two `StrictAntiOn`s — finishes.

All numeric constants come from `Real.pi_gt_d6`, `Real.pi_lt_d20`, `Real.exp_one_gt_d9`,
`Real.exp_one_lt_d9` and `Real.add_one_le_exp`.  Nothing is `norm_num`-on-`Real.exp`, and the
polynomial-versus-exponential step is just `X/8 ≤ e^{X/8}` raised to the fourth power.
-/

open scoped Real
open MeasureTheory Set Filter Topology

namespace XiLab

/-! ### The theta family `T k u = ∑_{n ≥ 1} (π n²)^k e^{−π n² e^{2u}}` -/

/-- `(π n²)^k e^{−π n² e^{2u}}`.  For `k = 0, 1, 2` these are the three series out of which
`Φ` and the Jacobi functional equation are assembled.-/
noncomputable def thTerm (k n : ℕ) (u : ℝ) : ℝ :=
  (π * (n : ℝ) ^ 2) ^ k * Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))

/-- `T k u = ∑_{n ≥ 1} (π n²)^k e^{−π n² e^{2u}}`.-/
noncomputable def T (k : ℕ) (u : ℝ) : ℝ := ∑' n : ℕ, thTerm k (n + 1) u

/--
@isnad1 id=le.0h3v.s4.e6e12a370568 from=translated src=- shape=242e3cc5 vocab=51887fba
-/
lemma thTerm_nonneg (k n : ℕ) (u : ℝ) : 0 ≤ thTerm k n u := by
  unfold thTerm
  have : (0:ℝ) ≤ π * (n : ℝ) ^ 2 := by positivity
  positivity

/-- Differentiating in `u` moves `k` up by one.
@isnad1 id=hasderiv.0h3v.s6.73be194a4d47 from=translated src=- shape=d9c3d374 vocab=d55c05c6
-/
lemma hasDerivAt_thTerm (k n : ℕ) (u : ℝ) :
    HasDerivAt (thTerm k n) (-2 * Real.exp (2 * u) * thTerm (k + 1) n u) u := by
  have h2 : HasDerivAt (fun v : ℝ => 2 * v) (2 : ℝ) u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have e2 : HasDerivAt (fun v : ℝ => Real.exp (2 * v)) (Real.exp (2 * u) * 2) u := h2.exp
  have hb : HasDerivAt (fun v : ℝ => Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * v))))
      (Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
        (-(π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2)))) u :=
    ((e2.const_mul (π * (n : ℝ) ^ 2)).neg).exp
  have hmul := hb.const_mul ((π * (n : ℝ) ^ 2) ^ k)
  have hfun : thTerm k n = fun v : ℝ =>
      (π * (n : ℝ) ^ 2) ^ k * Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * v))) := rfl
  have heq : -2 * Real.exp (2 * u) * thTerm (k + 1) n u
      = (π * (n : ℝ) ^ 2) ^ k * (Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
        (-(π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2)))) := by
    simp only [thTerm]; ring
  rw [hfun, heq]
  exact hmul

/-! ### A locally uniform majorant -/

/-- `π^k n^{2k} r(a)^n` with `r(a) = e^{−π e^{2a}} < 1`.-/
noncomputable def thBound (k : ℕ) (a : ℝ) (n : ℕ) : ℝ :=
  π ^ k * ((n : ℝ) ^ (2 * k) * Real.exp (-(π * Real.exp (2 * a))) ^ n)

/--
@isnad1 id=summable.0h2v.s4.512158a837ef from=translated src=- shape=27343aff vocab=a30b6487
-/
theorem summable_thBound (k : ℕ) (a : ℝ) : Summable (thBound k a) :=
  (summable_pow_mul_geometric_of_norm_lt_one (2 * k)
    (norm_exp_neg_pi_exp_lt_one a)).mul_left _

/--
@isnad1 id=le.1h4v.s4.fb601babd220 from=translated src=- shape=a3c357cb vocab=667c8602
-/
lemma abs_thTerm_le (k n : ℕ) {a u : ℝ} (hau : a ≤ u) :
    |thTerm k n u| ≤ thBound k a n := by
  have hpi := Real.pi_pos
  have hE : Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) ≤
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
  rw [abs_of_nonneg (thTerm_nonneg k n u), thTerm, thBound]
  have hpow : (π * (n : ℝ) ^ 2) ^ k = π ^ k * (n : ℝ) ^ (2 * k) := by
    rw [mul_pow, ← pow_mul]
  rw [hpow]
  calc π ^ k * (n : ℝ) ^ (2 * k) * Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))
      ≤ π ^ k * (n : ℝ) ^ (2 * k) * Real.exp (-(π * Real.exp (2 * a))) ^ n :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = π ^ k * ((n : ℝ) ^ (2 * k) * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by ring

/--
@isnad1 id=le.2h5v.s7.f2a410c1e64a from=translated src=- shape=c3ae0a9b vocab=c6dd24dd
-/
lemma abs_thTermDeriv_le (k n : ℕ) {a b u : ℝ} (hau : a ≤ u) (hub : u ≤ b) :
    |(-2 : ℝ) * Real.exp (2 * u) * thTerm (k + 1) n u| ≤
      2 * Real.exp (2 * b) * thBound (k + 1) a n := by
  have h1 : |thTerm (k + 1) n u| ≤ thBound (k + 1) a n := abs_thTerm_le _ _ hau
  have h2 : Real.exp (2 * u) ≤ Real.exp (2 * b) := Real.exp_le_exp.mpr (by linarith)
  have heq : |(-2 : ℝ) * Real.exp (2 * u) * thTerm (k + 1) n u| =
      2 * Real.exp (2 * u) * |thTerm (k + 1) n u| := by
    rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
    norm_num
  rw [heq]
  refine mul_le_mul (by linarith) h1 (abs_nonneg _) (by positivity)

/--
@isnad1 id=summable.0h2v.s4.1640e0bbf17e from=translated src=- shape=d666ff15 vocab=c8595f10
-/
theorem summable_thTerm (k : ℕ) (u : ℝ) : Summable (fun n : ℕ => thTerm k n u) := by
  refine Summable.of_norm_bounded (summable_thBound k u) (fun n => ?_)
  simpa [Real.norm_eq_abs] using abs_thTerm_le k n (le_refl u)

/--
@isnad1 id=summable.0h2v.s5.026f7a375ff9 from=translated src=- shape=71282564 vocab=79001caf
-/
theorem summable_thTerm_succ (k : ℕ) (u : ℝ) : Summable (fun n : ℕ => thTerm k (n + 1) u) :=
  (summable_nat_add_iff 1).mpr (summable_thTerm k u)

/-! ### Termwise differentiation of `T k` -/

/--
@isnad1 id=hasderiv.0h2v.s6.63c0d9c88188 from=translated src=- shape=321480a6 vocab=2bf14a81
-/
theorem hasDerivAt_T (k : ℕ) (x : ℝ) :
    HasDerivAt (T k) (-2 * Real.exp (2 * x) * T (k + 1) x) x := by
  have hmem : x ∈ Ioo (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
  have hsum : Summable
      (fun n : ℕ => 2 * Real.exp (2 * (x + 1)) * thBound (k + 1) (x - 1) (n + 1)) :=
    (((summable_nat_add_iff 1).mpr (summable_thBound (k + 1) (x - 1)))).mul_left _
  have key := hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => 2 * Real.exp (2 * (x + 1)) * thBound (k + 1) (x - 1) (n + 1))
    (g := fun n : ℕ => thTerm k (n + 1))
    (g' := fun (n : ℕ) (v : ℝ) => -2 * Real.exp (2 * v) * thTerm (k + 1) (n + 1) v)
    hsum isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hasDerivAt_thTerm k (n + 1) y)
    (fun n y hy => by
      rw [Real.norm_eq_abs]
      exact abs_thTermDeriv_le k (n + 1) hy.1.le hy.2.le)
    hmem (summable_thTerm_succ k x) hmem
  have hrw : (-2 * Real.exp (2 * x) * T (k + 1) x)
      = ∑' n : ℕ, (-2 * Real.exp (2 * x) * thTerm (k + 1) (n + 1) x) := by
    rw [T, tsum_mul_left]
  rw [hrw]
  exact key

/--
@isnad1 id=differen.0h1v.s5.7e6595837ebc from=translated src=- shape=e86db131 vocab=0b5fe795
-/
theorem differentiable_T (k : ℕ) : Differentiable ℝ (T k) :=
  fun x => (hasDerivAt_T k x).differentiableAt

/-! ### The Jacobi functional equation, in `T 0` form -/

/--
@isnad1 id=eq.0h1v.s6.c8a3c3185e2d from=translated src=- shape=b4f46c6b vocab=eee7ef37
-/
lemma tsum_int_thTerm (u : ℝ) :
    (∑' m : ℤ, Real.exp (-(π * (m : ℝ) ^ 2 * Real.exp (2 * u)))) = 1 + 2 * T 0 u := by
  set g : ℤ → ℝ := fun m => Real.exp (-(π * (m : ℝ) ^ 2 * Real.exp (2 * u))) with hg
  have h1 : (fun n : ℕ => g ((n : ℤ) + 1)) = fun n : ℕ => thTerm 0 (n + 1) u := by
    funext n
    simp only [hg, thTerm, pow_zero, one_mul]
    norm_num
  have h2 : (fun n : ℕ => g (-((n : ℤ) + 1))) = fun n : ℕ => thTerm 0 (n + 1) u := by
    funext n
    simp only [hg, thTerm, pow_zero, one_mul]
    norm_num
    ring
  have hs1 : Summable (fun n : ℕ => g ((n : ℤ) + 1)) := by
    rw [h1]; exact summable_thTerm_succ 0 u
  have hs2 : Summable (fun n : ℕ => g (-((n : ℤ) + 1))) := by
    rw [h2]; exact summable_thTerm_succ 0 u
  have hz : g 0 = 1 := by simp [hg]
  rw [tsum_of_add_one_of_neg_add_one hs1 hs2, h1, h2, hz, T]
  ring

/--
@isnad1 id=eq.0h1v.s5.db64baff8b4f from=translated src=- shape=14888f0a vocab=f0848b38
-/
lemma rpow_half_exp (u : ℝ) : (Real.exp (2 * u)) ^ (1 / 2 : ℝ) = Real.exp u := by
  rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
  ring_nf

/-- **Jacobi's functional equation**, in the form needed here:
`1 + 2 T₀(−u) = e^u (1 + 2 T₀(u))`, i.e. `θ(e^{−2u}) = e^u θ(e^{2u})`.
@isnad1 id=eq.0h1v.s6.03dce26ec376 from=translated src=- shape=b16ead60 vocab=0590a783
-/
theorem theta_FE (u : ℝ) : 1 + 2 * T 0 (-u) = Real.exp u * (1 + 2 * T 0 u) := by
  have ha : (0 : ℝ) < Real.exp (2 * u) := Real.exp_pos _
  have key := Real.tsum_exp_neg_mul_int_sq ha
  have hL : (∑' m : ℤ, Real.exp (-π * Real.exp (2 * u) * (m : ℝ) ^ 2)) = 1 + 2 * T 0 u := by
    rw [← tsum_int_thTerm u]
    congr 1; funext m; congr 1; ring
  have hR : (∑' m : ℤ, Real.exp (-π / Real.exp (2 * u) * (m : ℝ) ^ 2)) = 1 + 2 * T 0 (-u) := by
    rw [← tsum_int_thTerm (-u)]
    congr 1; funext m; congr 1
    rw [show (2 : ℝ) * (-u) = -(2 * u) by ring, Real.exp_neg]
    field_simp
  rw [hL, hR, rpow_half_exp] at key
  have hexp : Real.exp u ≠ 0 := (Real.exp_pos u).ne'
  field_simp at key
  linarith [key]

/-! ### `Φ` in terms of the theta family -/

/--
@isnad1 id=eq.0h2v.s7.82b182e583df from=translated src=- shape=8af31ea2 vocab=d7e9d5bd
-/
lemma phiTerm_eq (n : ℕ) (u : ℝ) :
    phiTerm n u = 4 * Real.exp (9 * u / 2) * thTerm 2 n u -
      6 * Real.exp (5 * u / 2) * thTerm 1 n u := by
  simp only [phiTerm, thTerm]
  ring

/--
@isnad1 id=eq.0h1v.s7.ad3158a04684 from=translated src=- shape=5642a913 vocab=f9defe7a
-/
theorem Phi_eq_T (u : ℝ) :
    Phi u = 4 * Real.exp (9 * u / 2) * T 2 u - 6 * Real.exp (5 * u / 2) * T 1 u := by
  have h1 : Summable (fun n : ℕ => 4 * Real.exp (9 * u / 2) * thTerm 2 (n + 1) u) :=
    (summable_thTerm_succ 2 u).mul_left _
  have h2 : Summable (fun n : ℕ => 6 * Real.exp (5 * u / 2) * thTerm 1 (n + 1) u) :=
    (summable_thTerm_succ 1 u).mul_left _
  rw [Phi]
  have : (fun n : ℕ => phiTerm (n + 1) u) =
      fun n : ℕ => (4 * Real.exp (9 * u / 2) * thTerm 2 (n + 1) u) -
        (6 * Real.exp (5 * u / 2) * thTerm 1 (n + 1) u) := by
    funext n; exact phiTerm_eq (n + 1) u
  rw [this, h1.tsum_sub h2, tsum_mul_left, tsum_mul_left, T, T]

/-! ### The derivative chain `thP → thQ → thR`

`thP u = θ(e^{2u}) = 1 + 2 T₀(u)`, `thQ = thP'`, `thR = thQ'`.  Writing the functional
equation and its first two `u`-derivatives in these three unknowns keeps every exponential
factor packaged inside `thQ`/`thR`, so the final algebra never has to expand `e^{2u}`. -/

noncomputable def thP (u : ℝ) : ℝ := 1 + 2 * T 0 u

noncomputable def thQ (u : ℝ) : ℝ := -4 * Real.exp (2 * u) * T 1 u

noncomputable def thR (u : ℝ) : ℝ :=
  -8 * Real.exp (2 * u) * T 1 u + 8 * Real.exp (2 * u) * Real.exp (2 * u) * T 2 u

/--
@isnad1 id=hasderiv.0h1v.s5.7400962402a1 from=translated src=- shape=475e04ea vocab=7ad5d15f
-/
lemma hasDerivAt_thP (u : ℝ) : HasDerivAt thP (thQ u) u := by
  have h := ((hasDerivAt_T 0 u).const_mul (2 : ℝ)).const_add (1 : ℝ)
  have heq : thQ u = 2 * (-2 * Real.exp (2 * u) * T 1 u) := by unfold thQ; ring
  rw [heq]
  exact h

/--
@isnad1 id=hasderiv.0h1v.s5.9d31f06a70ae from=translated src=- shape=475e04ea vocab=5f07a04c
-/
lemma hasDerivAt_thQ (u : ℝ) : HasDerivAt thQ (thR u) u := by
  have h2 : HasDerivAt (fun v : ℝ => 2 * v) (2 : ℝ) u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have e2 : HasDerivAt (fun v : ℝ => Real.exp (2 * v)) (Real.exp (2 * u) * 2) u := h2.exp
  have hc : HasDerivAt (fun v : ℝ => -4 * Real.exp (2 * v)) (-4 * (Real.exp (2 * u) * 2)) u :=
    e2.const_mul (-4 : ℝ)
  have h := hc.mul (hasDerivAt_T 1 u)
  have heq : thR u = -4 * (Real.exp (2 * u) * 2) * T 1 u
      + -4 * Real.exp (2 * u) * (-2 * Real.exp (2 * u) * T 2 u) := by unfold thR; ring
  rw [heq]
  exact h

/--
@isnad1 id=hasderiv.0h1v.s5.d36486257357 from=translated src=- shape=bda15752 vocab=1ef76832
-/
lemma hasDerivAt_neg_self (u : ℝ) : HasDerivAt (fun v : ℝ => -v) (-1 : ℝ) u :=
  hasDerivAt_neg' u

/--
@isnad1 id=hasderiv.0h1v.s5.d368acbb28f2 from=translated src=- shape=8f07d889 vocab=b7352cae
-/
lemma hasDerivAt_thP_neg (u : ℝ) :
    HasDerivAt (fun v : ℝ => thP (-v)) (-(thQ (-u))) u := by
  have h := (hasDerivAt_thP (-u)).comp u (hasDerivAt_neg_self u)
  have heq : -(thQ (-u)) = thQ (-u) * (-1) := by ring
  rw [heq]
  exact h

/--
@isnad1 id=hasderiv.0h1v.s5.c376dea800fe from=translated src=- shape=8f07d889 vocab=593cd501
-/
lemma hasDerivAt_thQ_neg (u : ℝ) :
    HasDerivAt (fun v : ℝ => thQ (-v)) (-(thR (-u))) u := by
  have h := (hasDerivAt_thQ (-u)).comp u (hasDerivAt_neg_self u)
  have heq : -(thR (-u)) = thR (-u) * (-1) := by ring
  rw [heq]
  exact h

/--
@isnad1 id=hasderiv.0h1v.s5.3a879eacb2cf from=translated src=- shape=da260941 vocab=593cd501
-/
lemma hasDerivAt_negThQneg (u : ℝ) :
    HasDerivAt (fun v : ℝ => -(thQ (-v))) (thR (-u)) u := by
  have h := (hasDerivAt_thQ_neg u).neg
  have heq : thR (-u) = -(-(thR (-u))) := by ring
  rw [heq]
  exact h

/--
@isnad1 id=hasderiv.0h1v.s6.ee7e61b8f74c from=translated src=- shape=d7b9d9aa vocab=c7bac9cf
-/
lemma hasDerivAt_expThP (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp v * thP v)
      (Real.exp u * thP u + Real.exp u * thQ u) u :=
  (Real.hasDerivAt_exp u).mul (hasDerivAt_thP u)

/--
@isnad1 id=hasderiv.0h1v.s6.32d021cb867d from=translated src=- shape=1a45545e vocab=af224a7d
-/
lemma hasDerivAt_expThPQ (u : ℝ) :
    HasDerivAt (fun v : ℝ => Real.exp v * thP v + Real.exp v * thQ v)
      ((Real.exp u * thP u + Real.exp u * thQ u)
        + (Real.exp u * thQ u + Real.exp u * thR u)) u :=
  (hasDerivAt_expThP u).add ((Real.hasDerivAt_exp u).mul (hasDerivAt_thQ u))

/-- The functional equation, restated in `thP`.
@isnad1 id=eq.0h1v.s4.eecda2cb3686 from=translated src=- shape=110d0495 vocab=42ffd099
-/
theorem theta_FE_P (u : ℝ) : thP (-u) = Real.exp u * thP u := theta_FE u

/-- **First `u`-derivative of the functional equation.**
@isnad1 id=eq.0h1v.s5.743ed72ac3ef from=translated src=- shape=1fa7057c vocab=17dc375c
-/
theorem theta_FE_I (u : ℝ) :
    -(thQ (-u)) = Real.exp u * thP u + Real.exp u * thQ u := by
  have hfun : (fun v : ℝ => thP (-v)) = fun v : ℝ => Real.exp v * thP v := funext theta_FE_P
  have h1 := hasDerivAt_thP_neg u
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_expThP u)

/-- **Second `u`-derivative of the functional equation.**
@isnad1 id=eq.0h1v.s6.0c4031b5e368 from=translated src=- shape=25d6a1cd vocab=0bcf283a
-/
theorem theta_FE_II (u : ℝ) :
    thR (-u) = (Real.exp u * thP u + Real.exp u * thQ u)
      + (Real.exp u * thQ u + Real.exp u * thR u) := by
  have hfun : (fun v : ℝ => -(thQ (-v)))
      = fun v : ℝ => Real.exp v * thP v + Real.exp v * thQ v := funext theta_FE_I
  have h1 := hasDerivAt_negThQneg u
  rw [hfun] at h1
  exact h1.unique (hasDerivAt_expThPQ u)

/-- `Φ = ½ e^{u/2} (θ'' + θ')`, in the packaged form `½ e^{u/2} (thQ + thR)`.
@isnad1 id=eq.0h1v.s6.0252f16ba85a from=translated src=- shape=94f7e66b vocab=45a4a0a3
-/
theorem Phi_eq_thQR (u : ℝ) : Phi u = 1 / 2 * Real.exp (u / 2) * (thQ u + thR u) := by
  have p1 : Real.exp (u / 2) * Real.exp (2 * u) = Real.exp (5 * u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  have p2 : Real.exp (u / 2) * (Real.exp (2 * u) * Real.exp (2 * u)) = Real.exp (9 * u / 2) := by
    rw [← Real.exp_add, ← Real.exp_add]; congr 1; ring
  rw [Phi_eq_T]
  unfold thQ thR
  linear_combination (-4 * T 2 u) * p2 + (6 * T 1 u) * p1

/-- **`Φ` is even.**  This is the Jacobi theta functional equation
`θ(1/x) = √x · θ(x)` differentiated twice in `x`.
@isnad1 id=eq.0h1v.s3.5ca2c1ad6815 from=translated src=- shape=cd419dad vocab=ac9c5fc9
-/
theorem Phi_even (u : ℝ) : Phi (-u) = Phi u := by
  have hI := theta_FE_I u
  have hII := theta_FE_II u
  have hsum : thQ (-u) + thR (-u) = Real.exp u * (thQ u + thR u) := by
    linear_combination hII - hI
  have hp : Real.exp (-u / 2) * Real.exp u = Real.exp (u / 2) := by
    rw [← Real.exp_add]; congr 1; ring
  rw [Phi_eq_thQR (-u), Phi_eq_thQR u, hsum]
  linear_combination (1 / 2 * (thQ u + thR u)) * hp

/-- `Φ'` is odd, so it vanishes at the origin.  This is the whole point of `Phi_even`:
no truncation of the defining series has this property.
@isnad1 id=eq.0h0v.s5.8de4f4ca2ad4 from=translated src=- shape=874afe33 vocab=61406803
-/
theorem deriv_Phi_zero : deriv Phi 0 = 0 := by
  have hfun : (fun v : ℝ => Phi (-v)) = Phi := funext Phi_even
  have h0 : HasDerivAt Phi (deriv Phi (-(0 : ℝ))) (-(0 : ℝ)) :=
    (differentiable_Phi _).hasDerivAt
  have hneg : HasDerivAt (fun v : ℝ => Phi (-v)) (deriv Phi (-(0 : ℝ)) * (-1)) 0 :=
    h0.comp (0 : ℝ) (hasDerivAt_neg_self 0)
  rw [hfun, neg_zero] at hneg
  have hd : HasDerivAt Phi (deriv Phi 0) 0 := (differentiable_Phi 0).hasDerivAt
  have h := hneg.unique hd
  linarith

/-! ### The second derivative of `Φ`

Writing `q = π n²` and `X = q e^{2u}`, `Wintner.phiTerm'` is `−q e^{5u/2} e^{−X}(8X²−30X+15)`,
whose `u`-derivative is `q e^{5u/2} e^{−X}(16X³ − 112X² + 165X − 37.5)`. -/

/-- `d²/du²` of `XiLab.phiTerm n`.-/
noncomputable def phiTerm'' (n : ℕ) (u : ℝ) : ℝ :=
  π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
      Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
    (16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 3 -
      112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 +
      165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) - 75 / 2)

/--
@isnad1 id=hasderiv.0h2v.s5.347c438b3519 from=translated src=- shape=f4cbe5c8 vocab=7bfafec0
-/
lemma hasDerivAt_phiTerm' (n : ℕ) (u : ℝ) : HasDerivAt (phiTerm' n) (phiTerm'' n u) u := by
  have h2 : HasDerivAt (fun v : ℝ => 2 * v) (2 : ℝ) u := by
    simpa using (hasDerivAt_id u).const_mul (2 : ℝ)
  have h5 : HasDerivAt (fun v : ℝ => 5 * v / 2) (5 / 2 : ℝ) u := by
    simpa using ((hasDerivAt_id u).const_mul (5 : ℝ)).div_const 2
  have e2 : HasDerivAt (fun v : ℝ => Real.exp (2 * v)) (Real.exp (2 * u) * 2) u := h2.exp
  have e5 : HasDerivAt (fun v : ℝ => Real.exp (5 * v / 2))
      (Real.exp (5 * u / 2) * (5 / 2)) u := h5.exp
  have hW : HasDerivAt (fun v : ℝ => π * (n : ℝ) ^ 2 * Real.exp (2 * v))
      (π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2)) u := e2.const_mul _
  have hEX : HasDerivAt (fun v : ℝ => Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * v))))
      (Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
        (-(π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2)))) u := hW.neg.exp
  have hWW : HasDerivAt
      (fun v : ℝ => π * (n : ℝ) ^ 2 * Real.exp (2 * v) * (π * (n : ℝ) ^ 2 * Real.exp (2 * v)))
      (π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2) * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) +
        π * (n : ℝ) ^ 2 * Real.exp (2 * u) * (π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2))) u :=
    hW.mul hW
  have hsq : (fun v : ℝ =>
      π * (n : ℝ) ^ 2 * Real.exp (2 * v) * (π * (n : ℝ) ^ 2 * Real.exp (2 * v)))
      = fun v : ℝ => (π * (n : ℝ) ^ 2 * Real.exp (2 * v)) ^ 2 := by funext v; ring
  rw [hsq] at hWW
  have hP := ((hWW.const_mul (8 : ℝ)).sub (hW.const_mul (30 : ℝ))).add_const (15 : ℝ)
  have hA : HasDerivAt (fun v : ℝ => -(π * (n : ℝ) ^ 2) * Real.exp (5 * v / 2))
      (-(π * (n : ℝ) ^ 2) * (Real.exp (5 * u / 2) * (5 / 2))) u := e5.const_mul _
  have hC := (hA.mul hEX).mul hP
  have hfun : phiTerm' n = fun v : ℝ =>
      -(π * (n : ℝ) ^ 2) * Real.exp (5 * v / 2) *
        Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * v))) *
        (8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * v)) ^ 2 -
          30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * v)) + 15) := rfl
  have heq : phiTerm'' n u =
      (-(π * (n : ℝ) ^ 2) * (Real.exp (5 * u / 2) * (5 / 2)) *
          Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) +
        -(π * (n : ℝ) ^ 2) * Real.exp (5 * u / 2) *
          (Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
            (-(π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2))))) *
        (8 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 -
          30 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 15) +
      -(π * (n : ℝ) ^ 2) * Real.exp (5 * u / 2) *
          Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
        (8 * (π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2) * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) +
              π * (n : ℝ) ^ 2 * Real.exp (2 * u) * (π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2))) -
          30 * (π * (n : ℝ) ^ 2 * (Real.exp (2 * u) * 2))) := by
    unfold phiTerm''; ring
  rw [hfun, heq]
  exact hC

/-! ### A locally uniform majorant for the twice-differentiated series -/

/--
@isnad1 id=le.2h2v.s6.df04cf7823e3 from=translated src=- shape=1b9d0e8c vocab=ef525443
-/
lemma cast_pow_le_pow_eight (n : ℕ) {i : ℕ} (h1 : 1 ≤ i) (h2 : i ≤ 8) :
    (n : ℝ) ^ i ≤ (n : ℝ) ^ 8 := by
  rcases Nat.eq_zero_or_pos n with rfl | h
  · rw [Nat.cast_zero, zero_pow (by omega : i ≠ 0), zero_pow (by norm_num : (8:ℕ) ≠ 0)]
  · exact pow_le_pow_right₀ (by exact_mod_cast h) h2

/-- Majorant for `|phiTerm'' n u|`, uniform for `u ∈ [a,b]`: `C(a,b) · n⁸ · r(a)^n`.-/
noncomputable def deriv2Bound (a b : ℝ) (n : ℕ) : ℝ :=
  (Real.exp (5 * b / 2) *
      (16 * π ^ 4 * Real.exp (6 * b) + 112 * π ^ 3 * Real.exp (4 * b) +
        165 * π ^ 2 * Real.exp (2 * b) + 75 / 2 * π)) *
    ((n : ℝ) ^ 8 * Real.exp (-(π * Real.exp (2 * a))) ^ n)

/--
@isnad1 id=summable.0h2v.s4.fb2a572d4811 from=translated src=- shape=ddf3513c vocab=5101c246
-/
theorem summable_deriv2Bound (a b : ℝ) : Summable (deriv2Bound a b) :=
  (summable_pow_mul_geometric_of_norm_lt_one 8 (norm_exp_neg_pi_exp_lt_one a)).mul_left _

/--
@isnad1 id=le.2h4v.s5.276cf8d076f1 from=translated src=- shape=569bf207 vocab=b66c46a3
-/
lemma abs_phiTerm''_le {a b : ℝ} (n : ℕ) {u : ℝ} (hau : a ≤ u) (hub : u ≤ b) :
    |phiTerm'' n u| ≤ deriv2Bound a b n := by
  have hpi := Real.pi_pos
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
  have hx0 : (0 : ℝ) ≤ π * (n : ℝ) ^ 2 * Real.exp (2 * u) := by positivity
  have hpre0 : (0 : ℝ) ≤ π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
      Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) := by positivity
  rw [phiTerm'', abs_mul, abs_of_nonneg hpre0]
  -- Step 1: `|16X³ − 112X² + 165X − 37.5| ≤ 16X³ + 112X² + 165X + 37.5`.
  have hP : |16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 3 -
      112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 +
      165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) - 75 / 2| ≤
      16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 3 +
        112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 +
        165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 75 / 2 := by
    have hX3 : (0 : ℝ) ≤ (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 3 := pow_nonneg hx0 3
    have hX2 : (0 : ℝ) ≤ (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 := sq_nonneg _
    rw [abs_le]
    constructor
    · nlinarith [hx0, hX3, hX2]
    · nlinarith [hx0, hX3, hX2]
  -- Step 2: monotone replacement `u → b` inside the polynomial.
  have hEb : Real.exp (2 * u) ≤ Real.exp (2 * b) := Real.exp_le_exp.mpr (by linarith)
  have hXb : π * (n : ℝ) ^ 2 * Real.exp (2 * u) ≤ π * (n : ℝ) ^ 2 * Real.exp (2 * b) :=
    mul_le_mul_of_nonneg_left hEb (by positivity)
  have hxb0 : (0 : ℝ) ≤ π * (n : ℝ) ^ 2 * Real.exp (2 * b) := by positivity
  have hQ : 16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 3 +
      112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 +
      165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) + 75 / 2 ≤
      16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 3 +
        112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 +
        165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) + 75 / 2 := by
    have hc3 : (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 3 ≤
        (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 3 := pow_le_pow_left₀ hx0 hXb 3
    have hc2 : (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 ≤
        (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 := pow_le_pow_left₀ hx0 hXb 2
    linarith
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
  have hpre : π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
        Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) ≤
      π * (n : ℝ) ^ 2 * (Real.exp (5 * b / 2) * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by
    have hpow : (0 : ℝ) ≤ Real.exp (-(π * Real.exp (2 * a))) ^ n :=
      pow_nonneg (Real.exp_pos _).le n
    have hstep : Real.exp (5 * u / 2) * Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) ≤
        Real.exp (5 * b / 2) * Real.exp (-(π * Real.exp (2 * a))) ^ n :=
      mul_le_mul h5b hEa (Real.exp_pos _).le (Real.exp_pos _).le
    calc π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
          Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))
        = π * (n : ℝ) ^ 2 * (Real.exp (5 * u / 2) *
            Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u)))) := by ring
      _ ≤ π * (n : ℝ) ^ 2 * (Real.exp (5 * b / 2) *
            Real.exp (-(π * Real.exp (2 * a))) ^ n) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
  calc π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
        Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
        |16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 3 -
          112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 +
          165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) - 75 / 2|
      ≤ (π * (n : ℝ) ^ 2 * (Real.exp (5 * b / 2) *
            Real.exp (-(π * Real.exp (2 * a))) ^ n)) *
          (16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 3 +
            112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 +
            165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) + 75 / 2) := by
        refine mul_le_mul hpre (hP.trans hQ) (abs_nonneg _) ?_
        positivity
    _ ≤ deriv2Bound a b n := by
        have hpow : (0 : ℝ) ≤ Real.exp (-(π * Real.exp (2 * a))) ^ n :=
          pow_nonneg (Real.exp_pos _).le n
        have h2 := cast_pow_le_pow_eight n (by norm_num : 1 ≤ 2) (by norm_num : 2 ≤ 8)
        have h4 := cast_pow_le_pow_eight n (by norm_num : 1 ≤ 4) (by norm_num : 4 ≤ 8)
        have h6 := cast_pow_le_pow_eight n (by norm_num : 1 ≤ 6) (by norm_num : 6 ≤ 8)
        have hE6 : Real.exp (2 * b) ^ 3 = Real.exp (6 * b) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have hE4 : Real.exp (2 * b) ^ 2 = Real.exp (4 * b) := by
          rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
        have hEb0 : (0 : ℝ) < Real.exp (2 * b) := Real.exp_pos _
        have h5b0 : (0 : ℝ) < Real.exp (5 * b / 2) := Real.exp_pos _
        rw [deriv2Bound]
        have key : π * (n : ℝ) ^ 2 *
              (16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 3 +
                112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 +
                165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) + 75 / 2) ≤
            (16 * π ^ 4 * Real.exp (6 * b) + 112 * π ^ 3 * Real.exp (4 * b) +
              165 * π ^ 2 * Real.exp (2 * b) + 75 / 2 * π) * (n : ℝ) ^ 8 := by
          rw [← hE6, ← hE4]
          have t6 : 112 * π ^ 3 * Real.exp (2 * b) ^ 2 * (n : ℝ) ^ 6 ≤
              112 * π ^ 3 * Real.exp (2 * b) ^ 2 * (n : ℝ) ^ 8 :=
            mul_le_mul_of_nonneg_left h6 (by positivity)
          have t4 : 165 * π ^ 2 * Real.exp (2 * b) * (n : ℝ) ^ 4 ≤
              165 * π ^ 2 * Real.exp (2 * b) * (n : ℝ) ^ 8 :=
            mul_le_mul_of_nonneg_left h4 (by positivity)
          have t2 : 75 / 2 * π * (n : ℝ) ^ 2 ≤ 75 / 2 * π * (n : ℝ) ^ 8 :=
            mul_le_mul_of_nonneg_left h2 (by positivity)
          nlinarith [t6, t4, t2]
        calc (π * (n : ℝ) ^ 2 * (Real.exp (5 * b / 2) *
                Real.exp (-(π * Real.exp (2 * a))) ^ n)) *
              (16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 3 +
                112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 +
                165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) + 75 / 2)
            = (π * (n : ℝ) ^ 2 *
                (16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 3 +
                  112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) ^ 2 +
                  165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * b)) + 75 / 2)) *
                (Real.exp (5 * b / 2) * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by ring
          _ ≤ ((16 * π ^ 4 * Real.exp (6 * b) + 112 * π ^ 3 * Real.exp (4 * b) +
                165 * π ^ 2 * Real.exp (2 * b) + 75 / 2 * π) * (n : ℝ) ^ 8) *
                (Real.exp (5 * b / 2) * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by
              refine mul_le_mul_of_nonneg_right key ?_
              positivity
          _ = (Real.exp (5 * b / 2) *
                (16 * π ^ 4 * Real.exp (6 * b) + 112 * π ^ 3 * Real.exp (4 * b) +
                  165 * π ^ 2 * Real.exp (2 * b) + 75 / 2 * π)) *
                ((n : ℝ) ^ 8 * Real.exp (-(π * Real.exp (2 * a))) ^ n) := by ring

/--
@isnad1 id=summable.0h1v.s4.51e637e509b9 from=translated src=- shape=0b46e227 vocab=a5107c4d
-/
theorem summable_phiTerm'' (x : ℝ) : Summable (fun n : ℕ => phiTerm'' n x) := by
  refine Summable.of_norm_bounded (summable_deriv2Bound (x - 1) (x + 1)) (fun n => ?_)
  simpa [Real.norm_eq_abs] using
    abs_phiTerm''_le n (by linarith : x - 1 ≤ x) (by linarith : x ≤ x + 1)

/--
@isnad1 id=summable.0h1v.s4.365e500054ac from=translated src=- shape=7f8378ff vocab=1f74bc36
-/
theorem summable_phiTerm''_succ (x : ℝ) : Summable (fun n : ℕ => phiTerm'' (n + 1) x) :=
  (summable_nat_add_iff 1).mpr (summable_phiTerm'' x)

/-- `Φ'`, as the termwise sum.-/
noncomputable def PhiD (x : ℝ) : ℝ := ∑' n : ℕ, phiTerm' (n + 1) x

/-- `Φ''`, as the termwise sum.-/
noncomputable def PhiDD (x : ℝ) : ℝ := ∑' n : ℕ, phiTerm'' (n + 1) x

/--
@isnad1 id=eq.0h0v.s5.b52cf44dd5ab from=translated src=- shape=0cc26a1b vocab=bf0fdf21
-/
theorem PhiD_eq_deriv : PhiD = deriv Phi := by
  funext x; rw [PhiD, deriv_Phi]

/-- **`Φ'` may be differentiated term by term.**
@isnad1 id=hasderiv.0h1v.s5.5ebe017b3a7b from=translated src=- shape=475e04ea vocab=2cc5dc9f
-/
theorem hasDerivAt_PhiD (x : ℝ) : HasDerivAt PhiD (PhiDD x) x := by
  have hmem : x ∈ Ioo (x - 1) (x + 1) := ⟨by linarith, by linarith⟩
  have hsum : Summable (fun n : ℕ => deriv2Bound (x - 1) (x + 1) (n + 1)) :=
    (summable_nat_add_iff 1).mpr (summable_deriv2Bound _ _)
  exact hasDerivAt_tsum_of_isPreconnected
    (u := fun n : ℕ => deriv2Bound (x - 1) (x + 1) (n + 1))
    (g := fun n : ℕ => phiTerm' (n + 1)) (g' := fun (n : ℕ) (v : ℝ) => phiTerm'' (n + 1) v)
    hsum isOpen_Ioo isPreconnected_Ioo
    (fun n y _ => hasDerivAt_phiTerm' (n + 1) y)
    (fun n y hy => by
      rw [Real.norm_eq_abs]
      exact abs_phiTerm''_le (n + 1) hy.1.le hy.2.le)
    hmem (summable_phiTerm'_succ x) hmem

/-! ### Numerical inputs

Every constant below is proved from `Real.pi_gt_d6`, `Real.pi_lt_d20`, `Real.exp_one_gt_d9`,
`Real.exp_one_lt_d9` and `Real.add_one_le_exp`.  Nothing is `norm_num`-on-`Real.exp`. -/

/--
@isnad1 id=le.1h1v.s5.9b6154ced78a from=translated src=- shape=71e15312 vocab=e030a0d9
-/
lemma exp_le_of_le_inv_160 {x : ℝ} (hx : x ≤ 1 / 160) : Real.exp x ≤ 101 / 100 := by
  have h1 : Real.exp x ≤ Real.exp (1 / 160) := Real.exp_le_exp.mpr hx
  have hp : (0 : ℝ) < Real.exp (1 / 160 : ℝ) := Real.exp_pos _
  have h2 : (1 - 1 / 160 : ℝ) ≤ (Real.exp (1 / 160 : ℝ))⁻¹ := by
    have h := Real.add_one_le_exp (-(1 / 160 : ℝ))
    rw [Real.exp_neg] at h
    linarith
  have h3 := mul_le_mul_of_nonneg_right h2 hp.le
  rw [inv_mul_cancel₀ hp.ne'] at h3
  linarith

/--
@isnad1 id=lt.0h0v.s4.a858fe2299ed from=translated src=- shape=3c26ae4f vocab=0dda0365
-/
lemma exp_four_lt : Real.exp 4 < 55 := by
  have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  have hp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hs : Real.exp 1 ^ 2 < 7.3891 := by nlinarith [h, hp]
  rw [h4]
  nlinarith [hs, sq_nonneg (Real.exp 1)]

/--
@isnad1 id=lt.0h0v.s4.cf0ae955a4f4 from=translated src=- shape=cf0a9d99 vocab=0dda0365
-/
lemma exp_four_gt : (54 : ℝ) < Real.exp 4 := by
  have h : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have hp : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
  have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hs : (7.389 : ℝ) < Real.exp 1 ^ 2 := by nlinarith [h, hp]
  rw [h4]
  nlinarith [hs, sq_nonneg (Real.exp 1)]

/--
@isnad1 id=lt.0h0v.s4.6cdb596128cc from=translated src=- shape=cf0a9d99 vocab=0dda0365
-/
lemma exp_twelve_gt : (157000 : ℝ) < Real.exp 12 := by
  have h12 : Real.exp 12 = Real.exp 4 ^ 3 := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have h := exp_four_gt
  have hp : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  have hfac : (0 : ℝ) < Real.exp 4 ^ 2 + 54 * Real.exp 4 + 2916 := by positivity
  rw [h12]
  nlinarith [mul_pos (sub_pos.mpr h) hfac]

/--
@isnad1 id=le.0h0v.s5.351b559ea1a5 from=translated src=- shape=df5507f0 vocab=ff3fd5be
-/
lemma exp_neg_four_ge : (1 / 55 : ℝ) ≤ Real.exp (-4) := by
  have h3 : Real.exp 4 < 55 := exp_four_lt
  have h4 : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  have hp : (0 : ℝ) < Real.exp (-4) := Real.exp_pos _
  have hmul : Real.exp (-4) * Real.exp 4 = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [hmul, h3, hp, h4]

/--
@isnad1 id=le.0h0v.s5.9a18ecb874ff from=translated src=- shape=a644ce02 vocab=ff3fd5be
-/
lemma exp_neg_four_le : Real.exp (-4) ≤ 1 / 54 := by
  have h3 : (54 : ℝ) < Real.exp 4 := exp_four_gt
  have h4 : (0 : ℝ) < Real.exp 4 := Real.exp_pos 4
  have hp : (0 : ℝ) < Real.exp (-4) := Real.exp_pos _
  have hmul : Real.exp (-4) * Real.exp 4 = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [hmul, h3, hp, h4]

/--
@isnad1 id=le.0h0v.s5.d808a296e3be from=translated src=- shape=a644ce02 vocab=ff3fd5be
-/
lemma exp_neg_twelve_le : Real.exp (-12) ≤ 1 / 157000 := by
  have h3 : (157000 : ℝ) < Real.exp 12 := exp_twelve_gt
  have h4 : (0 : ℝ) < Real.exp 12 := Real.exp_pos 12
  have hp : (0 : ℝ) < Real.exp (-12) := Real.exp_pos _
  have hmul : Real.exp (-12) * Real.exp 12 = 1 := by
    rw [← Real.exp_add]; norm_num
  nlinarith [hmul, h3, hp, h4]

/-! ### The three blocks of `Φ''` on `[0, 1/400]`

Written with the prefactor `q = π n²` and `X = q e^{2u}` abstracted, so that each block is a
statement about real numbers only. -/

/--
@isnad1 id=eq.0h2v.s8.b9ac74c7b7ee from=translated src=- shape=772bd955 vocab=e8e48d68
-/
lemma phiTerm''_eq (n : ℕ) (u : ℝ) :
    phiTerm'' n u = π * (n : ℝ) ^ 2 * Real.exp (5 * u / 2) *
      Real.exp (-(π * (n : ℝ) ^ 2 * Real.exp (2 * u))) *
      (16 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 3 -
        112 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) ^ 2 +
        165 * (π * (n : ℝ) ^ 2 * Real.exp (2 * u)) - 75 / 2) := rfl

/-- `n = 1`: the dominant, strongly negative block.
@isnad1 id=le.4h3v.s7.363d01bdd188 from=translated src=- shape=b4d2136b vocab=f60428bd
-/
lemma term_one_bound {q E5 X : ℝ} (hq : (3.14 : ℝ) ≤ q) (hE5 : (1 : ℝ) ≤ E5)
    (hXlo : (3.14 : ℝ) ≤ X) (hXhi : X ≤ 3.19) :
    q * E5 * Real.exp (-X) * (16 * X ^ 3 - 112 * X ^ 2 + 165 * X - 75 / 2) ≤ -5.7 := by
  have ht1 : (0 : ℝ) ≤ X - 3.14 := by linarith
  have ht2 : (0 : ℝ) ≤ 3.19 - X := by linarith
  have hB : 16 * X ^ 3 - 112 * X ^ 2 + 165 * X - 75 / 2 ≤ -100 := by
    nlinarith [mul_nonneg ht1 ht2, mul_nonneg (mul_nonneg ht1 ht1) ht2, ht1, ht2,
      sq_nonneg (X - 3.14)]
  have hEX : (1 / 55 : ℝ) ≤ Real.exp (-X) := by
    have h1 : Real.exp (-(4 : ℝ)) ≤ Real.exp (-X) := Real.exp_le_exp.mpr (by linarith)
    linarith [exp_neg_four_ge, h1]
  have hqE : (3.14 : ℝ) * 1 ≤ q * E5 := mul_le_mul hq hE5 (by norm_num) (by linarith)
  have hA : (3.14 : ℝ) * (1 / 55) ≤ q * E5 * Real.exp (-X) :=
    mul_le_mul (by linarith) hEX (by norm_num) (by linarith)
  have hApos : (0 : ℝ) ≤ q * E5 * Real.exp (-X) := by nlinarith [hA]
  have s1 : q * E5 * Real.exp (-X) * (16 * X ^ 3 - 112 * X ^ 2 + 165 * X - 75 / 2)
      ≤ q * E5 * Real.exp (-X) * (-100) := mul_le_mul_of_nonneg_left hB hApos
  nlinarith [s1, hA]

/-- `n = 2`: the only positive block, and it is small.
@isnad1 id=le.6h3v.s8.5b1609b27cff from=translated src=- shape=1e35ab3b vocab=f60428bd
-/
lemma term_two_bound {q E5 X : ℝ} (hq0 : (0 : ℝ) ≤ q) (hq : q ≤ 12.6) (hE50 : (0 : ℝ) ≤ E5)
    (hE5 : E5 ≤ 101 / 100) (hXlo : (12 : ℝ) ≤ X) (hXhi : X ≤ 12.726) :
    q * E5 * Real.exp (-X) * (16 * X ^ 3 - 112 * X ^ 2 + 165 * X - 75 / 2) ≤ 2.9 := by
  have hX0 : (0 : ℝ) ≤ X := by linarith
  have hB : 16 * X ^ 3 - 112 * X ^ 2 + 165 * X - 75 / 2 ≤ 35100 := by
    have h3 : X ^ 3 ≤ (12.726 : ℝ) ^ 3 := pow_le_pow_left₀ hX0 hXhi 3
    nlinarith [h3, sq_nonneg X, hXhi]
  have hEX : Real.exp (-X) ≤ 1 / 157000 := by
    have h1 : Real.exp (-X) ≤ Real.exp (-(12 : ℝ)) := Real.exp_le_exp.mpr (by linarith)
    linarith [exp_neg_twelve_le, h1]
  have h1 : q * E5 ≤ 12.6 * (101 / 100) := mul_le_mul hq hE5 hE50 (by norm_num)
  have hA : q * E5 * Real.exp (-X) ≤ 12.6 * (101 / 100) * (1 / 157000) :=
    mul_le_mul h1 hEX (Real.exp_pos _).le (by norm_num)
  have hA0 : (0 : ℝ) ≤ q * E5 * Real.exp (-X) :=
    mul_nonneg (mul_nonneg hq0 hE50) (Real.exp_pos _).le
  calc q * E5 * Real.exp (-X) * (16 * X ^ 3 - 112 * X ^ 2 + 165 * X - 75 / 2)
      ≤ q * E5 * Real.exp (-X) * 35100 := mul_le_mul_of_nonneg_left hB hA0
    _ ≤ 12.6 * (101 / 100) * (1 / 157000) * 35100 :=
        mul_le_mul_of_nonneg_right hA (by norm_num)
    _ ≤ 2.9 := by norm_num

/-- `n ≥ 3`: a geometric tail.  The polynomial is killed by `X⁴ ≤ 4096 e^{X/2}`, which is just
`X/8 ≤ e^{X/8}` raised to the fourth power.
@isnad1 id=le.5h3v.s8.37b6133fc65a from=translated src=- shape=41f41dca vocab=cfdef964
-/
lemma term_tail_bound {q E5 X : ℝ} (hq0 : (0 : ℝ) ≤ q) (hqX : q ≤ X) (hX : (28 : ℝ) ≤ X)
    (hE50 : (0 : ℝ) ≤ E5) (hE5 : E5 ≤ 101 / 100) :
    |q * E5 * Real.exp (-X) * (16 * X ^ 3 - 112 * X ^ 2 + 165 * X - 75 / 2)|
      ≤ 94208 * Real.exp (-(X / 2)) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hEX : (0 : ℝ) < Real.exp (-X) := Real.exp_pos _
  have hpre0 : (0 : ℝ) ≤ q * E5 * Real.exp (-X) :=
    mul_nonneg (mul_nonneg hq0 hE50) hEX.le
  rw [abs_mul, abs_of_nonneg hpre0]
  have h28 : (0 : ℝ) ≤ (X - 28) * X ^ 2 := mul_nonneg (by linarith) (sq_nonneg X)
  have hB : |16 * X ^ 3 - 112 * X ^ 2 + 165 * X - 75 / 2| ≤ 22 * X ^ 3 := by
    rw [abs_le]
    constructor
    · nlinarith [h28, hX0, sq_nonneg X]
    · nlinarith [h28, hX0, sq_nonneg X]
  have hpre : q * E5 * Real.exp (-X) ≤ X * (101 / 100) * Real.exp (-X) := by
    have h1 : q * E5 ≤ X * (101 / 100) := mul_le_mul hqX hE5 hE50 (by linarith)
    exact mul_le_mul_of_nonneg_right h1 hEX.le
  have hX4 : X ^ 4 ≤ 4096 * Real.exp (X / 2) := by
    have h1 : X / 8 ≤ Real.exp (X / 8) := by linarith [Real.add_one_le_exp (X / 8)]
    have h2 : (X / 8) ^ 4 ≤ Real.exp (X / 8) ^ 4 :=
      pow_le_pow_left₀ (by linarith) h1 4
    have h3 : Real.exp (X / 8) ^ 4 = Real.exp (X / 2) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [h3] at h2
    linarith
  have hEE : Real.exp (X / 2) * Real.exp (-X) = Real.exp (-(X / 2)) := by
    rw [← Real.exp_add]; congr 1; ring
  calc q * E5 * Real.exp (-X) * |16 * X ^ 3 - 112 * X ^ 2 + 165 * X - 75 / 2|
      ≤ X * (101 / 100) * Real.exp (-X) * (22 * X ^ 3) := by
        refine mul_le_mul hpre hB (abs_nonneg _) ?_
        exact mul_nonneg (mul_nonneg hX0.le (by norm_num)) hEX.le
    _ = 101 / 100 * 22 * (X ^ 4 * Real.exp (-X)) := by ring
    _ ≤ 101 / 100 * 22 * (4096 * Real.exp (X / 2) * Real.exp (-X)) := by
        have hstep := mul_le_mul_of_nonneg_right hX4 hEX.le
        nlinarith [hstep]
    _ = 101 / 100 * 22 * 4096 * Real.exp (-(X / 2)) := by rw [← hEE]; ring
    _ ≤ 94208 * Real.exp (-(X / 2)) := by
        have := (Real.exp_pos (-(X / 2))).le
        nlinarith

/-! ### The three blocks, instantiated -/

/--
@isnad1 id=and.0h0v.s4.4aae796b7092 from=translated src=- shape=fc8ed4a3 vocab=489aaca7
-/
lemma pi_bounds : (3.14 : ℝ) < π ∧ π < 3.15 :=
  ⟨lt_trans (by norm_num) Real.pi_gt_d6, lt_trans Real.pi_lt_d20 (by norm_num)⟩

/--
@isnad1 id=le.2h1v.s5.8bdaa0116174 from=translated src=- shape=242c7870 vocab=6277261f
-/
lemma phiTerm''_one_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 400) : phiTerm'' 1 u ≤ -5.7 := by
  obtain ⟨hpi1, hpi2⟩ := pi_bounds
  have hE2lo : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hE2hi : Real.exp (2 * u) ≤ 101 / 100 := exp_le_of_le_inv_160 (by linarith)
  have hE5lo : (1 : ℝ) ≤ Real.exp (5 * u / 2) := Real.one_le_exp (by linarith)
  have hc : ((1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
  rw [phiTerm''_eq, hc]
  refine term_one_bound (q := π * 1) (E5 := Real.exp (5 * u / 2))
    (X := π * 1 * Real.exp (2 * u)) (by linarith) hE5lo ?_ ?_
  · nlinarith [hE2lo, hpi1]
  · nlinarith [hE2hi, hpi2, Real.exp_pos (2 * u)]

/--
@isnad1 id=le.2h1v.s5.a7fbf6b11012 from=translated src=- shape=f68fea93 vocab=77e229f2
-/
lemma phiTerm''_two_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 400) : phiTerm'' 2 u ≤ 2.9 := by
  obtain ⟨hpi1, hpi2⟩ := pi_bounds
  have hE2lo : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hE2hi : Real.exp (2 * u) ≤ 101 / 100 := exp_le_of_le_inv_160 (by linarith)
  have hE5hi : Real.exp (5 * u / 2) ≤ 101 / 100 := exp_le_of_le_inv_160 (by linarith)
  have hc : ((2 : ℕ) : ℝ) ^ 2 = 4 := by norm_num
  rw [phiTerm''_eq, hc]
  refine term_two_bound (q := π * 4) (E5 := Real.exp (5 * u / 2))
    (X := π * 4 * Real.exp (2 * u)) (by positivity) (by linarith) (Real.exp_pos _).le hE5hi
    ?_ ?_
  · nlinarith [hE2lo, hpi1]
  · nlinarith [hE2hi, hpi2, Real.exp_pos (2 * u)]

/--
@isnad1 id=le.3h2v.s6.45f3bbe93f78 from=translated src=- shape=5dcc0290 vocab=4c523b9d
-/
lemma phiTerm''_tail_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 400) {m : ℕ} (hm : 3 ≤ m) :
    |phiTerm'' m u| ≤ 94208 * Real.exp (-4) ^ m := by
  obtain ⟨hpi1, hpi2⟩ := pi_bounds
  have hE2lo : (1 : ℝ) ≤ Real.exp (2 * u) := Real.one_le_exp (by linarith)
  have hE5hi : Real.exp (5 * u / 2) ≤ 101 / 100 := exp_le_of_le_inv_160 (by linarith)
  have hm3 : (3 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hq0 : (0 : ℝ) ≤ π * (m : ℝ) ^ 2 := by positivity
  have hmm : 3 * (m : ℝ) ≤ (m : ℝ) ^ 2 := by nlinarith
  have hqX : π * (m : ℝ) ^ 2 ≤ π * (m : ℝ) ^ 2 * Real.exp (2 * u) := by
    nlinarith [hq0, hE2lo]
  have hs1 : (3.14 : ℝ) * (3 * (m : ℝ)) ≤ π * (m : ℝ) ^ 2 := by
    nlinarith [hmm, hpi1, hm3, sq_nonneg ((m : ℝ))]
  have hX28 : (28 : ℝ) ≤ π * (m : ℝ) ^ 2 * Real.exp (2 * u) := by
    nlinarith [hs1, hqX, hm3]
  rw [phiTerm''_eq]
  refine (term_tail_bound hq0 hqX hX28 (Real.exp_pos _).le hE5hi).trans ?_
  have hfin : Real.exp (-(π * (m : ℝ) ^ 2 * Real.exp (2 * u) / 2)) ≤ Real.exp (-4) ^ m := by
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have h1 : (8 : ℝ) * (m : ℝ) ≤ π * (m : ℝ) ^ 2 * Real.exp (2 * u) := by
      nlinarith [hs1, hqX, hm3]
    linarith
  linarith [hfin]

/-! ### `Φ'' < 0` on `[0, 1/400]` -/

/--
@isnad1 id=eq.0h1v.s4.53b9a6ed45d8 from=translated src=- shape=a0dd47fb vocab=df794492
-/
@[simp] lemma phiTerm''_zero_index (u : ℝ) : phiTerm'' 0 u = 0 := by simp [phiTerm'']

/--
@isnad1 id=eq.0h1v.s4.ef90e9152a3d from=translated src=- shape=53cec0e6 vocab=9ae3519d
-/
theorem PhiDD_eq_tsum (u : ℝ) : PhiDD u = ∑' n : ℕ, phiTerm'' n u := by
  rw [PhiDD, (summable_phiTerm'' u).tsum_eq_zero_add, phiTerm''_zero_index, zero_add]

/--
@isnad1 id=eq.0h1v.s5.948f9a701b80 from=translated src=- shape=02d6fbc4 vocab=5b97a4a2
-/
theorem PhiDD_split (u : ℝ) :
    PhiDD u = phiTerm'' 1 u + phiTerm'' 2 u + ∑' n : ℕ, phiTerm'' (n + 3) u := by
  rw [PhiDD_eq_tsum, ← Summable.sum_add_tsum_nat_add 3 (summable_phiTerm'' u)]
  simp [Finset.sum_range_succ]

/--
@isnad1 id=le.2h1v.s6.0a85dcf2b455 from=translated src=- shape=2c91d3bc vocab=4d5c7bf9
-/
theorem tail_tsum_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 400) :
    |∑' n : ℕ, phiTerm'' (n + 3) u| ≤ 1.2 := by
  have hr0 : (0 : ℝ) ≤ Real.exp (-4) := (Real.exp_pos _).le
  have hrle : Real.exp (-4) ≤ 1 / 54 := exp_neg_four_le
  have hr1 : Real.exp (-4) < 1 := by linarith
  have hgeo : HasSum (fun n : ℕ => Real.exp (-4) ^ n) (1 - Real.exp (-4))⁻¹ :=
    hasSum_geometric_of_lt_one hr0 hr1
  have hg : HasSum (fun n : ℕ => 94208 * Real.exp (-4) ^ 3 * Real.exp (-4) ^ n)
      (94208 * Real.exp (-4) ^ 3 * (1 - Real.exp (-4))⁻¹) := hgeo.mul_left _
  have hbd : ∀ n : ℕ, ‖phiTerm'' (n + 3) u‖ ≤ 94208 * Real.exp (-4) ^ 3 * Real.exp (-4) ^ n := by
    intro n
    rw [Real.norm_eq_abs]
    have := phiTerm''_tail_le hu0 hu1 (m := n + 3) (by omega)
    calc |phiTerm'' (n + 3) u| ≤ 94208 * Real.exp (-4) ^ (n + 3) := this
      _ = 94208 * Real.exp (-4) ^ 3 * Real.exp (-4) ^ n := by rw [pow_add]; ring
  have hmain := tsum_of_norm_bounded hg hbd
  rw [Real.norm_eq_abs] at hmain
  refine hmain.trans ?_
  have hpos : (0 : ℝ) < 1 - Real.exp (-4) := by linarith
  have hinvpos : (0 : ℝ) < (1 - Real.exp (-4))⁻¹ := inv_pos.mpr hpos
  have hinv2 : (1 - Real.exp (-4))⁻¹ ≤ 2 := by
    have hlow : (1 : ℝ) / 2 ≤ 1 - Real.exp (-4) := by linarith
    have h := mul_le_mul_of_nonneg_left hlow hinvpos.le
    rw [inv_mul_cancel₀ hpos.ne'] at h
    linarith
  have hr3 : Real.exp (-4) ^ 3 ≤ (1 / 54 : ℝ) ^ 3 := pow_le_pow_left₀ hr0 hrle 3
  have hstep : Real.exp (-4) ^ 3 * (1 - Real.exp (-4))⁻¹ ≤ (1 / 54 : ℝ) ^ 3 * 2 :=
    mul_le_mul hr3 hinv2 hinvpos.le (by norm_num)
  nlinarith [hstep]

/--
@isnad1 id=lt.2h1v.s5.ca280079c6fe from=translated src=- shape=3b8719b6 vocab=572064c2
-/
theorem PhiDD_neg {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1 / 400) : PhiDD u < 0 := by
  have h1 := phiTerm''_one_le hu0 hu1
  have h2 := phiTerm''_two_le hu0 hu1
  have h3 := (le_abs_self (∑' n : ℕ, phiTerm'' (n + 3) u)).trans (tail_tsum_le hu0 hu1)
  rw [PhiDD_split]
  norm_num at h1 h2 h3 ⊢
  linarith

/-! ### Wintner's theorem down to the origin -/

/--
@isnad1 id=differen.0h0v.s5.46a421c69df5 from=translated src=- shape=aa9fb30a vocab=42a46360
-/
theorem differentiable_PhiD : Differentiable ℝ PhiD :=
  fun x => (hasDerivAt_PhiD x).differentiableAt

/--
@isnad1 id=strictan.0h0v.s5.7acb96fe5bc9 from=translated src=- shape=121de418 vocab=cb60145b
-/
theorem PhiD_strictAntiOn_Icc : StrictAntiOn PhiD (Icc 0 (1 / 400 : ℝ)) := by
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    differentiable_PhiD.continuous.continuousOn (fun x hx => ?_)
  rw [interior_Icc] at hx
  rw [(hasDerivAt_PhiD x).deriv]
  exact PhiDD_neg hx.1.le hx.2.le

/--
@isnad1 id=eq.0h0v.s3.ac83a8437bd4 from=translated src=- shape=3c26ae4f vocab=18a27210
-/
theorem PhiD_zero : PhiD 0 = 0 := by
  rw [PhiD_eq_deriv]; exact deriv_Phi_zero

/--
@isnad1 id=lt.1h1v.s4.a4f4bdf44957 from=translated src=- shape=3965f485 vocab=aa4671d7
-/
theorem PhiD_neg_of_pos {u : ℝ} (hu : 0 < u) : PhiD u < 0 := by
  rcases le_or_gt u (1 / 400 : ℝ) with h | h
  · have hmem0 : (0 : ℝ) ∈ Icc (0 : ℝ) (1 / 400) := ⟨le_refl 0, by norm_num⟩
    have hmemu : u ∈ Icc (0 : ℝ) (1 / 400) := ⟨hu.le, h⟩
    have := PhiD_strictAntiOn_Icc hmem0 hmemu hu
    rw [PhiD_zero] at this
    exact this
  · rw [PhiD_eq_deriv]
    exact deriv_Phi_neg le_pi_mul_exp_inv_four_hundred h.le

/-- **Wintner's monotonicity theorem, all the way to the origin.**

`Φ` is strictly decreasing on `[0, ∞)`.  `Wintner.lean` gets `[1/400, ∞)` termwise; the gap
`[0, 1/400]` is closed here by `Phi_even` (so `Φ'(0) = 0` exactly) together with `Φ'' < 0` on
that interval, which *is* a termwise estimate because the `n = 1` block of `Φ''` beats the rest
by a factor of six.
@isnad1 id=strictan.0h0v.s3.8f941b99c113 from=translated src=- shape=f2a09be3 vocab=18e0c317
-/
theorem Phi_strictAntiOn_Ici_zero : StrictAntiOn Phi (Ici (0 : ℝ)) := by
  refine strictAntiOn_of_deriv_neg (convex_Ici 0) continuous_Phi.continuousOn (fun x hx => ?_)
  rw [interior_Ici] at hx
  rw [← congrFun PhiD_eq_deriv x]
  exact PhiD_neg_of_pos hx

end XiLab

/-! ### Axiom audit -/
section AxiomAudit
end AxiomAudit

/-! ### Target signature, pinned verbatim -/
