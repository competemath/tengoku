/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Boundary.Comparison
public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Boundary.SingleCrossing
public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Boundary.ContinuousBoundaryProblem

/-!
# Initial single-interval geometry for the straight-line comparison

This formalizes the INITIAL shape argument in Step 4. It does not assert that
parabolic evolution preserves that shape, or initialize a zero count at positive
times. The initial difference formula is only identified with the American-price
difference where the expiry payoff is zero (`x>0`).

## Result

Public entry points include `slopeGap`, `slopeGap_differentiable`, `slopeGap_deriv_pos_at_zero`, `initialRatio_between_le_max`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary.Comparison

/-- The gap `logSlope f z - logSlope g z - 1` between the two logarithmic slopes. -/
noncomputable def slopeGap (f g : ℝ → ℝ) (z : ℝ) : ℝ :=
  logSlope f z - logSlope g z - 1

variable {k h α c : ℝ} {f g : ℝ → ℝ}

/--
@isnad1 id=differen.2h6v.s6.5991d0d6fc69 from=translated src=- shape=e0ff4604 vocab=8d9f6bfa
-/
theorem slopeGap_differentiable (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) : Differentiable ℝ (slopeGap f g) := by
  intro z
  exact (((logSlope_hasDeriv hf z).sub (logSlope_hasDeriv hg z)).sub_const 1).differentiableAt

/--
@isnad1 id=lt.5h7v.s7.1e7578a21d52 from=translated src=- shape=9cea2f8f vocab=530d3d4b
-/
theorem slopeGap_deriv_pos_at_zero (hα : α = k - h - 1) (hc : 0 < c)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g)
    (z : ℝ) (hz : slopeGap f g z = 0) : 0 < deriv (slopeGap f g) z := by
  unfold slopeGap
  rw [(slope_gap_crosses_up hα hf hg hz).deriv]
  exact hc

/--
@isnad1 id=le.6h9v.s7.9f7dc8aaa390 from=translated src=- shape=7a876984 vocab=d7b1fc4e
-/
theorem initialRatio_between_le_max (hα : α = k - h - 1) (hc : 0 < c)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g)
    {x y z : ℝ} (hxy : x ≤ y) (hyz : y ≤ z) :
    initialRatio f g y ≤ max (initialRatio f g x) (initialRatio f g z) :=
  value_between_le_max_of_upward_factor
    (fun x => (initialRatio_hasDeriv hf hg x).differentiableAt)
    (slopeGap_differentiable hf hg) (initialRatio_pos hf hg)
    (fun x => (initialRatio_hasDeriv hf hg x).deriv)
    (slopeGap_deriv_pos_at_zero hα hc hf hg) hxy hyz

/--
@isnad1 id=ordconne.4h7v.s6.1b52eb681857 from=translated src=- shape=7c3dd36d vocab=e6f7fe9f
-/
theorem initialRatio_sublevel_ordConnected (hα : α = k - h - 1) (hc : 0 < c)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g) (L : ℝ) :
    Set.OrdConnected {z | initialRatio f g z < L} := by
  rw [Set.ordConnected_iff]
  intro x hx z hz _ y hy
  exact (initialRatio_between_le_max hα hc hf hg hy.1 hy.2).trans_lt (max_lt hx hz)

/--
@isnad1 id=ne.5h7v.s7.91d48a67dd39 from=translated src=- shape=85dec2b1 vocab=09e51c11
-/
theorem initialRatio_simple_level (hα : α = k - h - 1) (hc : 0 < c)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g)
    {z : ℝ} (hlower : ∃ x, initialRatio f g x < initialRatio f g z) :
    deriv (initialRatio f g) z ≠ 0 :=
  deriv_ne_zero_of_exists_lower_of_upward_factor
    (fun x => (initialRatio_hasDeriv hf hg x).differentiableAt)
    (slopeGap_differentiable hf hg) (initialRatio_pos hf hg)
    (fun x => (initialRatio_hasDeriv hf hg x).deriv)
    (slopeGap_deriv_pos_at_zero hα hc hf hg) hlower

/--
@isnad1 id=false.8h9v.s7.ca1ab6767522 from=translated src=- shape=68999fb4 vocab=f21a11d0
-/
theorem initialRatio_no_three_equal (hα : α = k - h - 1) (hc : 0 < c)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g)
    {x y z : ℝ} (hxy : x < y) (hyz : y < z)
    (hexy : initialRatio f g x = initialRatio f g y)
    (heyz : initialRatio f g y = initialRatio f g z) : False :=
  no_three_equal_values_of_upward_factor
    (fun x => (initialRatio_hasDeriv hf hg x).differentiableAt)
    (slopeGap_differentiable hf hg) (initialRatio_pos hf hg)
    (fun x => (initialRatio_hasDeriv hf hg x).deriv)
    (slopeGap_deriv_pos_at_zero hα hc hf hg) hxy hyz hexy heyz

/-- Initial normalized difference on the zero-payoff side of the strike. -/
noncomputable def initialDifference (f g : ℝ → ℝ) (d x : ℝ) : ℝ :=
  -1 + Real.exp x * g (x - d) / f (x - d)

/--
@isnad1 id=eq.1h7v.s6.95ee8e026028 from=translated src=- shape=eaf9e4d3 vocab=a3d79ace
-/
theorem initialDifference_eq_price (hf : ProfileData (α - c) k f)
    (d x : ℝ) : initialDifference f g d x = (0 - price f g c d x 0) / f (x - d) := by
  simp only [initialDifference, price, mul_zero, add_zero, zero_sub]
  field_simp [(hf.pos (x - d)).ne']
  ring

/-- Equation (15) for the actual initial-difference function.
@isnad1 id=eq.1h7v.s6.0abab231791b from=translated src=- shape=0874c352 vocab=e03333e5
-/
theorem initialDifference_eq_ratio (hf : ProfileData (α - c) k f)
    (d x : ℝ) :
    initialDifference f g d x = -1 + Real.exp d / initialRatio f g (x - d) := by
  have he : Real.exp x = Real.exp d * Real.exp (x - d) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold initialDifference initialRatio
  rw [Real.exp_neg, he]
  field_simp [(hf.pos (x - d)).ne']

/--
@isnad1 id=iff.3h9v.s6.34ef909fcb5f from=translated src=- shape=27f4af1c vocab=d1c19aa0
-/
theorem initialDifference_level_iff (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) {ε : ℝ} (hε : -1 < ε) (d x : ℝ) :
    ε < initialDifference f g d x ↔ initialRatio f g (x - d) < Real.exp d / (ε + 1) := by
  rw [initialDifference_eq_ratio hf]
  have hR := initialRatio_pos hf hg (x - d)
  have hε' : 0 < ε + 1 := by linarith
  calc
    ε < -1 + Real.exp d / initialRatio f g (x - d) ↔
        ε + 1 < Real.exp d / initialRatio f g (x - d) := by constructor <;> intro h <;> linarith
    _ ↔ (ε + 1) * initialRatio f g (x - d) < Real.exp d := lt_div_iff₀ hR
    _ ↔ initialRatio f g (x - d) < Real.exp d / (ε + 1) := by
      rw [lt_div_iff₀ hε', mul_comm]

/--
@isnad1 id=iff.1h8v.s6.4a753f77814a from=translated src=- shape=90de4613 vocab=37589d59
-/
theorem initialDifference_eq_iff_ratio_eq (hf : ProfileData (α - c) k f) (d x y : ℝ) :
    initialDifference f g d x = initialDifference f g d y ↔
      initialRatio f g (x - d) = initialRatio f g (y - d) := by
  rw [initialDifference_eq_ratio hf, initialDifference_eq_ratio hf, add_right_inj,
    div_eq_mul_inv, div_eq_mul_inv, mul_right_inj' (Real.exp_pos d).ne', inv_inj]

/-- At every level the initial profile has at most two roots; the explicit
two-point cover excludes infinite zero sets as well.
@isnad1 id=ex.4h8v.s7.5784cc3061da from=translated src=- shape=482cce34 vocab=4a7c5a1b
-/
theorem initialDifference_level_subset_pair (hα : α = k - h - 1) (hc : 0 < c)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g) (d ε : ℝ) :
    ∃ a b : ℝ, {x | initialDifference f g d x = ε} ⊆ {a, b} := by
  apply subset_pair_of_no_ordered_triple
  intro x hx y hy z hz hxy hyz
  exact initialRatio_no_three_equal hα hc hf hg
    (sub_lt_sub_right hxy d) (sub_lt_sub_right hyz d)
    ((initialDifference_eq_iff_ratio_eq hf d x y).mp (hx.trans hy.symm))
    ((initialDifference_eq_iff_ratio_eq hf d y z).mp (hy.trans hz.symm))

/--
@isnad1 id=hasderiv.2h8v.s7.752f0801619b from=translated src=- shape=b57d11b0 vocab=5659073a
-/
theorem initialDifference_hasDeriv (hf : ProfileData (α - c) k f)
    (hg : ProfileData (α + 2 - c) h g) (d x : ℝ) :
    HasDerivAt (initialDifference f g d)
      (-Real.exp d * deriv (initialRatio f g) (x - d) / initialRatio f g (x - d) ^ 2) x := by
  rw [show initialDifference f g d = fun y => -1 + Real.exp d / initialRatio f g (y - d)
    from funext (initialDifference_eq_ratio hf d)]
  have hd := (initialRatio_hasDeriv hf hg (x - d)).differentiableAt.hasDerivAt
  have hv := ((hasDerivAt_const x (Real.exp d)).div
    (hd.comp x ((hasDerivAt_id x).sub_const d))
      (initialRatio_pos hf hg (x - d)).ne').const_add (-1)
  simp only [id_eq, mul_one, zero_mul, zero_sub, Function.comp_def] at hv
  convert! hv using 1
  ring

/-- Any level strictly below some initial value has only simple roots.
This is the noncritical-level fact needed for positive-time initialization.
@isnad1 id=ne.5h8v.s7.a3118df8f13f from=translated src=- shape=c6aed781 vocab=1e42875a
-/
theorem initialDifference_simple_level (hα : α = k - h - 1) (hc : 0 < c)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g)
    {d z : ℝ} (hhigher : ∃ x, initialDifference f g d z < initialDifference f g d x) :
    deriv (initialDifference f g d) z ≠ 0 := by
  obtain ⟨x, hx⟩ := hhigher
  rw [initialDifference_eq_ratio hf, initialDifference_eq_ratio hf] at hx
  have hratio : initialRatio f g (x - d) < initialRatio f g (z - d) :=
    (div_lt_div_iff_of_pos_left (Real.exp_pos d)
      (initialRatio_pos hf hg (z - d)) (initialRatio_pos hf hg (x - d))).mp (by linarith)
  have hn := initialRatio_simple_level hα hc hf hg ⟨x - d, hratio⟩
  rw [(initialDifference_hasDeriv hf hg d z).deriv]
  exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr (Real.exp_pos d).ne') hn)
    (pow_ne_zero _ (initialRatio_pos hf hg (z - d)).ne')

/-- The required initial superlevel set in `x>0` is an interval or empty.
`OrdConnected` includes empty sets and does not assume any zero-count theorem.
@isnad1 id=ordconne.5h8v.s7.b0a65a2497b7 from=translated src=- shape=76fe0988 vocab=21693acd
-/
theorem initialDifference_superlevel_ordConnected (hα : α = k - h - 1) (hc : 0 < c)
    (hf : ProfileData (α - c) k f) (hg : ProfileData (α + 2 - c) h g)
    {ε : ℝ} (hε : -1 < ε) (d : ℝ) :
    Set.OrdConnected {x | 0 < x ∧ ε < initialDifference f g d x} := by
  rw [Set.ordConnected_iff]
  intro x hx z hz _ y hy
  refine ⟨hx.1.trans_le hy.1, ?_⟩
  simp only [Set.mem_ofPred_eq] at hx hz
  rw [initialDifference_level_iff hf hg hε] at hx hz ⊢
  exact (initialRatio_between_le_max hα hc hf hg (sub_le_sub_right hy.1 d)
    (sub_le_sub_right hy.2 d)).trans_lt (max_lt hx.2 hz.2)

/-- Specialization to the fully explicit profiles: no ODE-profile assumptions
remain. The initial shape itself does not require `h<=k` or `d<0`.
@isnad1 id=ordconne.4h5v.s7.d3084eb210d5 from=translated src=- shape=fe218bc6 vocab=46e9314e
-/
theorem straight_initial_superlevel_ordConnected {k h c : ℝ}
    (hk : 0 < k) (hh : 0 ≤ h) (hc : 0 < c) {ε : ℝ} (hε : -1 < ε) (d : ℝ) :
    Set.OrdConnected {x | 0 < x ∧ ε < initialDifference
      (profile (k - h - 1 - c) k) (profile (k - h - 1 + 2 - c) h) d x} :=
  initialDifference_superlevel_ordConnected rfl hc (profile_data hk.le) (profile_data hh) hε d

/-- The actual normalized comparison difference at all prices and times. -/
noncomputable def normalizedDifference (p : ℝ → ℝ → ℝ) (f g : ℝ → ℝ)
    (c d x t : ℝ) : ℝ :=
  (p x t - price f g c d x t) / f (x + c * t - d)

/-- Identification is restricted to the zero-payoff half-line; no assertion
that the initial put payoff vanishes at negative log prices is made.
@isnad1 id=eq.3h10v.s6.79fd3062faad from=translated src=- shape=0e2cb957 vocab=9e23d9b1
-/
theorem normalizedDifference_initial {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b) (hf : ProfileData (α - c) k f)
    (d : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    normalizedDifference p f g c d x 0 = initialDifference f g d x := by
  have hp0 : p x 0 = 0 := by
    rw [hp.initial]
    exact max_eq_right (by have := Real.one_le_exp_iff.mpr hx; linarith)
  rw [initialDifference_eq_price hf]
  simp [normalizedDifference, hp0]

/--
@isnad1 id=ordconne.3h7v.s7.10aa6df2c4f8 from=translated src=- shape=3d8e6de3 vocab=3296232f
-/
theorem normalizedDifference_initial_superlevel {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : ContinuousBoundaryPutSolution k h p b) (hc : 0 < c) {ε : ℝ} (hε : -1 < ε) (d : ℝ) :
    Set.OrdConnected {x | 0 < x ∧ ε < normalizedDifference p
      (profile (k - h - 1 - c) k) (profile (k - h - 1 + 2 - c) h) c d x 0} := by
  convert straight_initial_superlevel_ordConnected hp.rate_pos hp.dividend_nonneg hc hε d using 1
  ext x
  by_cases hx : 0 < x
  · simp only [Set.mem_ofPred_eq, hx, true_and]
    rw [normalizedDifference_initial hp (profile_data hp.rate_pos.le) d hx.le]
  · simp [hx]

/-- Zero-dividend milestone stated directly using the existing CCJZ contract
and the constant second profile, not a different pricing-solution definition.
@isnad1 id=ordconne.3h6v.s6.f17eae922c5e from=translated src=- shape=fbe9dd41 vocab=c8ddb6a5
-/
theorem zeroDividend_initial_superlevel {p : ℝ → ℝ → ℝ} {b : ℝ → ℝ}
    (hp : NormalizedPutSolution k p b) (hc : 0 < c) {ε : ℝ} (hε : -1 < ε) (d : ℝ) :
    Set.OrdConnected {x | 0 < x ∧ ε < normalizedDifference p
      (profile (k - 1 - c) k) (fun _ => 1) c d x 0} := by
  simpa only [sub_zero, profile, ↓reduceIte] using
    normalizedDifference_initial_superlevel (dividendPutSolution_zero_iff.mpr hp).toContinuousBoundaryPutSolution hc hε d

end MathFin.BlackScholes.AmericanPut.Boundary.Comparison
