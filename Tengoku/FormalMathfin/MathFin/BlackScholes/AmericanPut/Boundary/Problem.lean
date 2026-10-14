/-
Copyright (c) 2026 Robert Martin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Martin
-/
module

public import Tengoku.FormalMathfin.MathFin.BlackScholes.AmericanPut.Boundary.Coordinates

/-!
# A classical normalized American-put problem

CCJZ (2008), (1.1), with the stopping-region extension and initial payoff on
ALL log prices. Arguments are always `(x, t)`, with `t` time remaining.
This is a solution predicate, not an existence or stochastic verification theorem.
No monotonicity, convexity, or curvature is included among its assumptions.

Interior derivatives are ordinary derivatives. At the moving boundary, smooth
fit is a right derivative and a right trace; no second derivative of the
payoff-extended price across the boundary is required. No smoothness at expiry
is imposed. The global-in-time formulation can be restricted to any maturity.

## Result

Public entry points include `normalizedRate`, `normalizedRate_pos`, `putPayoff`, `continuationRegion`.
-/

@[expose] public section

namespace MathFin.BlackScholes.AmericanPut.Boundary

open Filter
open scoped Topology ContDiff

/-- Positive-rate, zero-dividend Black--Scholes normalization. -/
noncomputable def normalizedRate (r σ : ℝ) : ℝ := 2 * r / σ ^ 2

/--
@isnad1 id=lt.2h2v.s5.4d089b4d4e58 from=translated src=- shape=6c67d60b vocab=a3903abf
-/
theorem normalizedRate_pos {r σ : ℝ} (hr : 0 < r) (hσ : 0 < σ) :
    0 < normalizedRate r σ := by
  unfold normalizedRate
  positivity

/-- Strike-normalized put payoff in log spot. -/
noncomputable def putPayoff (x : ℝ) : ℝ := max (1 - Real.exp x) 0

/-- Open continuation region; pairs are `(log spot, time remaining)`. -/
def continuationRegion (s : ℝ → ℝ) : Set (ℝ × ℝ) :=
  {z | 0 < z.2 ∧ s z.2 < z.1}

/-- The spatial Black--Scholes operator after normalization. -/
noncomputable def spatialOperator (k : ℝ) (f : ℝ → ℝ) (x : ℝ) : ℝ :=
  deriv (deriv f) x + (k - 1) * deriv f x - k * f x

/-- Analytic characterization to be connected to the GBM stopping value.
The smoothness requirements describe the intended classical solution class;
proving that the financial value belongs to it is a separate obligation. -/
structure NormalizedPutSolution (k : ℝ) (p : ℝ → ℝ → ℝ) (s : ℝ → ℝ) : Prop where
  rate_pos : 0 < k
  boundary_initial : s 0 = 0
  boundary_continuous : ContinuousOn s (Set.Ici 0)
  boundary_smooth : ContDiffOn ℝ ∞ s (Set.Ioi 0)
  price_continuous : ContinuousOn (fun z : ℝ × ℝ => p z.1 z.2) {z | 0 ≤ z.2}
  price_smooth : ContDiffOn ℝ ∞ (fun z : ℝ × ℝ => p z.1 z.2) (continuationRegion s)
  initial : ∀ x, p x 0 = putPayoff x
  dominates : ∀ x t, 0 ≤ t → putPayoff x ≤ p x t
  bounded : ∀ x t, 0 ≤ t → p x t ≤ 1
  exercise : ∀ x t, 0 < t → x ≤ s t → p x t = 1 - Real.exp x
  continuation : ∀ x t, 0 < t → s t < x → putPayoff x < p x t
  equation : ∀ x t, 0 < t → s t < x →
    deriv (p x) t = spatialOperator k (fun y => p y t) x
  smooth_fit : ∀ t, 0 < t → HasDerivWithinAt (fun x => p x t)
    (-Real.exp (s t)) (Set.Ici (s t)) (s t)
  gradient_trace : ∀ t, 0 < t →
    Tendsto (fun x => deriv (fun y => p y t) x)
      (nhdsWithin (s t) (Set.Ioi (s t))) (nhds (-Real.exp (s t)))
  decay : ∀ t, 0 ≤ t → Tendsto (fun x => p x t) atTop (nhds 0)

/--
@isnad1 id=le.0h1v.s3.da36b9658d29 from=translated src=- shape=8a62b088 vocab=fb31c446
-/
theorem putPayoff_nonneg (x : ℝ) : 0 ≤ putPayoff x := le_max_right _ _

/--
@isnad1 id=eq.1h1v.s5.5ebde39b23d4 from=translated src=- shape=8b803e2e vocab=08098cd7
-/
theorem putPayoff_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    putPayoff x = 1 - Real.exp x := by
  exact max_eq_left (sub_nonneg.mpr (Real.exp_le_one_iff.mpr hx))

/-- The normalized payoff is exactly the usual monetary put payoff.
@isnad1 id=eq.2h2v.s6.e25360211205 from=translated src=- shape=d2af98c5 vocab=d2f10345
-/
theorem putPayoff_in_stock_units {E S : ℝ} (hE : 0 < E) (hS : 0 < S) :
    E * putPayoff (Real.log (S / E)) = max (E - S) 0 := by
  unfold putPayoff
  rw [Real.exp_log (div_pos hS hE), mul_max_of_nonneg _ _ hE.le]
  congr 1
  · field_simp
  · ring

namespace NormalizedPutSolution

variable {k : ℝ} {p : ℝ → ℝ → ℝ} {s : ℝ → ℝ}

/-- The contact condition and nonnegative value force the threshold below strike.
@isnad1 id=le.2h4v.s5.7f610ee4ba15 from=translated src=- shape=1e0a9e63 vocab=7e1ed3da
-/
theorem boundary_nonpos (h : NormalizedPutSolution k p s) {t : ℝ} (ht : 0 < t) :
    s t ≤ 0 := by
  have hp := (putPayoff_nonneg (s t)).trans (h.dominates (s t) t ht.le)
  rw [h.exercise (s t) t ht le_rfl] at hp
  exact Real.exp_le_one_iff.mp (by linarith)

/-- Before expiry the contact set is exactly the lower half-line.
@isnad1 id=iff.2h5v.s5.490dfc685168 from=translated src=- shape=2f96dec5 vocab=09d0ff31
-/
theorem contact_iff (h : NormalizedPutSolution k p s) {x t : ℝ} (ht : 0 < t) :
    p x t = putPayoff x ↔ x ≤ s t := by
  constructor
  · intro heq
    by_contra hx
    have hlt := h.continuation x t ht (lt_of_not_ge hx)
    rw [heq] at hlt
    exact (lt_irrefl _ hlt)
  · intro hx
    rw [h.exercise x t ht hx, putPayoff_of_nonpos (hx.trans (h.boundary_nonpos ht))]

/-- In particular, the boundary is recoverable from the value function.
@isnad1 id=eq.2h4v.s5.09cc143ed5b2 from=translated src=- shape=f97052f1 vocab=49ba2c0c
-/
theorem contactSet (h : NormalizedPutSolution k p s) {t : ℝ} (ht : 0 < t) :
    {x | p x t = putPayoff x} = Set.Iic (s t) := by
  ext x
  exact h.contact_iff ht

/--
@isnad1 id=eq.2h4v.s5.7e97eb9be1eb from=translated src=- shape=b3917df8 vocab=1d7c5bef
-/
theorem boundary_eq_sSup_contact (h : NormalizedPutSolution k p s)
    {t : ℝ} (ht : 0 < t) : s t = sSup {x | p x t = putPayoff x} := by
  rw [h.contactSet ht, csSup_Iic]

/-- Uniqueness of the threshold for a FIXED price, not PDE uniqueness.
@isnad1 id=eq.3h5v.s5.2a9ed98fb865 from=translated src=- shape=1e0c3807 vocab=7ac289af
-/
theorem boundary_unique (h : NormalizedPutSolution k p s) {r : ℝ → ℝ}
    (hr : NormalizedPutSolution k p r) {t : ℝ} (ht : 0 ≤ t) : s t = r t := by
  rcases ht.eq_or_lt with ht | ht
  · subst t
    rw [h.boundary_initial, hr.boundary_initial]
  · rw [h.boundary_eq_sSup_contact ht, hr.boundary_eq_sSup_contact ht]

/-- At expiry the contact set is all of log-price space, unlike positive times.
@isnad1 id=eq.1h3v.s5.40ec8c17f6ca from=translated src=- shape=2a3b54c6 vocab=0962d1f8
-/
theorem contactSet_expiry (h : NormalizedPutSolution k p s) :
    {x | p x 0 = putPayoff x} = Set.univ := by
  ext x
  simp [h.initial]

/-- The reconstructed boundary is positive and does not exceed strike.
@isnad1 id=and.4h7v.s6.812c04fd9e3a from=translated src=- shape=826548fc vocab=e944d16d
-/
theorem stockBoundary_bounds (h : NormalizedPutSolution k p s)
    {E σ expiry T : ℝ} (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry) :
    0 < stockBoundary E σ expiry s T ∧ stockBoundary E σ expiry s T ≤ E := by
  constructor
  · exact mul_pos hE (Real.exp_pos _)
  · have hs := h.boundary_nonpos (normalizedTime_pos hσ hT)
    simpa [stockBoundary] using
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hs) hE.le

/-- Price/payoff coincidence expressed in the original positive stock variable.
@isnad1 id=iff.4h6v.s6.b5c5e7ae44e1 from=translated src=- shape=b578acd0 vocab=696546ee
-/
theorem contact_in_stock_units (h : NormalizedPutSolution k p s)
    {E S t : ℝ} (hE : 0 < E) (hS : 0 < S) (ht : 0 < t) :
    E * p (Real.log (S / E)) t = max (E - S) 0 ↔ S ≤ E * Real.exp (s t) := by
  rw [← putPayoff_in_stock_units hE hS, mul_right_inj' hE.ne', h.contact_iff ht]
  rw [← Real.exp_le_exp, Real.exp_log (div_pos hS hE), div_le_iff₀ hE]
  rw [mul_comm E]

/-- Regularity supplies actual derivatives, avoiding Lean's default derivative
value for a nondifferentiable function.
@isnad1 id=hasderiv.2h4v.s6.977571dc2025 from=translated src=- shape=ced25cbd vocab=7637e8a4
-/
theorem boundary_hasDerivAt (h : NormalizedPutSolution k p s) {t : ℝ} (ht : 0 < t) :
    HasDerivAt s (deriv s t) t :=
  ((h.boundary_smooth.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt
    (by simp)).hasDerivAt

/--
@isnad1 id=hasderiv.2h4v.s7.4a26dcab7bdd from=translated src=- shape=00a0eb80 vocab=7637e8a4
-/
theorem boundary_hasDerivAt_deriv (h : NormalizedPutSolution k p s)
    {t : ℝ} (ht : 0 < t) : HasDerivAt (deriv s) (deriv (deriv s) t) t := by
  have hs : ContDiffOn ℝ ∞ (deriv s) (Set.Ioi 0) :=
    h.boundary_smooth.deriv_of_isOpen isOpen_Ioi (by simp)
  exact ((hs.contDiffAt (isOpen_Ioi.mem_nhds ht)).differentiableAt (by simp)).hasDerivAt

/-- The remaining analytic curvature input suffices for the stock boundary.
This is a reduction lemma, not a proof of that input.
@isnad1 id=lt.5h7v.s7.1c715becd74a from=translated src=- shape=ed700c77 vocab=7eb73a3a
-/
theorem stock_curvature_of_log_curvature (h : NormalizedPutSolution k p s)
    {E σ expiry T : ℝ} (hE : 0 < E) (hσ : 0 < σ) (hT : T < expiry)
    (hcurvature : 0 < deriv (deriv s) (normalizedTime σ expiry T)) :
    0 < deriv (deriv (stockBoundary E σ expiry s)) T :=
  deriv2_stockBoundary_pos hE hσ hT (fun _ ht => h.boundary_hasDerivAt ht)
    (h.boundary_hasDerivAt_deriv (normalizedTime_pos hσ hT)) hcurvature

end NormalizedPutSolution

/-- OPEN analytic goal, deliberately a proposition definition and not a theorem.
Existence and stochastic identification must additionally be proved. -/
def NormalizedCurvatureClaim : Prop :=
  ∀ (k : ℝ) (p : ℝ → ℝ → ℝ) (s : ℝ → ℝ),
    NormalizedPutSolution k p s → ∀ t, 0 < t → 0 < deriv (deriv s) t

/-- OPEN non-vacuity obligation, separate from the conditional curvature claim. -/
def NormalizedExistenceClaim : Prop :=
  ∀ k : ℝ, 0 < k → ∃ p s, NormalizedPutSolution k p s

end MathFin.BlackScholes.AmericanPut.Boundary
