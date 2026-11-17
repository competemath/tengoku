/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.Seed.Algebra.Polynomial.Derivative
import Tengoku.Seed.Algebra.Polynomial.RingDivision
import Tengoku.Seed.Analysis.Complex.Polynomial.Basic
import Tengoku.Seed.Topology.Algebra.Polynomial
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.AntiHerglotz
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.LogDerivative
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.PoleProbe
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.RealZeros.Engine

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial logarithmic-derivative criteria

This module instantiates the local pole-exclusion argument for complex
polynomials and proves the exact zero-location characterization. For every
nonzero complex polynomial, the upper-half-plane sign condition is equivalent
to all roots lying in the closed lower half-plane. Under Schwarz symmetry this
specializes to an equivalence with real-rootedness.

## Main results

* `polynomial_antiHerglotz_iff_roots_closedLower` — the exact theorem without
  a symmetry assumption.
* `polynomial_logDeriv_sign_away_iff_roots_closedLower` — its punctured-domain
  form.
* `polynomial_antiHerglotz_iff_roots_real` — the Schwarz-symmetric
  real-rooted specialization.
-/

namespace OverflowResidueRH

open Complex

-- =====================================================================
-- Polynomial instantiation
-- =====================================================================

/-- **Polynomial logDeriv response (value form):** `Λ[p](z) = p'(z) / p(z)`.-/
noncomputable def polynomialLogDerivResponse (p : Polynomial ℂ) : ℂ → ℂ :=
  fun z => p.derivative.eval z / p.eval z

/-- Any polynomial supplying a `LocalLogDerivPoleDecomposition` at an upper
root has a positive imaginary escape.-/
theorem polynomial_local_pole_forces_escape
    (p : Polynomial ℂ) (ρ : ℂ)
    (D : LocalLogDerivPoleDecomposition (polynomialLogDerivResponse p) ρ) :
    PositiveUpperImaginaryEscape (polynomialLogDerivResponse p) :=
  positiveEscape_of_localLogDerivPole D

/-- **Polynomial pole-witness hypothesis (deferred Mathlib instantiation).**
For every upper-half-plane root `ρ` of `p` we have a
`LocalLogDerivPoleDecomposition` at `ρ`. The general construction of such
a decomposition from `p ≠ 0` and `p.eval ρ = 0` requires Mathlib's
polynomial root-multiplicity + bounded-continuity machinery and lives in
§8 / §9 below.-/
structure PolynomialPoleWitnessHypothesis (p : Polynomial ℂ) : Prop where
  decomp_at_each_upper_root :
    ∀ ρ : ℂ, p.eval ρ = 0 → 0 < ρ.im →
      Nonempty (LocalLogDerivPoleDecomposition
        (polynomialLogDerivResponse p) ρ)

/-- The polynomial pole-decomposition package implies the abstract
`LogDerivPoleWitnessLaw`.-/
theorem polynomial_logDeriv_poleWitness
    (p : Polynomial ℂ)
    (H : PolynomialPoleWitnessHypothesis p) :
    LogDerivPoleWitnessLaw
      (fun z => p.eval z)
      (polynomialLogDerivResponse p) where
  upper_zero_forces_escape := by
    intro ρ hroot hupper
    obtain ⟨D⟩ := H.decomp_at_each_upper_root ρ hroot hupper
    exact positiveEscape_of_localLogDerivPole D

/-- The logarithmic-derivative sign, the polynomial pole-witness package, and
conjugation symmetry imply that all roots of `p` are real.-/
theorem polynomial_roots_real_of_logDeriv_antiHerglotz_and_conjSymm
    (p : Polynomial ℂ)
    (H : PolynomialPoleWitnessHypothesis p)
    (hanti : AntiHerglotzUHP (polynomialLogDerivResponse p))
    (hsym : ∀ z : ℂ, p.eval (star z) = star (p.eval z)) :
    ∀ ρ : ℂ, p.eval ρ = 0 → ρ.im = 0 :=
  realZeros_of_antiHerglotz_logDerivative
    (polynomial_logDeriv_poleWitness p H) hanti hsym

-- =====================================================================
-- Discharging the polynomial pole-witness
-- =====================================================================

/-- The polynomial logarithmic-derivative background is continuous at any
non-root: `q'(z)/q(z)` is continuous at `ρ` whenever `q.eval ρ ≠ 0`.-/
theorem polynomial_logDeriv_background_continuousAt
    {q : Polynomial ℂ} {ρ : ℂ} (hqρ : q.eval ρ ≠ 0) :
    ContinuousAt (fun z => q.derivative.eval z / q.eval z) ρ := by
  apply ContinuousAt.div
  · exact (Polynomial.continuous q.derivative).continuousAt
  · exact (Polynomial.continuous q).continuousAt
  · exact hqρ

/-- The polynomial logarithmic-derivative background is bounded on a short
vertical probe by continuity at the base point.-/
theorem polynomial_logDeriv_background_bounded_on_probe
    {q : Polynomial ℂ} {ρ : ℂ}
    (hqρ : q.eval ρ ≠ 0)
    (hupper : 0 < ρ.im) :
    ∃ K : ℝ, 0 < K ∧
    ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 < ρ.im ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0 →
        |((q.derivative.eval (ρ - (ε : ℂ) * Complex.I)) /
           (q.eval (ρ - (ε : ℂ) * Complex.I))).im| ≤ K :=
  continuousAt_implies_probe_bounded
    (polynomial_logDeriv_background_continuousAt hqρ) hupper

/-- Polynomial factorization at a root using Mathlib's root multiplicity.
For `p ≠ 0` with `p.eval ρ = 0`, there exist `m > 0` and `q` such that
`p = (X − C ρ)^m · q` with `q.eval ρ ≠ 0`. Set `m := rootMultiplicity ρ p`;
positivity via `rootMultiplicity_pos`; factorization via
`pow_rootMultiplicity_dvd`; nonzero remainder by contradiction using
`dvd_iff_isRoot` + `mul_dvd_mul_left` + `pow_succ` +
`le_rootMultiplicity_iff`.-/
theorem polynomial_factor_at_root_with_nonzero_remainder
    {p : Polynomial ℂ} {ρ : ℂ}
    (hp : p ≠ 0)
    (hroot : p.eval ρ = 0) :
    ∃ m : ℕ, 0 < m ∧
    ∃ q : Polynomial ℂ,
      p = (Polynomial.X - Polynomial.C ρ)^m * q ∧
      q.eval ρ ≠ 0 := by
  set m := p.rootMultiplicity ρ with hm_def
  have hm_pos : 0 < m := by
    rw [hm_def]
    exact (Polynomial.rootMultiplicity_pos hp).mpr hroot
  obtain ⟨q, hq_eq⟩ : (Polynomial.X - Polynomial.C ρ)^m ∣ p :=
    Polynomial.pow_rootMultiplicity_dvd p ρ
  refine ⟨m, hm_pos, q, hq_eq, ?_⟩
  -- if q.eval ρ = 0, then (X - C ρ) ∣ q, so (X - C ρ)^(m+1) ∣ p,
  -- contradicting maximality of m
  intro hq_eval
  have h_dvd_q : (Polynomial.X - Polynomial.C ρ) ∣ q :=
    Polynomial.dvd_iff_isRoot.mpr hq_eval
  have h_succ_dvd : (Polynomial.X - Polynomial.C ρ)^(m+1) ∣ p := by
    rw [hq_eq, pow_succ]
    exact mul_dvd_mul_left _ h_dvd_q
  have h_le := (Polynomial.le_rootMultiplicity_iff hp).mpr h_succ_dvd
  rw [← hm_def] at h_le
  omega

-- =====================================================================
-- Value-to-polynomial logarithmic-derivative bridge
-- =====================================================================

/-- Polynomial value-form pole decomposition lifted to the logarithmic
derivative response: if
`p = (X − C ρ)^(k+1) · q` with `z ≠ ρ` and `q(z) ≠ 0`, then
`p'(z)/p(z) = (k+1)/(z−ρ) + q'(z)/q(z)`. Reduces to the value-form
`complex_local_pole_decomposition_general` after evaluating `eval` of
the factorization and its derivative.-/
theorem polynomial_logDeriv_local_decomposition_of_factor
    {p q : Polynomial ℂ} {ρ z : ℂ} {k : ℕ}
    (hfac : p = (Polynomial.X - Polynomial.C ρ) ^ (k + 1) * q)
    (hzρ : z ≠ ρ)
    (hqz : q.eval z ≠ 0) :
    polynomialLogDerivResponse p z =
      (((k + 1 : ℕ) : ℂ) / (z - ρ))
        + q.derivative.eval z / q.eval z := by
  unfold polynomialLogDerivResponse
  -- p.eval z = (z − ρ)^(k+1) * q.eval z
  have hp_eval : p.eval z = (z - ρ)^(k+1) * q.eval z := by
    rw [hfac]
    simp [Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  -- p'.eval z = (k+1) * (z − ρ)^k * q.eval z + (z − ρ)^(k+1) * q'.eval z
  have hp_deriv_eval : p.derivative.eval z
                    = ((k + 1 : ℕ) : ℂ) * (z - ρ)^k * q.eval z
                      + (z - ρ)^(k+1) * q.derivative.eval z := by
    rw [hfac, Polynomial.derivative_mul, Polynomial.derivative_pow_succ]
    simp [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
          Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C,
          Polynomial.derivative_sub, Polynomial.derivative_X,
          Polynomial.derivative_C]
  rw [hp_eval, hp_deriv_eval]
  exact complex_local_pole_decomposition_general z ρ (q.eval z)
          (q.derivative.eval z) k hzρ hqz

/-- Build `LocalLogDerivPoleDecomposition` from polynomial factorization
data. This combines:

  • probe ≠ pole (`probe_ne_pole`),
  • a polynomial background continuous and nonzero on the probe,
  • the value→polynomial bridge above.-/
noncomputable def localLogDerivPoleDecomposition_of_polynomial_factor
    {p q : Polynomial ℂ} {ρ : ℂ} {k : ℕ}
    (hupper : 0 < ρ.im)
    (hfac : p = (Polynomial.X - Polynomial.C ρ) ^ (k + 1) * q)
    (hqρ : q.eval ρ ≠ 0) :
    LocalLogDerivPoleDecomposition (polynomialLogDerivResponse p) ρ :=
  -- Background continuity:
  let hcontB := polynomial_logDeriv_background_continuousAt hqρ
  let hcontQ : ContinuousAt (fun z => q.eval z) ρ :=
    (Polynomial.continuous q).continuousAt
  -- From continuity helpers, get bounded background and nonzero q on probe:
  let hboundedB : ∃ K : ℝ, 0 < K ∧
      ∃ ε0 : ℝ, 0 < ε0 ∧ ε0 < ρ.im ∧
        ∀ ε : ℝ, 0 < ε → ε < ε0 →
          |((q.derivative.eval (ρ - (ε : ℂ) * Complex.I)) /
             (q.eval (ρ - (ε : ℂ) * Complex.I))).im| ≤ K :=
    continuousAt_implies_probe_bounded hcontB hupper
  let hnzQ : ∃ ε0' : ℝ, 0 < ε0' ∧ ε0' < ρ.im ∧
      ∀ ε : ℝ, 0 < ε → ε < ε0' →
        q.eval (ρ - (ε : ℂ) * Complex.I) ≠ 0 :=
    continuousAt_implies_probe_nonzero hcontQ hqρ hupper
  -- Extract and combine
  let K := hboundedB.choose
  let hK := hboundedB.choose_spec
  let ε0B := hK.2.choose
  let hε0B := hK.2.choose_spec
  let ε0Q := hnzQ.choose
  let hε0Q := hnzQ.choose_spec
  let ε0 := min ε0B ε0Q
  { m := k + 1
    hm_pos := Nat.succ_pos k
    background := fun z => q.derivative.eval z / q.eval z
    ε0 := ε0
    hε0 := lt_min hε0B.1 hε0Q.1
    hε0_lt := lt_of_le_of_lt (min_le_left _ _) hε0B.2.1
    K := K
    hK_pos := hK.1
    decomp_at_probe := fun ε hε_pos hε_lt => by
      have hε_lt_B : ε < ε0B :=
        lt_of_lt_of_le hε_lt (min_le_left _ _)
      have hε_lt_Q : ε < ε0Q :=
        lt_of_lt_of_le hε_lt (min_le_right _ _)
      have hzρ : ρ - (ε : ℂ) * Complex.I ≠ ρ := probe_ne_pole ρ ε hε_pos
      have hqz : q.eval (ρ - (ε : ℂ) * Complex.I) ≠ 0 :=
        hε0Q.2.2 ε hε_pos hε_lt_Q
      have h := polynomial_logDeriv_local_decomposition_of_factor
        hfac hzρ hqz
      convert h using 2
      norm_num
    background_bounded := fun ε hε_pos hε_lt => by
      have hε_lt_B : ε < ε0B :=
        lt_of_lt_of_le hε_lt (min_le_left _ _)
      exact hε0B.2.2 ε hε_pos hε_lt_B }

/-- For any nonzero polynomial `p`, the
hypothesis package `PolynomialPoleWitnessHypothesis p` follows from
root-multiplicity factorization and the local pole decomposition.-/
theorem polynomialPoleWitnessHypothesis_of_nonzero_polynomial
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    PolynomialPoleWitnessHypothesis p := by
  constructor
  intro ρ hroot hupper
  obtain ⟨m, hm, q, hfac, hqρ⟩ :=
    polynomial_factor_at_root_with_nonzero_remainder hp hroot
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 :=
    ⟨m - 1, by omega⟩
  exact ⟨localLogDerivPoleDecomposition_of_polynomial_factor
    hupper hfac hqρ⟩

/-- For any nonzero polynomial `p`, the logarithmic-derivative sign condition
and conjugation symmetry imply that all roots are real.-/
theorem polynomial_roots_real_of_logDeriv_antiHerglotz_and_conjSymm'
    (p : Polynomial ℂ) (hp : p ≠ 0)
    (hanti : AntiHerglotzUHP (polynomialLogDerivResponse p))
    (hsym : ∀ z : ℂ, p.eval (star z) = star (p.eval z)) :
    ∀ ρ : ℂ, p.eval ρ = 0 → ρ.im = 0 :=
  polynomial_roots_real_of_logDeriv_antiHerglotz_and_conjSymm
    p (polynomialPoleWitnessHypothesis_of_nonzero_polynomial p hp)
    hanti hsym

-- =====================================================================
-- Exact zero-location characterization without symmetry
-- =====================================================================

/-- A pole in the closed lower half-plane contributes a nonpositive
imaginary part to its Cauchy kernel throughout the upper half-plane.-/
theorem lowerHalfPlane_residue_imag_nonpos
    (z rho : ℂ) (hz : 0 < z.im) (hrho : rho.im ≤ 0) :
    ((1 : ℂ) / (z - rho)).im ≤ 0 := by
  have hne : z - rho ≠ 0 := by
    intro h
    have him : (z - rho).im = 0 := by rw [h]; rfl
    rw [Complex.sub_im] at him
    linarith
  rw [one_div, Complex.inv_im, Complex.sub_im]
  have hnorm : 0 < Complex.normSq (z - rho) := Complex.normSq_pos.mpr hne
  exact le_of_lt (div_neg_of_neg_of_pos (by linarith) hnorm)

/-- A pole in the closed lower half-plane contributes a strictly negative
imaginary part throughout the open upper half-plane.-/
theorem lowerHalfPlane_residue_imag_neg
    (z rho : ℂ) (hz : 0 < z.im) (hrho : rho.im ≤ 0) :
    ((1 : ℂ) / (z - rho)).im < 0 := by
  have hne : z - rho ≠ 0 := by
    intro h
    have him : (z - rho).im = 0 := by rw [h]; rfl
    rw [Complex.sub_im] at him
    linarith
  rw [one_div, Complex.inv_im, Complex.sub_im]
  have hnorm : 0 < Complex.normSq (z - rho) := Complex.normSq_pos.mpr hne
  exact div_neg_of_neg_of_pos (by linarith) hnorm

/-- A finite residue cloud supported in the closed lower half-plane has
nonpositive imaginary part on the upper half-plane.-/
theorem lowerHalfPlane_residue_cloud_antiHerglotz_multiset
    (roots : Multiset ℂ)
    (hroots : ∀ rho ∈ roots, rho.im ≤ 0) :
    AntiHerglotzUHP
      (fun z : ℂ => (roots.map fun rho : ℂ => (1 : ℂ) / (z - rho)).sum) := by
  revert hroots
  induction roots using Multiset.induction_on with
  | empty =>
      intro _ z _
      simp
  | @cons rho roots ih =>
      intro hroots z hz
      have hrho : rho.im ≤ 0 := hroots rho (by simp)
      have htail : ∀ sigma ∈ roots, sigma.im ≤ 0 := by
        intro sigma hsigma
        exact hroots sigma (by simp [hsigma])
      have hhead := lowerHalfPlane_residue_imag_nonpos z rho hz hrho
      have hrest := ih htail z hz
      simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
      exact add_nonpos hhead hrest

/-- A nonempty finite residue cloud supported in the closed lower half-plane
has strictly negative imaginary part on the upper half-plane.-/
theorem lowerHalfPlane_residue_cloud_strictAntiHerglotz_multiset
    (roots : Multiset ℂ) (hne : roots ≠ 0)
    (hroots : ∀ rho ∈ roots, rho.im ≤ 0) :
    StrictAntiHerglotzUHP
      (fun z : ℂ => (roots.map fun rho : ℂ => (1 : ℂ) / (z - rho)).sum) := by
  intro z hz
  induction roots using Multiset.induction_on with
  | empty => exact (hne rfl).elim
  | @cons rho roots _ih =>
      have hrho : rho.im ≤ 0 := hroots rho (by simp)
      have htail : ∀ sigma ∈ roots, sigma.im ≤ 0 := by
        intro sigma hsigma
        exact hroots sigma (by simp [hsigma])
      have hhead := lowerHalfPlane_residue_imag_neg z rho hz hrho
      have hrest := lowerHalfPlane_residue_cloud_antiHerglotz_multiset
        roots htail z hz
      simp only [Multiset.map_cons, Multiset.sum_cons, Complex.add_im]
      linarith

/-- For a nonzero complex polynomial, the upper-half-plane sign condition on
its logarithmic derivative is equivalent to all roots lying in the closed
lower half-plane. No conjugation symmetry is required.-/
theorem polynomial_antiHerglotz_iff_roots_closedLower
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    AntiHerglotzUHP (polynomialLogDerivResponse p) ↔
      ∀ rho : ℂ, p.eval rho = 0 → rho.im ≤ 0 := by
  constructor
  · intro hsign rho hroot
    apply le_of_not_gt
    intro hupper
    have hnonzero := antiHerglotz_forbids_upper_zeros
      (polynomial_logDeriv_poleWitness p
        (polynomialPoleWitnessHypothesis_of_nonzero_polynomial p hp))
      hsign rho hupper
    exact hnonzero hroot
  · intro hroots z hz
    by_cases hpz : p.eval z = 0
    · unfold polynomialLogDerivResponse
      rw [hpz, div_zero, Complex.zero_im]
    · unfold polynomialLogDerivResponse
      rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpz]
      exact lowerHalfPlane_residue_cloud_antiHerglotz_multiset p.roots
        (fun rho hrho => hroots rho ((Polynomial.mem_roots hp).mp hrho)) z hz

/-- For a nonzero complex polynomial, strict anti-Herglotz behavior of its
logarithmic derivative is equivalent to positive degree together with every
root lying in the closed lower half-plane. The degree hypothesis is necessary:
the logarithmic derivative of a nonzero constant polynomial is zero.-/
theorem polynomial_strictAntiHerglotz_iff_roots_closedLower
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    StrictAntiHerglotzUHP (polynomialLogDerivResponse p) ↔
      0 < p.natDegree ∧
        ∀ rho : ℂ, p.eval rho = 0 → rho.im ≤ 0 := by
  constructor
  · intro hsign
    refine ⟨?_, (polynomial_antiHerglotz_iff_roots_closedLower p hp).mp
      hsign.antiHerglotz⟩
    by_contra hdegree
    have hdegree_zero : p.natDegree = 0 := Nat.eq_zero_of_not_pos hdegree
    have hI := hsign Complex.I (by simp)
    rw [Polynomial.eq_C_of_natDegree_eq_zero hdegree_zero] at hI
    simp [polynomialLogDerivResponse] at hI
  · rintro ⟨hdegree, hroots⟩ z hz
    have hpz : p.eval z ≠ 0 := by
      intro hpz
      have := hroots z hpz
      linarith
    unfold polynomialLogDerivResponse
    rw [(IsAlgClosed.splits p).eval_derivative_div_eval_of_ne_zero hpz]
    exact lowerHalfPlane_residue_cloud_strictAntiHerglotz_multiset
      p.roots
      ((IsAlgClosed.splits p).roots_ne_zero (Nat.ne_of_gt hdegree))
      (fun rho hrho => hroots rho ((Polynomial.mem_roots hp).mp hrho)) z hz

/-- Punctured-domain version of
`polynomial_antiHerglotz_iff_roots_closedLower`. This is the mathematically
natural public statement: the logarithmic derivative is only constrained
where its denominator is nonzero.-/
theorem polynomial_logDeriv_sign_away_iff_roots_closedLower
    (p : Polynomial ℂ) (hp : p ≠ 0) :
    (∀ z : ℂ, 0 < z.im → p.eval z ≠ 0 →
        (polynomialLogDerivResponse p z).im ≤ 0) ↔
      ∀ rho : ℂ, p.eval rho = 0 → rho.im ≤ 0 := by
  constructor
  · intro hsign
    apply (polynomial_antiHerglotz_iff_roots_closedLower p hp).mp
    intro z hz
    by_cases hpz : p.eval z = 0
    · unfold polynomialLogDerivResponse
      rw [hpz, div_zero, Complex.zero_im]
    · exact hsign z hz hpz
  · intro hroots z hz _hpz
    exact (polynomial_antiHerglotz_iff_roots_closedLower p hp).mpr
      hroots z hz

-- =====================================================================
-- Polynomial converse from a real linear factorization
-- =====================================================================

/-- **Real linear factorization data for a polynomial.** Witnesses that
`p` factors over ℂ as `C c · ∏_i (X − C r_i)` with `c ≠ 0` and real
roots `r_i` (counted with multiplicity by repetition in the list).-/
structure PolynomialRealLinearFactorization (p : Polynomial ℂ) where
  c : ℂ
  hc : c ≠ 0
  roots : List ℝ
  factorization :
    p =
      Polynomial.C c *
        (roots.map fun r : ℝ =>
          Polynomial.X - Polynomial.C ((r : ℝ) : ℂ)).prod

/-- A nonzero complex polynomial all of whose roots are real admits the real
linear factorization used by the logarithmic-derivative calculation below.

This is the fundamental-theorem-of-algebra discharge that was missing from
the previous factorized polynomial statement.-/
noncomputable def PolynomialRealLinearFactorization.of_roots_real
    (p : Polynomial ℂ) (hp : p ≠ 0)
    (hreal : ∀ ρ : ℂ, p.eval ρ = 0 → ρ.im = 0) :
    PolynomialRealLinearFactorization p := by
  classical
  refine
    { c := p.leadingCoeff
      hc := Polynomial.leadingCoeff_ne_zero.mpr hp
      roots := p.roots.toList.map Complex.re
      factorization := ?_ }
  have hfac :
      Polynomial.C p.leadingCoeff *
          (p.roots.map fun ρ : ℂ => Polynomial.X - Polynomial.C ρ).prod = p :=
    Polynomial.C_leadingCoeff_mul_prod_multiset_X_sub_C
      IsAlgClosed.card_roots_eq_natDegree
  have hmap :
      (p.roots.toList.map fun ρ : ℂ =>
          Polynomial.X - Polynomial.C (((ρ.re : ℝ) : ℂ))) =
        p.roots.toList.map fun ρ : ℂ =>
          Polynomial.X - Polynomial.C ρ := by
    apply List.map_congr_left
    intro ρ hρ
    have hroot : p.eval ρ = 0 :=
      (Polynomial.mem_roots hp).mp (Multiset.mem_toList.mp hρ)
    have hρ_real : (((ρ.re : ℝ) : ℂ)) = ρ := by
      apply Complex.ext
      · simp
      · simp [hreal ρ hroot]
    rw [hρ_real]
  have hcoe :
      ((p.roots.toList.map
          (fun ρ : ℂ => Polynomial.X - Polynomial.C ρ) :
          List (Polynomial ℂ)) : Multiset (Polynomial ℂ)) =
        p.roots.map fun ρ : ℂ => Polynomial.X - Polynomial.C ρ := by
    change
      Multiset.map (fun ρ : ℂ => Polynomial.X - Polynomial.C ρ)
          (p.roots.toList : Multiset ℂ) =
        Multiset.map (fun ρ : ℂ => Polynomial.X - Polynomial.C ρ) p.roots
    rw [Multiset.coe_toList]
  have hprod :
      ((p.roots.toList.map Complex.re).map fun r : ℝ =>
          Polynomial.X - Polynomial.C ((r : ℝ) : ℂ)).prod =
        (p.roots.map fun ρ : ℂ =>
          Polynomial.X - Polynomial.C ρ).prod := by
    rw [List.map_map]
    change
      (p.roots.toList.map fun ρ : ℂ =>
          Polynomial.X - Polynomial.C (((ρ.re : ℝ) : ℂ))).prod =
        (p.roots.map fun ρ : ℂ =>
          Polynomial.X - Polynomial.C ρ).prod
    rw [hmap]
    exact congrArg Multiset.prod hcoe
  calc
    p = Polynomial.C p.leadingCoeff *
        (p.roots.map fun ρ : ℂ =>
          Polynomial.X - Polynomial.C ρ).prod := hfac.symm
    _ = Polynomial.C p.leadingCoeff *
        ((p.roots.toList.map Complex.re).map fun r : ℝ =>
          Polynomial.X - Polynomial.C ((r : ℝ) : ℂ)).prod := by
      rw [hprod]

/-- Evaluation of a real linear product.-/
private theorem prodLinearReal_eval
    (roots : List ℝ) (z : ℂ) :
    (roots.map fun r : ℝ => Polynomial.X - Polynomial.C ((r : ℝ) : ℂ)).prod.eval z
      = (roots.map fun r : ℝ => z - (r : ℂ)).prod := by
  induction roots with
  | nil => simp
  | cons r rs ih =>
    simp [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_X,
          Polynomial.eval_C, ih]

/-- A real linear product is nonzero at a point distinct from
all roots.**-/
private theorem prodLinearReal_eval_ne_zero
    (roots : List ℝ) {z : ℂ} (hz : ∀ r ∈ roots, z ≠ (r : ℂ)) :
    (roots.map fun r : ℝ => Polynomial.X - Polynomial.C ((r : ℝ) : ℂ)).prod.eval z
      ≠ 0 := by
  rw [prodLinearReal_eval]
  induction roots with
  | nil => simp
  | cons r rs ih =>
    have h_head : z ≠ (r : ℂ) := hz r (List.mem_cons_self ..)
    have h_tail : ∀ s ∈ rs, z ≠ (s : ℂ) :=
      fun s hs => hz s (List.mem_cons_of_mem _ hs)
    have h_rest := ih h_tail
    simp only [List.map_cons, List.prod_cons]
    exact mul_ne_zero (sub_ne_zero.mpr h_head) h_rest

/-- The logarithmic derivative of a real linear product equals the cloud
sum.** Induction on the list of roots, using the product rule
  `(p · q)' = p' · q + p · q'`
to split each factor.

At each step we have `((X − C r) · q)' / ((X − C r) · q) = 1/(z − r) +
q'/q` (this is `complex_local_pole_decomposition_simple_root` instantiated
on values). Iterating gives the residue cloud.-/
theorem polynomialLogDeriv_of_linearProd_eq_cloud
    (roots : List ℝ) (z : ℂ)
    (hz : ∀ r ∈ roots, z ≠ (r : ℂ)) :
    polynomialLogDerivResponse
        (roots.map fun r : ℝ => Polynomial.X - Polynomial.C ((r : ℝ) : ℂ)).prod z
      = (roots.map fun r : ℝ => (1 : ℂ) / (z - (r : ℂ))).sum := by
  induction roots with
  | nil =>
    -- empty product = 1; derivative = 0; cloud = 0
    simp [polynomialLogDerivResponse]
  | cons r rs ih =>
    have h_head : z ≠ (r : ℂ) := hz r (List.mem_cons_self ..)
    have h_tail : ∀ s ∈ rs, z ≠ (s : ℂ) :=
      fun s hs => hz s (List.mem_cons_of_mem _ hs)
    have h_rest := ih h_tail
    -- Names for the factors.
    set q : Polynomial ℂ :=
      (rs.map fun r : ℝ => Polynomial.X - Polynomial.C ((r : ℝ) : ℂ)).prod
      with hq_def
    have hq_eval : q.eval z ≠ 0 :=
      prodLinearReal_eval_ne_zero rs h_tail
    -- p = (X - C r) * q.  Compute p.eval and p'.eval.
    have h_p_eval :
        ((List.map (fun r : ℝ => Polynomial.X - Polynomial.C ((r : ℝ) : ℂ))
              (r :: rs)).prod).eval z
          = (z - (r : ℂ)) * q.eval z := by
      simp [hq_def, Polynomial.eval_mul, Polynomial.eval_sub,
            Polynomial.eval_X, Polynomial.eval_C]
    have h_p_deriv_eval :
        (((List.map (fun r : ℝ => Polynomial.X - Polynomial.C ((r : ℝ) : ℂ))
              (r :: rs)).prod).derivative).eval z
          = q.eval z + (z - (r : ℂ)) * q.derivative.eval z := by
      simp [hq_def, Polynomial.derivative_mul, Polynomial.derivative_sub,
            Polynomial.derivative_X, Polynomial.derivative_C,
            Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_sub,
            Polynomial.eval_X, Polynomial.eval_C]
    have hr_ne : z - (r : ℂ) ≠ 0 := sub_ne_zero.mpr h_head
    -- Compute the cloud equality directly.
    change polynomialLogDerivResponse
            (List.map (fun r : ℝ => Polynomial.X - Polynomial.C ((r : ℝ) : ℂ))
              (r :: rs)).prod z
          = (List.map (fun r : ℝ => (1 : ℂ) / (z - (r : ℂ))) (r :: rs)).sum
    unfold polynomialLogDerivResponse
    rw [h_p_eval, h_p_deriv_eval]
    have h_alg :
        (q.eval z + (z - (r : ℂ)) * q.derivative.eval z) /
          ((z - (r : ℂ)) * q.eval z)
          = 1 / (z - (r : ℂ)) + q.derivative.eval z / q.eval z := by
      field_simp
    rw [h_alg, List.map_cons, List.sum_cons]
    -- Cancel matching first term, leaving `q'/q = (rs.map …).sum`, which
    -- is `h_rest` (defeq through `polynomialLogDerivResponse`).
    have h_rest' : q.derivative.eval z / q.eval z
                  = (List.map (fun r : ℝ => (1 : ℂ) / (z - (r : ℂ))) rs).sum :=
      h_rest
    rw [h_rest']

/-- The logarithmic derivative is invariant under nonzero constant
multiplication.** `Λ[C c · q](z) = Λ[q](z)` when `q.eval z ≠ 0` and
`c ≠ 0`.-/
private theorem polynomialLogDeriv_C_mul
    (c : ℂ) (hc : c ≠ 0) (q : Polynomial ℂ) (z : ℂ) (hq : q.eval z ≠ 0) :
    polynomialLogDerivResponse (Polynomial.C c * q) z
      = polynomialLogDerivResponse q z := by
  unfold polynomialLogDerivResponse
  have h_eval : (Polynomial.C c * q).eval z = c * q.eval z := by
    simp [Polynomial.eval_mul, Polynomial.eval_C]
  have h_deriv :
      ((Polynomial.C c * q).derivative).eval z = c * q.derivative.eval z := by
    simp [Polynomial.derivative_mul, Polynomial.derivative_C,
          Polynomial.eval_mul, Polynomial.eval_C]
  rw [h_eval, h_deriv]
  field_simp

/-- A real linear product evaluates to zero at any root.-/
private theorem prodLinearReal_eval_zero_of_mem
    (roots : List ℝ) {z : ℂ} {r : ℝ}
    (hr : r ∈ roots) (hz : z = (r : ℂ)) :
    (roots.map fun s : ℝ => Polynomial.X - Polynomial.C ((s : ℝ) : ℂ)).prod.eval z
      = 0 := by
  rw [prodLinearReal_eval]
  induction roots with
  | nil => exact absurd hr (List.not_mem_nil)
  | cons s rs ih =>
    simp only [List.map_cons, List.prod_cons]
    rcases List.mem_cons.mp hr with rfl | hr_tail
    · simp [hz]
    · rw [ih hr_tail]; ring

/-- The logarithmic derivative of a real-linearly-factorized polynomial
equals the real residue cloud at any non-root.**-/
theorem polynomialLogDeriv_eq_real_residue_cloud_of_factorization
    {p : Polynomial ℂ}
    (F : PolynomialRealLinearFactorization p)
    (z : ℂ) (hz : p.eval z ≠ 0) :
    polynomialLogDerivResponse p z =
      (F.roots.map fun r : ℝ => (1 : ℂ) / (z - (r : ℂ))).sum := by
  -- Use an isolated `congrArg` for the rewrite to dodge motive issues
  -- (the goal contains `F.roots`, and naive `rw [F.factorization]` tries
  -- to rewrite `p` in `F`'s implicit type as well).
  set q : Polynomial ℂ :=
    (F.roots.map fun r : ℝ => Polynomial.X - Polynomial.C ((r : ℝ) : ℂ)).prod
    with hq_def
  -- 1. Recover `∀ r ∈ F.roots, z ≠ (r : ℂ)` from `hz`.
  have h_z_ne : ∀ r ∈ F.roots, z ≠ (r : ℂ) := by
    intro r hr hz_eq
    apply hz
    have hp_eval : p.eval z = F.c * q.eval z := by
      have h := congrArg (Polynomial.eval z) F.factorization
      rw [h, Polynomial.eval_mul, Polynomial.eval_C]
    rw [hp_eval, prodLinearReal_eval_zero_of_mem F.roots hr hz_eq, mul_zero]
  -- 2. Express LHS via the factorization, isolated as a single congrArg.
  have h_q_eval : q.eval z ≠ 0 :=
    prodLinearReal_eval_ne_zero F.roots h_z_ne
  have hp_lhs :
      polynomialLogDerivResponse p z
        = polynomialLogDerivResponse (Polynomial.C F.c * q) z :=
    congrArg (fun r => polynomialLogDerivResponse r z) F.factorization
  rw [hp_lhs, polynomialLogDeriv_C_mul F.c F.hc q z h_q_eval]
  -- 3. Apply the linear-product cloud identity.
  exact polynomialLogDeriv_of_linearProd_eq_cloud F.roots z h_z_ne

/-- A real-linearly-factorized polynomial satisfies the sign condition.
The converse of `polynomial_roots_real_of_logDeriv_antiHerglotz_and_conjSymm'`
in the factorized form. At a non-root we reduce `Λ[p]` to the real
residue cloud and apply §2's `real_residue_cloud_antiHerglotz_list`. At
zeros, Lean's totalized `0 / 0 = 0` makes the inequality vacuous
(§6-bis `antiHerglotz_at_zero_is_vacuous`).-/
theorem polynomial_antiHerglotz_of_realLinearFactorization
    {p : Polynomial ℂ}
    (F : PolynomialRealLinearFactorization p) :
    AntiHerglotzUHP (polynomialLogDerivResponse p) := by
  intro z hz
  by_cases hpz : p.eval z = 0
  · -- vacuous at a zero: totalized response is 0, so Im is 0 ≤ 0.
    unfold polynomialLogDerivResponse
    rw [hpz, div_zero, Complex.zero_im]
  · rw [polynomialLogDeriv_eq_real_residue_cloud_of_factorization F z hpz]
    exact real_residue_cloud_antiHerglotz_list F.roots z hz

/-- For a nonzero polynomial whose zero set is closed under conjugation, the
upper-half-plane logarithmic-derivative sign condition is equivalent to every
root being real.

This is the Schwarz-symmetric specialization of
`polynomial_antiHerglotz_iff_roots_closedLower`: symmetry rules out lower
nonreal roots once upper nonreal roots have been excluded.-/
theorem polynomial_antiHerglotz_iff_roots_real
    (p : Polynomial ℂ) (hp : p ≠ 0)
    (h_schwarz : ∀ z : ℂ, p.eval (star z) = star (p.eval z)) :
    AntiHerglotzUHP (polynomialLogDerivResponse p) ↔
      ∀ ρ : ℂ, p.eval ρ = 0 → ρ.im = 0 := by
  constructor
  · intro h_sign
    exact polynomial_roots_real_of_logDeriv_antiHerglotz_and_conjSymm'
      p hp h_sign h_schwarz
  · intro h_roots
    exact (polynomial_antiHerglotz_iff_roots_closedLower p hp).mpr
      (fun rho hroot => (h_roots rho hroot).le)

/-- Strict Schwarz-symmetric polynomial criterion. A nonzero polynomial has
strictly anti-Herglotz logarithmic derivative on the upper half-plane exactly
when it has positive degree and all of its roots are real.-/
theorem polynomial_strictAntiHerglotz_iff_roots_real
    (p : Polynomial ℂ) (hp : p ≠ 0)
    (h_schwarz : ∀ z : ℂ, p.eval (star z) = star (p.eval z)) :
    StrictAntiHerglotzUHP (polynomialLogDerivResponse p) ↔
      0 < p.natDegree ∧
        ∀ rho : ℂ, p.eval rho = 0 → rho.im = 0 := by
  constructor
  · intro hsign
    exact ⟨
      ((polynomial_strictAntiHerglotz_iff_roots_closedLower p hp).mp hsign).1,
      (polynomial_antiHerglotz_iff_roots_real p hp h_schwarz).mp
        hsign.antiHerglotz⟩
  · rintro ⟨hdegree, hroots⟩
    exact (polynomial_strictAntiHerglotz_iff_roots_closedLower p hp).mpr
      ⟨hdegree, fun rho hroot => (hroots rho hroot).le⟩

/-- Punctured-domain form of `polynomial_antiHerglotz_iff_roots_real`.
The logarithmic-derivative inequality is requested only where `p.eval z ≠ 0`,
so the public statement does not depend on totalized division at roots.-/
theorem polynomial_logDeriv_sign_away_iff_roots_real
    (p : Polynomial ℂ) (hp : p ≠ 0)
    (h_schwarz : ∀ z : ℂ, p.eval (star z) = star (p.eval z)) :
    (∀ z : ℂ, 0 < z.im → p.eval z ≠ 0 →
        (polynomialLogDerivResponse p z).im ≤ 0) ↔
      ∀ ρ : ℂ, p.eval ρ = 0 → ρ.im = 0 := by
  constructor
  · intro h_sign
    apply (polynomial_antiHerglotz_iff_roots_real p hp h_schwarz).mp
    intro z hz
    by_cases hpz : p.eval z = 0
    · unfold polynomialLogDerivResponse
      rw [hpz, div_zero, Complex.zero_im]
    · exact h_sign z hz hpz
  · intro h_roots z hz _hpz
    exact (polynomial_antiHerglotz_iff_roots_real p hp h_schwarz).mpr
      h_roots z hz

/-- Compatibility theorem for the older real-linear-factorization API. The
factorization data already implies the reverse sign direction, so the
real-root premise of that implication is redundant in this formulation.
Prefer `polynomial_antiHerglotz_iff_roots_real` in new code.-/
theorem polynomial_realLinearFactorized_antiHerglotz_iff
    {p : Polynomial ℂ}
    (F : PolynomialRealLinearFactorization p)
    (hp : p ≠ 0)
    (hsym : ∀ z : ℂ, p.eval (star z) = star (p.eval z)) :
    AntiHerglotzUHP (polynomialLogDerivResponse p)
      ↔ ∀ ρ : ℂ, p.eval ρ = 0 → ρ.im = 0 := by
  constructor
  · intro hanti
    exact polynomial_roots_real_of_logDeriv_antiHerglotz_and_conjSymm'
      p hp hanti hsym
  · intro _
    exact polynomial_antiHerglotz_of_realLinearFactorization F

end OverflowResidueRH
