import Tengoku.WasowAsymptoticsLean.WasowRamifiedGauge
import Tengoku.WasowAsymptoticsLean.WasowShearingGauge
import Tengoku.WasowAsymptoticsLean.WasowPhaseNormalization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.rootOnRay_refine` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.phaseOnRay_refine` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.refinePhase_coeff_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.deriv_phaseOnRay_refine` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.commonDenominator_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.denominator_dvd_common` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.common_refinement_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.common_refinement_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.commonFamily_coeff_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.phaseOnRay_commonFamily` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.refinedWitness` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.constant_family_pullback` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowPhaseFamily.shearing_family_pullback` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Actual algebra for fixed finite Puiseux phase families.  Every denominator and
polynomial below is selected before the ray direction.  The common-denominator
construction uses the zero root branch throughout; it does not replace arbitrary
angle-dependent branch choices by zero.  No existence assertion for the general
rational normal-form goal is assumed or proved here.
-/
set_option autoImplicit false
noncomputable section
open Filter
open scoped Topology BigOperators
namespace WasowPhaseFamily
open CRGNormalFormGoal

/-- Raising the zero branch of a refined root gives the original zero branch.
@isnad1 id=eq.3h4v.s6.42b6299c9b17 from=translated src=- shape=b18b3120 vocab=987da774
-/
theorem rootOnRay_refine (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    rootOnRay (p*k) θ ⟨0, Nat.mul_pos hp hk⟩ r ^ k = rootOnRay p θ ⟨0,hp⟩ r := by
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  have hpow : (r ^ (1 / ((p*k : ℕ) : ℝ))) ^ k = r ^ (1 / (p : ℝ)) := by
    rw [← Real.rpow_mul_natCast hr]
    congr 1
    push_cast
    field_simp
  have hexp : Complex.exp ((((θ / ((p*k : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I) ^ k =
      Complex.exp (((θ / (p : ℝ)) : ℝ) * Complex.I) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp
  simp only [rootOnRay, Nat.cast_zero, mul_zero, add_zero,
    mul_pow, ← Complex.ofReal_pow, hpow, hexp]

/-- Refinement of the phase polynomial is an actual polynomial composition.-/
def refinePhase (k : ℕ) (F : Polynomial ℂ) : Polynomial ℂ :=
  F.comp (Polynomial.X ^ k)

/--
@isnad1 id=eq.3h5v.s6.3c4d398399d3 from=translated src=- shape=e597b8ea vocab=763efda3
-/
theorem phaseOnRay_refine (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (F : Polynomial ℂ) (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    phaseOnRay (p*k) (refinePhase k F) θ ⟨0,Nat.mul_pos hp hk⟩ r =
      phaseOnRay p F θ ⟨0,hp⟩ r := by
  simp only [phaseOnRay, refinePhase, Polynomial.eval_comp, Polynomial.eval_pow,
    Polynomial.eval_X, rootOnRay_refine p k hp hk θ hr]

/--
@isnad1 id=eq.1h2v.s5.a500b3fdd1ba from=translated src=- shape=060df905 vocab=d2f890fb
-/
theorem refinePhase_coeff_zero (k : ℕ) (hk : 0 < k) (F : Polynomial ℂ) :
    (refinePhase k F).coeff 0 = F.coeff 0 := by
  simp only [refinePhase, Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_comp]
  simp [hk.ne']

/--
@isnad1 id=eq.3h5v.s7.98600de27539 from=translated src=- shape=e9ba887b vocab=c9cc808d
-/
theorem deriv_phaseOnRay_refine (p k : ℕ) (hp : 0 < p) (hk : 0 < k)
    (F : Polynomial ℂ) (θ : ℝ) {r : ℝ} (hr : 0 < r) :
    deriv (phaseOnRay (p*k) (refinePhase k F) θ ⟨0,Nat.mul_pos hp hk⟩) r =
      deriv (phaseOnRay p F θ ⟨0,hp⟩) r := by
  apply Filter.EventuallyEq.deriv_eq
  filter_upwards [eventually_gt_nhds hr] with t ht
  exact phaseOnRay_refine p k hp hk F θ ht.le

/-- A common denominator for any finite family; no angle is an input.-/
def commonDenominator {ι : Type*} [Fintype ι] (p : ι → ℕ) : ℕ := ∏ i, p i

/--
@isnad1 id=lt.1h2v.s5.c9e83e754d42 from=translated src=- shape=92c325ac vocab=5eb6dd76
-/
theorem commonDenominator_pos {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) : 0 < commonDenominator p :=
  Finset.prod_pos (fun i _ => hp i)

/--
@isnad1 id=dvd.0h3v.s4.f2dc2c6f4ff0 from=translated src=- shape=695ed55a vocab=dc785c4b
-/
theorem denominator_dvd_common {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (i : ι) : p i ∣ commonDenominator p := by
  classical
  exact Finset.dvd_prod_of_mem p (Finset.mem_univ i)

/--
@isnad1 id=lt.1h3v.s5.9ab708bfdf03 from=translated src=- shape=9467bfbb vocab=df35c464
-/
theorem common_refinement_pos {ι : Type*} [Fintype ι]
    (p : ι → ℕ) (hp : ∀ i, 0 < p i) (i : ι) : 0 < commonDenominator p / p i := by
  exact Nat.div_pos (Nat.le_of_dvd (commonDenominator_pos p hp) (denominator_dvd_common p i)) (hp i)

/--
@isnad1 id=eq.0h3v.s5.5992bc42b54e from=translated src=- shape=d9c879bc vocab=e0407be4
-/
theorem common_refinement_mul {ι : Type*} [Fintype ι] (p : ι → ℕ) (i : ι) :
    p i * (commonDenominator p / p i) = commonDenominator p :=
  Nat.mul_div_cancel' (denominator_dvd_common p i)

/-- A finite collection of differently ramified blocks becomes one fixed family
on the dependent sum of their column indices.-/
def commonFamily {ι : Type*} [Fintype ι] (p : ι → ℕ)
    {d : ι → ℕ} (F : ∀ i, Fin (d i) → Polynomial ℂ) :
    (Σ i, Fin (d i)) → Polynomial ℂ :=
  fun j => refinePhase (commonDenominator p / p j.1) (F j.1 j.2)

/--
@isnad1 id=eq.2h5v.s6.724f76ac6312 from=translated src=- shape=5a638be8 vocab=9fadd99e
-/
theorem commonFamily_coeff_zero {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) {d : ι → ℕ} (F : ∀ i, Fin (d i) → Polynomial ℂ)
    (hF : ∀ i j, (F i j).coeff 0 = 0) (j : Σ i, Fin (d i)) :
    (commonFamily p F j).coeff 0 = 0 := by
  rw [commonFamily, refinePhase_coeff_zero _ (common_refinement_pos p hp j.1), hF]

/--
@isnad1 id=eq.2h7v.s7.b8da33c62a7c from=translated src=- shape=ac904617 vocab=39d95bd8
-/
theorem phaseOnRay_commonFamily {ι : Type*} [Fintype ι] (p : ι → ℕ)
    (hp : ∀ i, 0 < p i) {d : ι → ℕ} (F : ∀ i, Fin (d i) → Polynomial ℂ)
    (j : Σ i, Fin (d i)) (θ : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    phaseOnRay (commonDenominator p) (commonFamily p F j) θ
      ⟨0, commonDenominator_pos p hp⟩ r = phaseOnRay (p j.1) (F j.1 j.2) θ ⟨0,hp j.1⟩ r := by
  have hh := phaseOnRay_refine (p j.1) (commonDenominator p / p j.1) (hp j.1)
    (common_refinement_pos p hp j.1) (F j.1 j.2) θ hr
  simp only [phaseOnRay, rootOnRay] at hh ⊢
  simpa only [common_refinement_mul p j.1, commonFamily] using hh

/-- This explicit witness may be reused after a common-denominator refinement:
the matrices and all polynomial bounds are unchanged.-/
def refinedWitness {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (p k : ℕ) (hp : 0 < p) (hk : 0 < k) (F : Fin m → Polynomial ℂ) (θ : ℝ)
    (W : RayGaugeWitness A θ (fun i => phaseOnRay p (F i) θ ⟨0,hp⟩)) :
    RayGaugeWitness A θ
      (fun i => phaseOnRay (p*k) (refinePhase k (F i)) θ ⟨0,Nat.mul_pos hp hk⟩) where
  T := W.T
  S := W.S
  T' := W.T'
  R := W.R
  C := W.C
  K := W.K
  R_pos := W.R_pos
  C_pos := W.C_pos
  K_nonneg := W.K_nonneg
  pole_free := W.pole_free
  T_derivative := W.T_derivative
  inverse_left := W.inverse_left
  inverse_right := W.inverse_right
  T_bound := W.T_bound
  S_bound := W.S_bound
  gauge_identity := by
    intro r hr
    simpa only [deriv_phaseOnRay_refine p k hp hk _ θ (W.R_pos.trans hr)] using W.gauge_identity r hr

/-- Constant coordinates preserve exactly the given, direction-independent
phase family. The actual intermediate gauge is constructed from the matrix.
@isnad1 id=nonempty.3h6v.s6.14c5d7973fc6 from=translated src=- shape=7c402d7a vocab=d626ea59
-/
theorem constant_family_pullback {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (C : Matrix (Fin m) (Fin m) ℂ) (hC : C.det ≠ 0)
    (p : ℕ) (hp : 0 < p) (F : Fin m → Polynomial ℂ)
    (h : ∀ θ : ℝ, Nonempty (RayGaugeWitness (WasowGaugeComposition.constantConjugate A C) θ
      (fun i => phaseOnRay p (F i) θ ⟨0,hp⟩))) :
    ∀ θ : ℝ, Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (F i) θ ⟨0,hp⟩)) := by
  intro θ
  obtain ⟨W⟩ := h θ
  exact WasowGaugeComposition.pullback_constant_rayGauge A C hC θ _ W

/-- Integer shearing likewise constructs the genuine intermediate gauge and
retains all phase polynomials selected before the angle.
@isnad1 id=nonempty.2h6v.s6.7d1eeb735708 from=translated src=- shape=562d1b89 vocab=19988990
-/
theorem shearing_family_pullback {m : ℕ} (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (k : Fin m → ℤ) (p : ℕ) (hp : 0 < p) (F : Fin m → Polynomial ℂ)
    (h : ∀ θ : ℝ, Nonempty (RayGaugeWitness (WasowShearingGauge.shearedCoefficient A k) θ
      (fun i => phaseOnRay p (F i) θ ⟨0,hp⟩))) :
    ∀ θ : ℝ, Nonempty (RayGaugeWitness A θ (fun i => phaseOnRay p (F i) θ ⟨0,hp⟩)) := by
  intro θ
  obtain ⟨W⟩ := h θ
  exact WasowShearingGauge.pullback_shearing_rayGauge A k θ _ W

end WasowPhaseFamily
