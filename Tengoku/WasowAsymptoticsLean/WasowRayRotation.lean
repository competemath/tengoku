import Tengoku.WasowAsymptoticsLean.WasowRationalAtInfinity
import Tengoku.Seed.Analysis.Analytic.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowRayRotation.rescale` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.coeff_rescale` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.entry_rescale` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.constantCoeff_rescale` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.derivative_rescale` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.rescale_X_pow_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.coeff_rotateCoefficient` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.rotate_gauge_equation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.hasFPowerSeriesAt_rotate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.coeff_rotateTaylor` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.rotated_coefficients_match` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowRayRotation.rational_ray_expansion_from_fixed` (it only prints; the queue checks the axioms of every declaration). -/

/-! Rotate one fixed complex formal reduction onto a ray, without selecting a
new formal tree. Here d is Wasow's book rank; the analytic/formal parameter is
q=d+1, so the differential gauge equation contains X^(d+2). Matrix coefficients
are noncommutative, and rescaling is proved to preserve their actual products.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators Matrix.Norms.Operator
namespace WasowRayRotation
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- True central substitution F(X) ↦ F(cX) in matrix power series.-/
def rescale (c : ℂ) : PowerSeries (Matrix ι ι ℂ) →+* PowerSeries (Matrix ι ι ℂ) where
  toFun F := PowerSeries.mk (fun n => c ^ n • PowerSeries.coeff n F)
  map_zero' := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk, map_zero, smul_zero]
  map_one' := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with hn
    · subst n
      simp
    · simp
  map_add' F G := by
    apply PowerSeries.ext
    intro n
    simp only [PowerSeries.coeff_mk, map_add, smul_add]
  map_mul' F G := by
    apply PowerSeries.ext
    intro n
    rw [PowerSeries.coeff_mk, PowerSeries.coeff_mul, PowerSeries.coeff_mul, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    have h := Finset.mem_antidiagonal.mp hk
    simp only [PowerSeries.coeff_mk]
    rw [← h, pow_add, mul_smul]
    simp only [smul_mul_assoc, mul_smul_comm]
    exact smul_comm _ _ _

/--
@isnad1 id=eq.0h4v.s9.85c9723ab6cf from=translated src=- shape=e12c967d vocab=03f2b254
-/
@[simp] theorem coeff_rescale (c : ℂ) (F : PowerSeries (Matrix ι ι ℂ)) (n : ℕ) :
    PowerSeries.coeff n (rescale c F) = c ^ n • PowerSeries.coeff n F :=
  by
    change PowerSeries.coeff n (PowerSeries.mk (fun k => c ^ k • PowerSeries.coeff k F)) = _
    exact PowerSeries.coeff_mk _ _

/-- Each entry is precisely mathlib's established scalar power substitution.
@isnad1 id=eq.0h5v.s7.d856452d9e86 from=translated src=- shape=368c7193 vocab=7d010506
-/
theorem entry_rescale (c : ℂ) (F : PowerSeries (Matrix ι ι ℂ)) (i j : ι) :
    WasowPowerSeries.entry (rescale c F) i j =
      PowerSeries.rescale c (WasowPowerSeries.entry F i j) := by
  apply PowerSeries.ext
  intro n
  simp only [WasowPowerSeries.coeff_entry, coeff_rescale, PowerSeries.coeff_rescale,
    Matrix.smul_apply, smul_eq_mul]

/--
@isnad1 id=eq.0h3v.s8.e67017c9761f from=translated src=- shape=d12d0ae9 vocab=1cf1e0ac
-/
theorem constantCoeff_rescale (c : ℂ) (F : PowerSeries (Matrix ι ι ℂ)) :
    PowerSeries.constantCoeff (rescale c F) = PowerSeries.constantCoeff F := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply,
    coeff_rescale, pow_zero, one_smul, PowerSeries.coeff_zero_eq_constantCoeff_apply]

/-- The actual coefficientwise derivative includes the scalar chain factor.
@isnad1 id=eq.0h3v.s8.3362640b65d8 from=translated src=- shape=479da0e3 vocab=af373f38
-/
theorem derivative_rescale (c : ℂ) (F : PowerSeries (Matrix ι ι ℂ)) :
    WasowPowerSeries.derivative (rescale c F) = c • rescale c (WasowPowerSeries.derivative F) := by
  apply PowerSeries.ext
  intro n
  simp only [WasowPowerSeries.coeff_derivative, coeff_rescale, PowerSeries.coeff_smul,
    smul_smul, pow_succ]
  congr 1
  ring

/--
@isnad1 id=eq.0h4v.s9.97014fbd7b3d from=translated src=- shape=a6ecbb01 vocab=3c8f28bd
-/
theorem rescale_X_pow_mul (c : ℂ) (F : PowerSeries (Matrix ι ι ℂ)) (n : ℕ) :
    rescale c (PowerSeries.X ^ n * F) =
      c ^ n • (PowerSeries.X ^ n * rescale c F) := by
  apply PowerSeries.ext
  intro k
  simp only [coeff_rescale, PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_smul]
  split_ifs with h
  · rw [smul_smul, ← pow_add, Nat.add_sub_of_le h]
  · simp

def rotateGauge (u : ℂ) (P : PowerSeries (Matrix ι ι ℂ)) := rescale u⁻¹ P

def rotateCoefficient (u : ℂ) (d : ℕ) (A : PowerSeries (Matrix ι ι ℂ)) :=
  u ^ (d+1) • rescale u⁻¹ A

/--
@isnad1 id=eq.0h5v.s9.a9f01132ce09 from=translated src=- shape=80c3a6e6 vocab=4de412c8
-/
theorem coeff_rotateCoefficient (u : ℂ) (d : ℕ)
    (A : PowerSeries (Matrix ι ι ℂ)) (k : ℕ) :
    PowerSeries.coeff k (rotateCoefficient u d A) =
      (u ^ (d+1) * (u⁻¹)^k) • PowerSeries.coeff k A := by
  rw [rotateCoefficient, PowerSeries.coeff_smul, coeff_rescale, smul_smul]

/-- The complete noncommutative differential gauge equation rotates with the
same fixed series. No recomputation of Jordan coordinates or phases occurs.
@isnad1 id=eq.2h6v.s9.c74b542ac86e from=translated src=- shape=91a7e1d0 vocab=9b79d593
-/
theorem rotate_gauge_equation (u : ℂ) (hu : u ≠ 0) (d : ℕ)
    (A P B : PowerSeries (Matrix ι ι ℂ))
    (heq : A*P-P*B = -(PowerSeries.X^(d+2)*WasowPowerSeries.derivative P)) :
    rotateCoefficient u d A * rotateGauge u P - rotateGauge u P * rotateCoefficient u d B =
      -(PowerSeries.X^(d+2) * WasowPowerSeries.derivative (rotateGauge u P)) := by
  have hc : u^(d+1)*(u⁻¹)^(d+2) = u⁻¹ := by
    rw [show d+2=(d+1)+1 by omega, pow_succ (u⁻¹) (d+1), ← mul_assoc, inv_pow,
      mul_inv_cancel₀ (pow_ne_zero _ hu), one_mul]
  unfold rotateCoefficient rotateGauge
  calc
    _ = u^(d+1) • rescale u⁻¹ (A*P-P*B) := by
      simp only [map_sub, map_mul, smul_sub, smul_mul_assoc, mul_smul_comm]
    _ = -(PowerSeries.X^(d+2) * WasowPowerSeries.derivative (rescale u⁻¹ P)) := by
      rw [heq, map_neg, rescale_X_pow_mul, smul_neg, smul_smul, hc,
        derivative_rescale, mul_smul_comm]

def rotateAnalytic (u : ℂ) (d : ℕ) (a : ℂ → Matrix ι ι ℂ) : ℂ → Matrix ι ι ℂ :=
  fun t => u ^ (d+1) • a (u⁻¹*t)

def rotateTaylor (u : ℂ) (d : ℕ)
    (s : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ)) :
    FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ) :=
  u ^ (d+1) • s.compContinuousLinearMap (u⁻¹ • ContinuousLinearMap.id ℂ ℂ)

omit [DecidableEq ι] in
/--
@isnad1 id=hasfpowe.1h5v.s7.18301074ad64 from=translated src=- shape=7eff8847 vocab=b8bdbac9
-/
theorem hasFPowerSeriesAt_rotate {a : ℂ → Matrix ι ι ℂ}
    {s : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ)}
    (ha : HasFPowerSeriesAt a s 0) (u : ℂ) (d : ℕ) :
    HasFPowerSeriesAt (rotateAnalytic u d a) (rotateTaylor u d s) 0 := by
  have hh : HasFPowerSeriesAt a s ((u⁻¹ • ContinuousLinearMap.id ℂ ℂ) 0) := by
    simpa using ha
  exact hh.compContinuousLinearMap.const_smul (c := u ^ (d+1))

omit [DecidableEq ι] in
/-- The true Taylor coefficients of the rotated analytic function, with all
rotation and inverse-variable chain factors displayed.
@isnad1 id=eq.0h5v.s7.eea201740dd2 from=translated src=- shape=e93f3656 vocab=e38c9c0f
-/
theorem coeff_rotateTaylor (u : ℂ) (d : ℕ)
    (s : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ)) (k : ℕ) :
    (rotateTaylor u d s).coeff k = (u ^ (d+1) * (u⁻¹)^k) • s.coeff k := by
  change u ^ (d+1) • s k (fun _ => u⁻¹ • (1 : ℂ)) = _
  simp only [smul_eq_mul, mul_one]
  have he : s k (fun _ => u⁻¹) = (u⁻¹)^k • s.coeff k :=
    FormalMultilinearSeries.apply_eq_pow_smul_coeff
  exact (congrArg (fun M : Matrix ι ι ℂ => u^(d+1) • M) he).trans
    (smul_smul _ _ _)

/--
@isnad1 id=eq.1h6v.s9.68c299dd2dc1 from=translated src=- shape=92e4c7d6 vocab=ee97958d
-/
theorem rotated_coefficients_match (u : ℂ) (d : ℕ)
    (s : FormalMultilinearSeries ℂ ℂ (Matrix ι ι ℂ))
    (A : PowerSeries (Matrix ι ι ℂ)) (hc : ∀ k, s.coeff k = PowerSeries.coeff k A) :
    ∀ k, (rotateTaylor u d s).coeff k = PowerSeries.coeff k (rotateCoefficient u d A) := by
  intro k
  rw [coeff_rotateTaylor, coeff_rotateCoefficient, hc]

/-- This is the exact Taylor series of the ray germ already constructed from
the rational input; it is obtained from its fixed, unrotated Taylor series.
@isnad1 id=and.2h5v.s10.79e6980f6954 from=translated src=- shape=b77b681a vocab=f932e69a
-/
theorem rational_ray_expansion_from_fixed {m : ℕ}
    (A : Matrix (Fin m) (Fin m) (RatFunc ℂ))
    (s : FormalMultilinearSeries ℂ ℂ (Matrix (Fin m) (Fin m) ℂ))
    (F : PowerSeries (Matrix (Fin m) (Fin m) ℂ))
    (ha : HasFPowerSeriesAt (WasowRationalAtInfinity.coefficient A) s 0)
    (hc : ∀ k, s.coeff k = PowerSeries.coeff k F) (θ : ℝ) :
    HasFPowerSeriesAt (WasowRationalAtInfinity.rayAnalytic A θ)
      (rotateTaylor (Complex.exp ((θ : ℂ)*Complex.I)) (WasowRationalAtInfinity.order A) s) 0 ∧
      ∀ k, (rotateTaylor (Complex.exp ((θ : ℂ)*Complex.I)) (WasowRationalAtInfinity.order A) s).coeff k =
        PowerSeries.coeff k (rotateCoefficient (Complex.exp ((θ : ℂ)*Complex.I))
          (WasowRationalAtInfinity.order A) F) :=
  ⟨hasFPowerSeriesAt_rotate ha _ _, rotated_coefficients_match _ _ s F hc⟩

end WasowRayRotation
