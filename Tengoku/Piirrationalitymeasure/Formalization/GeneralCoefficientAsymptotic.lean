import Tengoku.Piirrationalitymeasure.Formalization.GeneralCoefficientLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Lemma 4.1 for arbitrary nonnegative power series with span one. -/

namespace PiIrrationality.GeneralCoefficient

open PowerSeries MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem coefficient_local_limit (F : PowerSeries ℝ) (hF : ∀ k, 0 ≤ coeff k F)
    {x value r : ℝ} (hx : 0 < x) (hvalue : 0 < value)
    (hseries : HasSum (fun k => coeff k F * x ^ k) value)
    (hxr : x < r) (hr : Summable (fun k => coeff k F * r ^ k))
    (hspan : HasLatticeSpanOne {k : ℕ | coeff k F ≠ 0}) (q : ℕ)
    (hmean : ∫ k : ℕ, (k : ℝ) ∂(law F hF x value hx.le hvalue hseries 1).toMeasure = q)
    (hvar : 0 < ∫ k : ℕ, ((k : ℝ) - q) ^ 2
      ∂(law F hF x value hx.le hvalue hseries 1).toMeasure) :
    Tendsto (fun n : ℕ => Real.sqrt (n : ℝ) * probability F x value n (q * n)) atTop
      (𝓝 (1 / Real.sqrt (2 * Real.pi *
        (∫ k : ℕ, ((k : ℝ) - q) ^ 2 ∂(law F hF x value hx.le hvalue hseries 1).toMeasure)))) := by
  have hspan' : HasLatticeSpanOne (law F hF x value hx.le hvalue hseries 1).support := by
    rw [law_support F hF hx hvalue hseries]
    exact hspan
  simpa only [law_toReal] using lattice_probability_local_limit
    (law F hF x value hx.le hvalue hseries 1) (law F hF x value hx.le hvalue hseries) q
    hspan' (law_memLp_two F hF hx.le hvalue hseries hxr hr) hmean hvar
    (law_charFun_pow F hF hx.le hvalue hseries)

theorem coefficient_asymptotic (F : PowerSeries ℝ) (hF : ∀ k, 0 ≤ coeff k F)
    {x value r : ℝ} (hx : 0 < x) (hvalue : 0 < value)
    (hseries : HasSum (fun k => coeff k F * x ^ k) value)
    (hxr : x < r) (hr : Summable (fun k => coeff k F * r ^ k))
    (hspan : HasLatticeSpanOne {k : ℕ | coeff k F ≠ 0}) (q : ℕ)
    (hmean : ∫ k : ℕ, (k : ℝ) ∂(law F hF x value hx.le hvalue hseries 1).toMeasure = q)
    (hvar : 0 < ∫ k : ℕ, ((k : ℝ) - q) ^ 2
      ∂(law F hF x value hx.le hvalue hseries 1).toMeasure) :
    Tendsto (fun n : ℕ => coeff (q * n) (F ^ n) /
      (value ^ n / x ^ (q * n) /
        Real.sqrt (2 * Real.pi *
          (∫ k : ℕ, ((k : ℝ) - q) ^ 2
            ∂(law F hF x value hx.le hvalue hseries 1).toMeasure) * n))) atTop (𝓝 1) := by
  let v := ∫ k : ℕ, ((k : ℝ) - q) ^ 2
    ∂(law F hF x value hx.le hvalue hseries 1).toMeasure
  have hv : 0 < v := hvar
  have hnormal : 0 < Real.sqrt (2 * Real.pi * v) := by positivity
  have ht := (coefficient_local_limit F hF hx hvalue hseries hxr hr hspan q hmean hvar).const_mul
    (Real.sqrt (2 * Real.pi * v))
  have hn : Real.sqrt (2 * Real.pi * v) * (1 / Real.sqrt (2 * Real.pi * v)) = 1 := by
    field_simp
  change Tendsto _ atTop (𝓝 (Real.sqrt (2 * Real.pi * v) * (1 / Real.sqrt (2 * Real.pi * v)))) at ht
  rw [hn] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hnpos
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hsqrt : Real.sqrt (2 * Real.pi * v * (n : ℝ)) =
      Real.sqrt (2 * Real.pi * v) * Real.sqrt (n : ℝ) :=
    Real.sqrt_mul (by positivity) _
  change _ = coeff (q * n) (F ^ n) / (value ^ n / x ^ (q * n) /
    Real.sqrt (2 * Real.pi * v * n))
  rw [probability_extraction F hx hvalue n (q * n), hsqrt]
  field_simp [hx.ne', hvalue.ne', hnormal.ne', (Real.sqrt_pos.mpr hnreal).ne']

theorem lemma_4_1 (F : PowerSeries ℝ) (hF : ∀ k, 0 ≤ coeff k F)
    {R x value : ℝ} (hx : 0 < x) (hxR : x < R) (hvalue : 0 < value)
    (hseries : HasSum (fun k => coeff k F * x ^ k) value)
    (hconv : ∀ y : ℝ, 0 ≤ y → y < R → Summable (fun k => coeff k F * y ^ k))
    (hspan : HasLatticeSpanOne {k : ℕ | coeff k F ≠ 0}) (q : ℕ)
    (hmean : ∫ k : ℕ, (k : ℝ) ∂(law F hF x value hx.le hvalue hseries 1).toMeasure = q)
    (hvar : 0 < ∫ k : ℕ, ((k : ℝ) - q) ^ 2
      ∂(law F hF x value hx.le hvalue hseries 1).toMeasure) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (𝓝 0) ∧ ∀ n : ℕ, 0 < n →
      coeff (q * n) (F ^ n) =
        value ^ n / x ^ (q * n) /
          Real.sqrt (2 * Real.pi *
            (∫ k : ℕ, ((k : ℝ) - q) ^ 2
              ∂(law F hF x value hx.le hvalue hseries 1).toMeasure) * n) * (1 + error n) := by
  let v := ∫ k : ℕ, ((k : ℝ) - q) ^ 2
    ∂(law F hF x value hx.le hvalue hseries 1).toMeasure
  let main := fun n : ℕ => value ^ n / x ^ (q * n) / Real.sqrt (2 * Real.pi * v * n)
  have ht := coefficient_asymptotic F hF hx hvalue hseries
    (r := (x + R) / 2) (by linarith)
    (hconv _ (by linarith) (by linarith)) hspan q hmean hvar
  refine ⟨fun n => coeff (q * n) (F ^ n) / main n - 1, ?_, ?_⟩
  · simpa only [sub_self] using ht.sub_const 1
  · intro n hn
    have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    have hv : 0 < v := hvar
    have hmain : main n ≠ 0 := by dsimp [main]; positivity
    change coeff (q * n) (F ^ n) = main n * (1 + (coeff (q * n) (F ^ n) / main n - 1))
    field_simp
    ring

end PiIrrationality.GeneralCoefficient
