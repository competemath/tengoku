import Tengoku.Nlalib.NLAlib.ForMathlib.Analysis.LogarithmicMomentFactor
import Tengoku.Seed.Analysis.SpecialFunctions.Sqrt
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Explicit fixed-confidence spectral-grid scale

The actual interpolation prefactor and Gaussian resolvent concentration
budget are absorbed at height `10^10 Δ`. These elementary estimates
retain the source dimension and weak parameters.
-/

noncomputable section
set_option autoImplicit false
namespace NLAlib

/-- The actual interpolation coefficient at order `2q` is bounded by a
universal cubic in the positive integer order.
@isnad1 id=le.1h1v.s7.893afbef9ee0 from=translated src=- shape=ae2ab4f9 vocab=5092686c
-/
theorem gaussian_free_even_order_prefactor_le {q : ℕ} (hq : 0 < q) :
    (((2 * (2 * q) + 1) * (2 * (2 * q) + 2) ^ 2 : ℕ) : ℝ) ≤
      180 * (q : ℝ) ^ 3 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hq2 : (q : ℝ) ≤ (q : ℝ) ^ 2 := by nlinarith
  have hq3 : (q : ℝ) ^ 2 ≤ (q : ℝ) ^ 3 := by
    nlinarith [mul_nonneg (sq_nonneg (q : ℝ)) (sub_nonneg.mpr hq1)]
  push_cast
  nlinarith

/-- The true Markov dimension factor is bounded uniformly at logarithmic
moment order.
@isnad1 id=le.2h2v.s6.007840d36e2e from=translated src=- shape=1cd5c80e vocab=5fba044d
-/
theorem gaussian_free_markov_factor_le {q d : ℕ} (hq : 0 < q)
    (hlog : Real.log (d : ℝ) ≤ q) :
    Real.exp 1 * (d : ℝ) ^ (1 / (4 * (q : ℝ))) ≤ (1000000 : ℝ) := by
  have hp : 0 < 2 * (q : ℝ) := by positivity
  have h := Real.exp_one_mul_rpow_inv_two_mul_le_nine_of_log_le
    (Nat.cast_nonneg d) hp (hlog.trans (by nlinarith [Nat.cast_nonneg (α := ℝ) q] : (q : ℝ) ≤ 2 * (q : ℝ)))
  have heq : 2 * (2 * (q : ℝ)) = 4 * q := by ring
  rw [heq] at h
  exact h.trans (by norm_num)

/-- The actual native free moment multiplier is below the fixed universal
comparison constant.
@isnad1 id=le.0h0v.s5.4ab8536e012f from=translated src=- shape=bdb6c026 vocab=639180de
-/
theorem gaussian_free_ultracontractive_factor_le :
    438 * Real.exp 5 ≤ (1000000 : ℝ) := by
  have he : Real.exp 5 = (Real.exp 1) ^ 5 := by
    rw [← Real.exp_nat_mul]
    norm_num
  rw [he]
  have hp := pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_three.le 5
  norm_num at hp
  nlinarith

/-- At the fixed large height the genuine interpolation budget is at most
one elementary reciprocal-height term.
@isnad1 id=other.5h4v.s8.cc654dc8b0ee from=translated src=- shape=6970072b vocab=d78568b7
-/
theorem gaussian_free_interpolation_budget_le {q : ℕ} (hq : 0 < q)
    {V W Δ : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W) (hΔ : 0 < Δ)
    (hbudget : (q : ℝ) ^ 3 * (V * W) ≤ Δ ^ 4) :
    let η : ℝ := 10000000000 * Δ
    (((2 * (2 * q) + 1) * (2 * (2 * q) + 2) ^ 2 : ℕ) : ℝ) *
      (V * W) * (η⁻¹) ^ 5 ≤ Δ / η ^ 2 := by
  dsimp only
  let η : ℝ := 10000000000 * Δ
  have hη : 0 < η := by dsimp [η]; positivity
  have hcoef := gaussian_free_even_order_prefactor_le hq
  have hraw : (((2 * (2 * q) + 1) * (2 * (2 * q) + 2) ^ 2 : ℕ) : ℝ) *
      (V * W) * (η⁻¹) ^ 5 ≤ 180 * Δ ^ 4 / η ^ 5 := by
    calc
      _ ≤ (180 * (q : ℝ) ^ 3) * (V * W) * (η⁻¹) ^ 5 :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right hcoef (mul_nonneg hV hW)) (by positivity)
      _ ≤ (180 * Δ ^ 4) * (η⁻¹) ^ 5 :=
        mul_le_mul_of_nonneg_right (by nlinarith only [hbudget]) (by positivity)
      _ = _ := by rw [div_eq_mul_inv, inv_pow]
  refine hraw.trans ?_
  apply (div_le_div_iff₀ (pow_pos hη 5) (pow_pos hη 2)).mpr
  dsimp [η]
  nlinarith [pow_nonneg hΔ.le 6]

/-- Gaussian resolvent fluctuation terms at order `2q` cost at most five
copies of the source weak radius.
@isnad1 id=other.3h3v.s7.8889aa7a87bc from=translated src=- shape=1701c81f vocab=3d761e98
-/
theorem gaussian_free_fluctuation_sqrt_le {q : ℕ} (hq : 0 < q)
    {s η : ℝ} (hs : 0 ≤ s) (hη : 0 < η) :
    let c : ℝ := s ^ 2 * (η⁻¹) ^ 4
    Real.sqrt (4 * c * (2 * (q : ℝ))) + 2 * Real.sqrt (c * q) ≤
      5 * (s * Real.sqrt (q : ℝ)) / η ^ 2 := by
  let c : ℝ := s ^ 2 * (η⁻¹) ^ 4
  let L : ℝ := s * Real.sqrt (q : ℝ) / η ^ 2
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hL : 0 ≤ L := by dsimp [L]; positivity
  have hLs : L ^ 2 = c * q := by
    dsimp [L, c]
    rw [div_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg q)]
    field_simp
  have hsq : Real.sqrt (c * q) = L := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _) hL).mp
    rw [Real.sq_sqrt (by positivity)]
    exact hLs.symm
  have hlarge : Real.sqrt (4 * c * (2 * (q : ℝ))) ≤ 3 * L := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [sq_nonneg L]
  dsimp only
  calc
    _ ≤ 5 * L := by rw [hsq]; linarith
    _ = _ := by dsimp [L]; ring

/-- The forward Markov interpolation budget is absorbed by the actual
fixed comparison error.
@isnad1 id=le.4h5v.s7.18157dba4519 from=translated src=- shape=801e96d6 vocab=68a6443b
-/
theorem gaussian_free_forward_error_le {q d : ℕ} (hq : 0 < q)
    (hlog : Real.log (d : ℝ) ≤ q) {B Δ η : ℝ} (hB : 0 ≤ B) (hΔ : 0 ≤ Δ) :
    (Real.exp 1 * (d : ℝ) ^ (1 / (4 * (q : ℝ)))) * B ≤
      1000000 * (B + 6 * Δ / η ^ 2) := by
  have h := mul_le_mul_of_nonneg_right (gaussian_free_markov_factor_le hq hlog) hB
  have hpos : 0 ≤ 6 * Δ / η ^ 2 := by positivity
  nlinarith

/-- The actual reverse free/Gaussian resolvent error is absorbed by the
fixed interpolation error, with the literal original weak and variance
budgets.
@isnad1 id=other.7h7v.s8.0ba3953713d0 from=translated src=- shape=06cc56e6 vocab=ba54ee9d
-/
theorem gaussian_free_reverse_error_le {q d : ℕ} (hq : 0 < q)
    {s σ B Δ η : ℝ} (hs : 0 ≤ s) (hσ : 0 ≤ σ) (hB : 0 ≤ B)
    (hη : 0 < η) (hweak : s * Real.sqrt (q : ℝ) ≤ Δ)
    (hvariance : σ / (d : ℝ) ^ 2 ≤ Δ) :
    let c : ℝ := s ^ 2 * (η⁻¹) ^ 4
    (438 * Real.exp 5) * (Real.sqrt (4 * c * (2 * (q : ℝ))) +
      2 * Real.sqrt (c * q) + B + σ / ((d : ℝ) ^ 2 * η ^ 2)) ≤
      1000000 * (B + 6 * Δ / η ^ 2) := by
  dsimp only
  have hfluc := gaussian_free_fluctuation_sqrt_le hq hs hη
  dsimp only at hfluc
  have hfluc' : 5 * (s * Real.sqrt (q : ℝ)) / η ^ 2 ≤ 5 * Δ / η ^ 2 := by
    exact div_le_div_of_nonneg_right (by nlinarith only [hweak]) (sq_nonneg η)
  have hvar : σ / ((d : ℝ) ^ 2 * η ^ 2) ≤ Δ / η ^ 2 := by
    rw [← div_div]
    exact div_le_div_of_nonneg_right hvariance (sq_nonneg η)
  have hnonneg : 0 ≤ Real.sqrt (4 * (s ^ 2 * (η⁻¹) ^ 4) * (2 * (q : ℝ))) +
      2 * Real.sqrt (s ^ 2 * (η⁻¹) ^ 4 * q) + B + σ / ((d : ℝ) ^ 2 * η ^ 2) := by positivity
  have h := mul_le_mul_of_nonneg_right gaussian_free_ultracontractive_factor_le hnonneg
  ring_nf at h hfluc hfluc' hvar ⊢
  linarith only [h, hfluc, hfluc', hvar]

/-- The complete interpolation, free resolvent fluctuation, and grid mesh
budget is absorbed by half the reciprocal height.
@isnad1 id=other.6h5v.s8.0661e09300ae from=translated src=- shape=ee3451d2 vocab=3d761e98
-/
theorem gaussian_free_grid_error_budget_le {q : ℕ} (hq : 0 < q)
    {V W s Δ : ℝ} (hV : 0 ≤ V) (hW : 0 ≤ W)
    (hΔ : 0 < Δ) (hweak : s * Real.sqrt (q : ℝ) ≤ Δ)
    (hbudget : (q : ℝ) ^ 3 * (V * W) ≤ Δ ^ 4) :
    let η : ℝ := 10000000000 * Δ
    let B : ℝ := (((2 * (2 * q) + 1) * (2 * (2 * q) + 2) ^ 2 : ℕ) : ℝ) *
      (V * W) * (η⁻¹) ^ 5
    let err : ℝ := 1000000 * (B + 6 * Δ / η ^ 2)
    err + (1000000 + 1) * (2 * s * Real.sqrt (q : ℝ)) / η ^ 2 ≤ (2 * η)⁻¹ := by
  dsimp only
  let η : ℝ := 10000000000 * Δ
  have hη : 0 < η := by dsimp [η]; positivity
  have hB := gaussian_free_interpolation_budget_le hq hV hW hΔ hbudget
  change (((2 * (2 * q) + 1) * (2 * (2 * q) + 2) ^ 2 : ℕ) : ℝ) *
    (V * W) * (η⁻¹) ^ 5 ≤ Δ / η ^ 2 at hB
  have hmesh : (1000000 + 1 : ℝ) * (2 * s * Real.sqrt (q : ℝ)) / η ^ 2 ≤
      (2 * (1000000 + 1 : ℝ)) * Δ / η ^ 2 := by
    apply div_le_div_of_nonneg_right _ (sq_nonneg η)
    nlinarith only [hweak]
  have hupper : (1000000 : ℝ) *
      ((((2 * (2 * q) + 1) * (2 * (2 * q) + 2) ^ 2 : ℕ) : ℝ) *
        (V * W) * (η⁻¹) ^ 5 + 6 * Δ / η ^ 2) +
      (1000000 + 1) * (2 * s * Real.sqrt (q : ℝ)) / η ^ 2 ≤
      (9000002 : ℝ) * Δ / η ^ 2 := by
    ring_nf at hB hmesh ⊢
    linarith only [hB, hmesh]
  refine hupper.trans ?_
  rw [← one_div]
  apply (div_le_div_iff₀ (pow_pos hη 2) (by positivity : 0 < 2 * η)).mpr
  dsimp [η]
  nlinarith [sq_nonneg Δ]

/-- With a positive weak scale the literal Gaussian fluctuation tail at
`2 sqrt(cq)` is exactly `2 exp(-2q)`.
@isnad1 id=other.3h3v.s7.6b820e848ed0 from=translated src=- shape=c6c7c5e1 vocab=3ba082ed
-/
theorem gaussian_free_fluctuation_tail_eq {q : ℕ} (hq : 0 < q)
    {s η : ℝ} (hs : 0 < s) (hη : 0 < η) :
    let c : ℝ := s ^ 2 * (η⁻¹) ^ 4
    2 * Real.exp (-((2 * Real.sqrt (c * q)) ^ 2) / (2 * c)) =
      2 * Real.exp (-2 * (q : ℝ)) := by
  let c : ℝ := s ^ 2 * (η⁻¹) ^ 4
  have hc : 0 < c := by dsimp [c]; positivity
  change 2 * Real.exp (-((2 * Real.sqrt (c * q)) ^ 2) / (2 * c)) = _
  congr 2
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  field_simp [hc.ne']

end NLAlib
