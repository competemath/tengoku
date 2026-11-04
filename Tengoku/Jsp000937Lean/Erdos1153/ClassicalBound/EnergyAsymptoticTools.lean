import Tengoku.Jsp000937Lean.Erdos1153.ClassicalBound.ArcsineBinCount
import Tengoku.Jsp000937Lean.Erdos1153.ClassicalBound.EnergyBins
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics
import Tengoku.Seed.Algebra.Order.Floor.Semifield
import Tengoku.Seed.NumberTheory.Harmonic.Bounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Asymptotic parameter selection for the clipped pair-energy argument

This file makes the discrete rounding convention explicit.  With `d=n-1`,
`arcsineTotalBinCount n q` is the number of reflected geometric bins, and
`arcsineDenseThreshold n q R` is the natural quotient

    n / (arcsineTotalBinCount n q * R).

For fixed `q > 1` and fixed positive divisors, the bin count is logarithmic,
so this threshold tends to infinity.  More precisely, its further quotient
by any fixed `L` has harmonic number at least `(1-eta) log n` eventually.
-/

namespace Erdos1153
namespace ClassicalBound

open Filter Asymptotics

noncomputable section

/-- Total number of bins in the reflected logarithmic arcsine partition
for degree `n-1`.-/
def arcsineTotalBinCount (n : ℕ) (q : ℝ) : ℕ :=
  2 * (arcsineGeometricExponent (n - 1) q + 1)

/-- Natural dense-bin threshold.  This is the floor implicit in the finite
combinatorial argument.-/
def arcsineDenseThreshold (n : ℕ) (q : ℝ) (R : ℕ) : ℕ :=
  n / (arcsineTotalBinCount n q * R)

/-- The explicit coefficient in the `C_q (log n + 1)` total-bin bound.-/
def arcsineTotalBinCountCoefficient (q : ℝ) : ℝ :=
  2 * ((Real.log 2 + 2) / Real.log q + 2)

/--
@isnad1 id=lt.0h2v.s3.03c8c8c8837f from=translated src=- shape=25b8bdde vocab=e8996850
-/
lemma arcsineTotalBinCount_pos (n : ℕ) (q : ℝ) :
    0 < arcsineTotalBinCount n q := by
  unfold arcsineTotalBinCount
  positivity

/--
@isnad1 id=lt.1h1v.s4.3af1b6260723 from=translated src=- shape=35bd48ee vocab=eab45ca3
-/
lemma arcsineTotalBinCountCoefficient_pos {q : ℝ} (hq : 1 < q) :
    0 < arcsineTotalBinCountCoefficient q := by
  unfold arcsineTotalBinCountCoefficient
  have hlogq : 0 < Real.log q := Real.log_pos hq
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  positivity

/-- The degree `n-1` is positive from `n=2` onward.
@isnad1 id=le.1h1v.s5.ceb5722f42ca from=translated src=- shape=6528d12f vocab=cf369417
-/
lemma one_le_pred_of_two_le {n : ℕ} (hn : 2 ≤ n) :
    1 ≤ n - 1 := by omega

/--
@isnad1 id=eventual.0h0v.s4.3c425a56abeb from=translated src=- shape=ed68300b vocab=82fc9de5
-/
theorem eventually_one_le_pred :
    ∀ᶠ n : ℕ in atTop, 1 ≤ n - 1 := by
  filter_upwards [eventually_ge_atTop 2] with n hn
  omega

/-- Replace `log(n-1)` by `log n` in the committed total-bin estimate.
@isnad1 id=le.2h2v.s5.57f84e5c36bf from=translated src=- shape=4d6d9194 vocab=6d92d287
-/
theorem arcsineTotalBinCount_le_coefficient_mul_log
    {n : ℕ} {q : ℝ} (hn : 2 ≤ n) (hq : 1 < q) :
    (arcsineTotalBinCount n q : ℝ) ≤
      arcsineTotalBinCountCoefficient q * (Real.log (n : ℝ) + 1) := by
  have hd : 1 ≤ n - 1 := one_le_pred_of_two_le hn
  have hdpos : 0 < ((n - 1 : ℕ) : ℝ) := by positivity
  have hnpos : 0 < (n : ℝ) := by positivity
  have hpredle : ((n - 1 : ℕ) : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast Nat.sub_le n 1
  have hlogle : Real.log ((n - 1 : ℕ) : ℝ) ≤ Real.log (n : ℝ) :=
    Real.log_le_log hdpos hpredle
  have hC : 0 ≤ ((Real.log 2 + 2) / Real.log q + 2) := by
    have := arcsineTotalBinCountCoefficient_pos hq
    unfold arcsineTotalBinCountCoefficient at this
    nlinarith
  calc
    (arcsineTotalBinCount n q : ℝ) ≤
        2 * (((Real.log 2 + 2) / Real.log q + 2) *
          (Real.log ((n - 1 : ℕ) : ℝ) + 1)) := by
      exact two_mul_arcsineGeometricExponent_add_one_le_constant_mul_logDegree
        hd hq
    _ ≤ 2 * (((Real.log 2 + 2) / Real.log q + 2) *
          (Real.log (n : ℝ) + 1)) := by
      gcongr
    _ = arcsineTotalBinCountCoefficient q *
          (Real.log (n : ℝ) + 1) := by
      rw [arcsineTotalBinCountCoefficient]
      ring

/-- A fixed multiple of `log x + 1` is eventually bounded by every
positive real power of `x`.
@isnad1 id=eventual.2h2v.s6.9fd86f9bed5f from=translated src=- shape=594d6171 vocab=de16a433
-/
lemma eventually_const_mul_log_add_one_le_rpow
    {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∀ᶠ x : ℝ in atTop, A * (Real.log x + 1) ≤ x ^ δ := by
  have hlog : Real.log =o[atTop] (fun x : ℝ ↦ x ^ δ) :=
    isLittleO_log_rpow_atTop hδ
  have hone : (fun _x : ℝ ↦ (1 : ℝ)) =o[atTop]
      (fun x : ℝ ↦ x ^ δ) :=
    (Real.isLittleO_const_log_atTop (c := (1 : ℝ))).trans hlog
  have hsmall : (fun x : ℝ ↦ A * (Real.log x + 1)) =o[atTop]
      (fun x : ℝ ↦ x ^ δ) :=
    (hlog.add hone).const_mul_left A
  filter_upwards [hsmall.eventuallyLE, eventually_ge_atTop (1 : ℝ)] with x hx hx1
  have hleft : 0 ≤ A * (Real.log x + 1) := by
    exact mul_nonneg hA (add_nonneg (Real.log_nonneg hx1) zero_le_one)
  have hright : 0 ≤ x ^ δ := Real.rpow_nonneg (zero_le_one.trans hx1) δ
  simpa only [Real.norm_eq_abs, abs_of_nonneg hleft, abs_of_nonneg hright] using hx

/-- The total number of bins times any fixed natural factors is eventually
at most `n^delta`.
@isnad1 id=eventual.2h4v.s6.00ed2bb41aff from=translated src=- shape=5ef957c6 vocab=c31f2922
-/
theorem eventually_totalBinCount_mul_fixed_le_rpow
    {q δ : ℝ} (hq : 1 < q) (hδ : 0 < δ) (R L : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((arcsineTotalBinCount n q * R * L : ℕ) : ℝ) ≤ (n : ℝ) ^ δ := by
  let A := arcsineTotalBinCountCoefficient q * (R : ℝ) * (L : ℝ)
  have hA : 0 ≤ A := by
    dsimp [A]
    exact mul_nonneg
      (mul_nonneg (arcsineTotalBinCountCoefficient_pos hq).le
        (Nat.cast_nonneg R)) (Nat.cast_nonneg L)
  have hpowerReal := eventually_const_mul_log_add_one_le_rpow hA hδ
  have hpowerNat : ∀ᶠ n : ℕ in atTop,
      A * (Real.log (n : ℝ) + 1) ≤ (n : ℝ) ^ δ :=
    tendsto_natCast_atTop_atTop.eventually hpowerReal
  filter_upwards [eventually_ge_atTop 2, hpowerNat] with n hn hpower
  have hbins := arcsineTotalBinCount_le_coefficient_mul_log hn hq
  calc
    ((arcsineTotalBinCount n q * R * L : ℕ) : ℝ) =
        (arcsineTotalBinCount n q : ℝ) * (R : ℝ) * (L : ℝ) := by
      norm_num
    _ ≤ (arcsineTotalBinCountCoefficient q *
          (Real.log (n : ℝ) + 1)) * (R : ℝ) * (L : ℝ) := by
      gcongr
    _ = A * (Real.log (n : ℝ) + 1) := by
      dsimp [A]
      ring
    _ ≤ (n : ℝ) ^ δ := hpower

/-- Eventually the fixed local divisor `L` fits below the natural dense-bin
threshold.
@isnad1 id=eventual.3h3v.s5.ba8a4aaa2ee5 from=translated src=- shape=48ac606c vocab=5474f4d1
-/
theorem eventually_le_arcsineDenseThreshold
    {q : ℝ} (hq : 1 < q) {R L : ℕ} (hR : 1 ≤ R) (_hL : 1 ≤ L) :
    ∀ᶠ n : ℕ in atTop, L ≤ arcsineDenseThreshold n q R := by
  have hden := eventually_totalBinCount_mul_fixed_le_rpow hq one_pos R L
  filter_upwards [hden] with n hn
  rw [Real.rpow_one] at hn
  have hnat : arcsineTotalBinCount n q * R * L ≤ n := by
    exact_mod_cast hn
  have hBR : 0 < arcsineTotalBinCount n q * R :=
    mul_pos (arcsineTotalBinCount_pos n q) (Nat.zero_lt_of_lt hR)
  rw [arcsineDenseThreshold, Nat.le_div_iff_mul_le hBR]
  simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hnat

/-- Exact division loss: removing `B * floor(n/(B R))` leaves at least the
fraction `1-1/R` of the original mass.
@isnad1 id=le.1h3v.s6.5be8c56b7ec8 from=translated src=- shape=adc98bc0 vocab=cd921550
-/
theorem one_sub_inv_mul_le_sub_totalBinCount_mul_denseThreshold
    {n R : ℕ} {q : ℝ} (hR : 0 < R) :
    (1 - (R : ℝ)⁻¹) * (n : ℝ) ≤
      ((n - arcsineTotalBinCount n q *
        arcsineDenseThreshold n q R : ℕ) : ℝ) := by
  let B := arcsineTotalBinCount n q
  let T := arcsineDenseThreshold n q R
  have hB : 0 < B := arcsineTotalBinCount_pos n q
  have hBR : 0 < B * R := mul_pos hB hR
  have hmul : T * (B * R) ≤ n := by
    dsimp [T, arcsineDenseThreshold]
    exact Nat.div_mul_le_self n (B * R)
  have hBTdiv : B * T ≤ n / R := by
    apply (Nat.le_div_iff_mul_le hR).2
    simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hBTn : B * T ≤ n := hBTdiv.trans (Nat.div_le_self n R)
  have hcastBT : (B * T : ℝ) ≤ (n : ℝ) / (R : ℝ) := by
    calc
      (B * T : ℝ) ≤ ((n / R : ℕ) : ℝ) := by exact_mod_cast hBTdiv
      _ ≤ (n : ℝ) / (R : ℝ) := by exact Nat.cast_div_le
  rw [show arcsineTotalBinCount n q = B by rfl,
    show arcsineDenseThreshold n q R = T by rfl, Nat.cast_sub hBTn]
  have hRreal : (0 : ℝ) < (R : ℝ) := by exact_mod_cast hR
  rw [inv_eq_one_div]
  have hid : (1 - 1 / (R : ℝ)) * (n : ℝ) =
      (n : ℝ) - (n : ℝ) / (R : ℝ) := by ring
  rw [hid]
  norm_num only [Nat.cast_mul]
  linarith

/-- The further quotient by `L` is one natural division by the product of
all three fixed/logarithmic factors.
@isnad1 id=eq.0h4v.s5.83bb4aa5c350 from=translated src=- shape=afc1391e vocab=903f7744
-/
lemma denseThreshold_div_eq
    (n : ℕ) (q : ℝ) (R L : ℕ) :
    arcsineDenseThreshold n q R / L =
      n / (arcsineTotalBinCount n q * R * L) := by
  rw [arcsineDenseThreshold, Nat.div_div_eq_div_mul]

/-- The harmonic factor at the dense-bin scale retains any prescribed
fraction of `log n`.
@isnad1 id=eventual.4h4v.s6.e92f6ba1d6a1 from=translated src=- shape=069f9900 vocab=f8e7cd3e
-/
theorem eventually_one_sub_mul_log_le_realHarmonic_denseThreshold_div
    {q : ℝ} (hq : 1 < q) {R L : ℕ} (hR : 1 ≤ R) (hL : 1 ≤ L)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      (1 - η) * Real.log (n : ℝ) ≤
        realHarmonic (arcsineDenseThreshold n q R / L) := by
  by_cases hηone : 1 ≤ η
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hlogn : 0 ≤ Real.log (n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hn)
    exact (mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hηone) hlogn).trans
      (realHarmonic_nonneg _)
  · have hηlt : η < 1 := lt_of_not_ge hηone
    have hden := eventually_totalBinCount_mul_fixed_le_rpow hq hη R L
    filter_upwards [eventually_ge_atTop 2, hden] with n hn hden
    let D := arcsineTotalBinCount n q * R * L
    have hD : 0 < D := by
      dsimp [D]
      exact mul_pos
        (mul_pos (arcsineTotalBinCount_pos n q) (Nat.zero_lt_of_lt hR))
        (Nat.zero_lt_of_lt hL)
    have hnpos : 0 < (n : ℝ) := by positivity
    have hDpos : 0 < (D : ℝ) := by exact_mod_cast hD
    have hlogD : Real.log (D : ℝ) ≤ η * Real.log (n : ℝ) := by
      have h := Real.log_le_log hDpos hden
      rw [Real.log_rpow hnpos] at h
      exact h
    have hlogquot :
        (1 - η) * Real.log (n : ℝ) ≤
          Real.log ((n : ℝ) / (D : ℝ)) := by
      rw [Real.log_div (ne_of_gt hnpos) (ne_of_gt hDpos)]
      linarith
    have hharm : Real.log ((n : ℝ) / (D : ℝ)) ≤
        realHarmonic (n / D) := by
      have hy : 0 ≤ (n : ℝ) / (D : ℝ) := by positivity
      have h := log_le_harmonic_floor ((n : ℝ) / (D : ℝ)) hy
      rw [Nat.floor_div_eq_div] at h
      simpa only [realHarmonic] using h
    rw [denseThreshold_div_eq, show
      arcsineTotalBinCount n q * R * L = D by rfl]
    exact hlogquot.trans hharm

end

end ClassicalBound
end Erdos1153
