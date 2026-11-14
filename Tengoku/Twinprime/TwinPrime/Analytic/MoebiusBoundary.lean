import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusAbel
import Tengoku.Twinprime.TwinPrime.Analytic.MoebiusHyperbola
import Tengoku.Seed.NumberTheory.Harmonic.EulerMascheroni

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The elementary boundary constant for smoothed Möbius sums

The convolution identity supplies the constant. Quantitative ordinary Mertens
cancellation controls the harmonic remainder by finite Abel summation.
No absolute summability of `μ(n)/n` is assumed.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped Topology ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

theorem sum_reciprocalNat_Ioc (N : ℕ) :
    (∑ n ∈ Ioc 0 N, reciprocalNat n) = (harmonic N : ℝ) := by
  have hI : Ioc 0 N = Icc 1 N := by ext n; simp only [mem_Ioc, mem_Icc]; omega
  simp [hI, harmonic_eq_sum_Icc, one_div]

/-- The finite identity which fixes the boundary constant at one.-/
theorem normalizedMoebius_harmonic_sum (X : ℕ) (hX : 1 ≤ X) :
    (∑ d ∈ Ioc 0 X, normalizedMoebius d * (harmonic (X / d) : ℝ)) = 1 := by
  have h := sum_Ioc_mul_eq_sum_sum normalizedMoebius reciprocalNat X
  have hconv : normalizedMoebius * reciprocalNat = 1 := by
    rw [mul_comm, reciprocalNat_mul_normalizedMoebius]
  rw [hconv] at h
  simp_rw [sum_reciprocalNat_Ioc] at h
  simpa [ArithmeticFunction.one_apply, hX] using h.symm

def harmonicRemainder (X d : ℕ) : ℝ :=
  (harmonic (X / d) : ℝ) - Real.log ((X : ℝ) / d) - Real.eulerMascheroniConstant

private theorem harmonicReal_mono : Monotone (fun n : ℕ => (harmonic n : ℝ)) := by
  apply monotone_nat_of_le_succ
  intro n
  rw [harmonic_succ, Rat.cast_add]
  have h : (0 : ℝ) ≤ (((n + 1 : ℕ) : ℚ)⁻¹ : ℚ) := by positivity
  linarith

private theorem quotient_bounds (X d : ℕ) (hd : 0 < d) :
    (X / d : ℕ) ≤ (X : ℝ) / d ∧ (X : ℝ) / d < (X / d : ℕ) + 1 := by
  have hdr : (0 : ℝ) < d := by exact_mod_cast hd
  constructor
  · rw [le_div_iff₀ hdr]
    exact_mod_cast Nat.div_mul_le_self X d
  · rw [div_lt_iff₀ hdr]
    have h := Nat.mod_lt X hd
    have he := Nat.mod_add_div X d
    exact_mod_cast (show X < (X / d + 1) * d by nlinarith)

/-- Uniform harmonic approximation, retaining the real quotient in the log.-/
theorem abs_harmonicRemainder_le (X d : ℕ) (hd : 1 ≤ d) (hdX : d ≤ X) :
    |harmonicRemainder X d| ≤ 2 * d / X := by
  let q := X / d
  have hq : 1 ≤ q := (Nat.le_div_iff_mul_le (by omega)).mpr (by simpa using hdX)
  have hqr : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hdr : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
  have hXr : (0 : ℝ) < X := hdr.trans_le (by exact_mod_cast hdX)
  obtain ⟨hlo, hhi⟩ := quotient_bounds X d (by omega)
  change (q : ℝ) ≤ (X : ℝ) / d at hlo
  change (X : ℝ) / d < (q : ℝ) + 1 at hhi
  have hl : Real.log (q : ℝ) ≤ Real.log ((X : ℝ) / d) :=
    Real.log_le_log hqr hlo
  have hu : Real.log ((X : ℝ) / d) ≤ Real.log ((q : ℝ) + 1) :=
    Real.log_le_log (div_pos hXr hdr) hhi.le
  have hinc : Real.log ((q : ℝ) + 1) - Real.log q ≤ 1 / (q : ℝ) := by
    have h := Real.log_le_sub_one_of_pos (div_pos (by linarith : (0 : ℝ) < q + 1) hqr)
    rw [Real.log_div (by positivity : (q : ℝ) + 1 ≠ 0) hqr.ne'] at h
    convert h using 1
    field_simp
    ring
  have hγlo := Real.eulerMascheroniSeq_lt_eulerMascheroniConstant q
  have hγhi := Real.eulerMascheroniConstant_lt_eulerMascheroniSeq' q
  simp only [Real.eulerMascheroniSeq, Real.eulerMascheroniSeq',
    show q ≠ 0 by omega, ite_false] at hγlo hγhi
  have hrem : |harmonicRemainder X d| ≤ 1 / (q : ℝ) := by
    rw [abs_le]
    unfold harmonicRemainder
    change -(1 / (q : ℝ)) ≤ (harmonic q : ℝ) - Real.log ((X : ℝ) / d) -
        Real.eulerMascheroniConstant ∧
      (harmonic q : ℝ) - Real.log ((X : ℝ) / d) - Real.eulerMascheroniConstant ≤ 1 / q
    constructor <;> linarith
  apply hrem.trans
  apply (div_le_div_iff₀ hqr hXr).mpr
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hh : (X : ℝ) / d ≤ 2 * q := by linarith
  have hh' := (div_le_iff₀ hdr).mp hh
  nlinarith

/-- Both harmonic and logarithmic pieces decrease with the divisor variable;
their separate variations telescope.-/
theorem harmonicRemainder_variation_le (X a : ℕ) (ha : 1 ≤ a) (haX : a ≤ X) :
    (∑ t ∈ Ico a X, |harmonicRemainder X (t + 1) - harmonicRemainder X t|) ≤
      2 * Real.log X := by
  let H : ℕ → ℝ := fun d => (harmonic (X / d) : ℝ)
  let J : ℕ → ℝ := fun d => Real.log ((X : ℝ) / d)
  have hXr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hstep (t : ℕ) (ht : t ∈ Ico a X) :
      |harmonicRemainder X (t + 1) - harmonicRemainder X t| ≤
        (H t - H (t + 1)) + (J t - J (t + 1)) := by
    obtain ⟨hat, htX⟩ := mem_Ico.mp ht
    have ht0 : 0 < t := by omega
    have hH : H (t + 1) ≤ H t := harmonicReal_mono (Nat.div_le_div_left (Nat.le_succ t) ht0)
    have hJ : J (t + 1) ≤ J t := by
      apply Real.log_le_log
      · exact div_pos hXr (by positivity)
      · exact div_le_div_of_nonneg_left hXr.le (by exact_mod_cast ht0)
          (by exact_mod_cast Nat.le_succ t)
    have heq : harmonicRemainder X (t + 1) - harmonicRemainder X t =
        (H (t + 1) - H t) - (J (t + 1) - J t) := by
      dsimp [harmonicRemainder, H, J]
      ring
    rw [heq]
    calc
      _ ≤ |H (t + 1) - H t| + |J (t + 1) - J t| := abs_sub _ _
      _ = _ := by rw [abs_of_nonpos (sub_nonpos.mpr hH), abs_of_nonpos (sub_nonpos.mpr hJ)]; ring
  have htel (f : ℕ → ℝ) :
      (∑ t ∈ Ico a X, (f t - f (t + 1))) = f a - f X := by
    have h := congrArg Neg.neg (sum_Ico_sub f haX)
    simpa only [← sum_neg_distrib, neg_sub] using h
  have hHa : H a ≤ 1 + Real.log X := by
    apply (harmonic_le_one_add_log (X / a)).trans
    have hq : 0 < X / a := Nat.div_pos haX (by omega)
    have hlog : Real.log (X / a : ℕ) ≤ Real.log (X : ℝ) :=
      Real.log_le_log (by exact_mod_cast hq) (by exact_mod_cast Nat.div_le_self X a)
    linarith
  have hJa : J a ≤ Real.log X := by
    apply Real.log_le_log (div_pos hXr (by exact_mod_cast (show 0 < a by omega)))
    exact div_le_self hXr.le (by exact_mod_cast ha)
  calc
    _ ≤ ∑ t ∈ Ico a X, ((H t - H (t + 1)) + (J t - J (t + 1))) := sum_le_sum hstep
    _ = (H a - H X) + (J a - J X) := by rw [sum_add_distrib, htel H, htel J]
    _ ≤ _ := by
      have hHX : H X = 1 := by simp [H, Nat.div_self (by omega : 0 < X)]
      have hJX : J X = 0 := by simp [J]
      rw [hHX, hJX]
      linarith

/-- Exact decomposition of the normalized convolution into smoothing and its
harmonic remainder.-/
theorem smoothedMoebiusSum_add_harmonicRemainder (X : ℕ) (hX : 1 ≤ X) :
    smoothedMoebiusSum X + Real.eulerMascheroniConstant * normalizedMoebiusSum X +
      (∑ d ∈ Ioc 0 X, normalizedMoebius d * harmonicRemainder X d) = 1 := by
  rw [← normalizedMoebius_harmonic_sum X hX]
  unfold smoothedMoebiusSum normalizedMoebiusSum
  rw [Nat.floor_natCast, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
  apply sum_congr rfl
  intro d hd
  unfold harmonicRemainder
  ring

def moebiusHarmonicError (X : ℕ) : ℝ :=
  ∑ d ∈ Ioc 0 X, normalizedMoebius d * harmonicRemainder X d

/-- A finite split into a short absolutely bounded head and an Abel-controlled
tail. Only ordinary Mertens sums on the displayed interval are used.-/
theorem abs_moebiusHarmonicError_le (X a : ℕ) (ha : 2 ≤ a) (haX : a ≤ X)
    (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ t ∈ Icc a X, |mertensSum t| ≤ K * t / (Real.log t) ^ 6) :
    |moebiusHarmonicError X| ≤ 2 * a / X +
      (((32 + 2 / Real.log 2) * K) / (Real.log a) ^ 5) * (2 + 2 * Real.log X) := by
  let E : ℝ := ((32 + 2 / Real.log 2) * K) / (Real.log a) ^ 5
  have hEa : 0 ≤ E := by
    dsimp [E]
    have : 0 < Real.log (a : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < a by omega))
    positivity
  have hXr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hhead : |∑ d ∈ Ioc 0 a, normalizedMoebius d * harmonicRemainder X d| ≤
      2 * a / X := by
    calc
      _ ≤ ∑ d ∈ Ioc 0 a, |normalizedMoebius d * harmonicRemainder X d| :=
        abs_sum_le_sum_abs _ _
      _ ≤ ∑ _d ∈ Ioc 0 a, (2 / (X : ℝ)) := by
        apply sum_le_sum
        intro d hd
        obtain ⟨hd0, hda⟩ := mem_Ioc.mp hd
        have hdr : (0 : ℝ) < d := by exact_mod_cast hd0
        have hμ : |(μ d : ℝ)| ≤ 1 := by exact_mod_cast (abs_moebius_le_one (n := d))
        have hμd : |normalizedMoebius d| ≤ 1 / (d : ℝ) := by
          rw [normalizedMoebius_apply, abs_div, abs_of_pos hdr]
          exact div_le_div_of_nonneg_right hμ hdr.le
        rw [abs_mul]
        calc
          _ ≤ (1 / (d : ℝ)) * (2 * d / X) :=
            mul_le_mul hμd (abs_harmonicRemainder_le X d hd0 (hda.trans haX))
              (abs_nonneg _) (by positivity)
          _ = _ := by field_simp
      _ = _ := by simp; ring
  have htailE (t : ℕ) (ht : t ∈ Icc a X) :
      |∑ d ∈ Ioc a t, normalizedMoebius d| ≤ E := by
    obtain ⟨hat, htX⟩ := mem_Icc.mp ht
    have hs := sum_Ioc_consecutive normalizedMoebius (Nat.zero_le a) hat
    have heq : (∑ d ∈ Ioc a t, normalizedMoebius d) =
        normalizedMoebiusSum t - normalizedMoebiusSum a := by
      unfold normalizedMoebiusSum
      linarith
    rw [heq]
    apply reciprocalCoefficientSum_tail_le_log_five (fun n => (μ n : ℝ)) a t ha hat K hK
    intro u hu
    exact hM u (mem_Icc.mpr ⟨(mem_Icc.mp hu).1, (mem_Icc.mp hu).2.trans htX⟩)
  have htail : |∑ d ∈ Ioc a X, normalizedMoebius d * harmonicRemainder X d| ≤
      E * (2 + 2 * Real.log X) := by
    have h := abs_sum_Ioc_mul_le_total_variation a X haX
      (harmonicRemainder X) normalizedMoebius E htailE
    have hR : |harmonicRemainder X X| ≤ 2 := by
      have h := abs_harmonicRemainder_le X X (by omega) le_rfl
      simpa [hXr.ne', mul_div_assoc] using h
    have hvar := harmonicRemainder_variation_le X a (by omega) haX
    have h' : |∑ d ∈ Ioc a X, normalizedMoebius d * harmonicRemainder X d| ≤
        E * (|harmonicRemainder X X| +
          ∑ t ∈ Ico a X, |harmonicRemainder X (t + 1) - harmonicRemainder X t|) := by
      simpa only [mul_comm] using h
    exact h'.trans (mul_le_mul_of_nonneg_left (add_le_add hR hvar) hEa)
  have hsplit := sum_Ioc_consecutive
    (fun d => normalizedMoebius d * harmonicRemainder X d) (Nat.zero_le a) haX
  unfold moebiusHarmonicError
  rw [← hsplit]
  exact (abs_add_le _ _).trans (add_le_add hhead htail)

/-- The harmonic remainder tends to zero under ordinary quantitative Mertens
cancellation. The cutoff is only an auxiliary elementary fifth-root split.-/
theorem tendsto_moebiusHarmonicError_of_mertens_log_six (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6) :
    Tendsto moebiusHarmonicError atTop (𝓝 0) := by
  let C : ℝ := (32 + 2 / Real.log 2) * K
  let D : ℝ := 2 / Real.log 2 + 28
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hU : Tendsto (fun X : ℕ => (primaryCutoff X : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp tendsto_primaryCutoff
  have hlogU := Real.tendsto_log_atTop.comp hU
  have hupper : Tendsto (fun X : ℕ => 2 / (primaryCutoff X : ℝ) +
      (C * D) / (Real.log (primaryCutoff X)) ^ 4) atTop (𝓝 0) := by
    have h₁ := hU.inv_tendsto_atTop.const_mul 2
    have h₂ := (hlogU.inv_tendsto_atTop.pow 4).const_mul (C * D)
    simpa [div_eq_mul_inv, inv_pow] using h₁.add h₂
  obtain ⟨N, hN⟩ := eventually_atTop.mp hM
  rw [tendsto_zero_iff_abs_tendsto_zero]
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
  · filter_upwards with X
    exact abs_nonneg _
  · filter_upwards [eventually_ge_atTop 32,
      tendsto_primaryCutoff.eventually (eventually_ge_atTop N)] with X hX hUN
    let U := primaryCutoff X
    have hU2 : 2 ≤ U := primaryCutoff_two_le hX
    have hUX : U ≤ X := primaryCutoff_le (by omega)
    have hUr : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
    have hXr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
    have hlogUr : 0 < Real.log (U : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < U by omega))
    have hUlog2 : Real.log (2 : ℝ) ≤ Real.log U :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hU2)
    have hlogU1 : Real.log ((U : ℝ) + 1) ≤ 2 * Real.log U := by
      calc
        _ ≤ Real.log ((U : ℝ) ^ (2 : ℕ)) := Real.log_le_log (by positivity) (by
          have h : (2 : ℝ) ≤ U := by exact_mod_cast hU2
          nlinarith [sq_nonneg ((U : ℝ) - 2)])
        _ = _ := by rw [Real.log_pow]; norm_num
    have hlogX : Real.log (X : ℝ) ≤ 14 * Real.log U := by
      have h₁ : Real.log (X : ℝ) ≤ Real.log (2 * X + 2) :=
        Real.log_le_log hXr (by linarith)
      have h₂ := log_dyadic_le_seven_log_primaryCutoff X (by omega)
      change Real.log (2 * X + 2) ≤ 7 * Real.log ((U : ℝ) + 1) at h₂
      linarith
    have hweight : 2 + 2 * Real.log (X : ℝ) ≤ D * Real.log U := by
      have htwo : 2 ≤ (2 / Real.log 2) * Real.log U := by
        calc
          2 = (2 / Real.log 2) * Real.log 2 := by field_simp
          _ ≤ _ := mul_le_mul_of_nonneg_left hUlog2 (by positivity)
      dsimp [D]
      nlinarith
    have hUsq : U ^ 2 ≤ X :=
      (pow_le_pow_right₀ (by omega : 1 ≤ U) (by decide : 2 ≤ 5)).trans
        (primaryCutoff_pow_five_le X)
    have hhead : 2 * (U : ℝ) / X ≤ 2 / (U : ℝ) := by
      apply (div_le_div_iff₀ hXr hUr).mpr
      have h : (U : ℝ) ^ 2 ≤ X := by exact_mod_cast hUsq
      nlinarith
    have htail : (C / (Real.log U) ^ 5) * (2 + 2 * Real.log X) ≤
        (C * D) / (Real.log U) ^ 4 := by
      calc
        _ ≤ (C / (Real.log U) ^ 5) * (D * Real.log U) :=
          mul_le_mul_of_nonneg_left hweight (by positivity)
        _ = _ := by field_simp
    have hfinite := abs_moebiusHarmonicError_le X U hU2 hUX K hK
      (fun t ht => hN t (hUN.trans (mem_Icc.mp ht).1))
    exact hfinite.trans (add_le_add hhead htail)

/-- The finite convolution and the harmonic error identify the integer
smoothed boundary constant.-/
theorem tendsto_smoothedMoebiusSum_nat_of_mertens_and_zero (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6)
    (hzero : Tendsto normalizedMoebiusSum atTop (𝓝 0)) :
    Tendsto (fun X : ℕ => smoothedMoebiusSum X) atTop (𝓝 1) := by
  have hE := tendsto_moebiusHarmonicError_of_mertens_log_six K hK hM
  have hS := hzero.const_mul Real.eulerMascheroniConstant
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub
    (hS.add hE)
  norm_num only [mul_zero, add_zero, sub_zero] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have heq := smoothedMoebiusSum_add_harmonicRemainder X hX
  change smoothedMoebiusSum X + Real.eulerMascheroniConstant * normalizedMoebiusSum X +
    moebiusHarmonicError X = 1 at heq
  linarith

/-- The ordinary logarithmic Möbius moment has constant `-1`; that constant
is proved from the convolution and is not an independent hypothesis.-/
theorem tendsto_moebiusLogMoment_of_mertens_and_zero (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6)
    (hzero : Tendsto normalizedMoebiusSum atTop (𝓝 0)) :
    Tendsto moebiusLogMoment atTop (𝓝 (-1)) := by
  have hlog := tendsto_log_mul_floor_of_mul_log_sq normalizedMoebiusSum
    (tendsto_normalizedMoebiusSum_mul_log_sq_of_mertens_log_six K hK hM hzero)
  have hlogNat := hlog.comp tendsto_natCast_atTop_atTop
  simp only [Function.comp_def, Nat.floor_natCast] at hlogNat
  have h := hlogNat.sub (tendsto_smoothedMoebiusSum_nat_of_mertens_and_zero K hK hM hzero)
  norm_num only [zero_sub] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop 1] with X hX
  have heq := smoothedMoebiusSum_eq_log_mul_sub_moment
    (by exact_mod_cast (show 0 < X by omega) : (0 : ℝ) < X)
  rw [Nat.floor_natCast] at heq
  linarith

/-- The real-endpoint smoothing limit, derived from quantitative ordinary
Mertens cancellation and the reciprocal limit zero, with no moment assumption.-/
theorem tendsto_smoothedMoebiusSum_of_mertens_and_zero (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6)
    (hzero : Tendsto normalizedMoebiusSum atTop (𝓝 0)) :
    Tendsto smoothedMoebiusSum atTop (𝓝 1) :=
  tendsto_smoothedMoebiusSum_of_ordinary_inputs K hK hM hzero
    (tendsto_moebiusLogMoment_of_mertens_and_zero K hK hM hzero)

/-- Quantitative ordinary Mertens cancellation alone supplies the moment
constant, with the reciprocal normalization discharged by the hyperbola lemma.-/
theorem tendsto_moebiusLogMoment_of_mertens_log_six (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6) :
    Tendsto moebiusLogMoment atTop (𝓝 (-1)) :=
  tendsto_moebiusLogMoment_of_mertens_and_zero K hK hM
    (tendsto_normalizedMoebiusSum_of_mertens_log_six K hK hM)

/-- The classical smoothed normalization follows from the ordinary quantitative
Mertens hypothesis; no limit constant is left as an additional premise.-/
theorem tendsto_smoothedMoebiusSum_of_mertens_log_six (K : ℝ) (hK : 0 ≤ K)
    (hM : ∀ᶠ t : ℕ in atTop, |mertensSum t| ≤ K * t / (Real.log t) ^ 6) :
    Tendsto smoothedMoebiusSum atTop (𝓝 1) :=
  tendsto_smoothedMoebiusSum_of_mertens_and_zero K hK hM
    (tendsto_normalizedMoebiusSum_of_mertens_log_six K hK hM)

end TwinPrime.Analytic
