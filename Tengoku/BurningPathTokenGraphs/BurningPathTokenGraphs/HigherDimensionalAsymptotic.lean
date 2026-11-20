import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.BaselineAsymptotic
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.DiscreteContinuumComparison
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.HigherDimensionalConstant
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.SimplexDensityLower
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.SimplexDensityUpper
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TwoTokenSharpAsymptotic
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Asymptotics
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Topology.Order.LiminfLimsup
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The higher-dimensional path-token limit

This file proves the fixed-dimensional normalized limit by combining the
ordered-simplex density theorem with the exact discrete-continuum comparisons.
-/

open Filter Topology

namespace BurningPath

/--
The lower simplex-density comparison and the discrete-continuum transfer imply
the powered discrete lower estimate.-/
theorem eventually_density_power_lower (k : ℕ) (hk : 2 ≤ k)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      ((cubeBulkDensity k - η) / Nat.factorial k) *
          ((n - k : ℕ) : ℝ) ^ k ≤
        ((pathTokenBurningNumberTotal k n + k : ℕ) : ℝ) ^ (k + 1) := by
  filter_upwards [eventually_ge_atTop (k + 1),
      (tendsto_pathTokenBurningNumberTotal_atTop k (by omega)).eventually_gt_atTop k]
      with n hn ht
  have hkn : k ≤ n := by omega
  let t := pathTokenBurningNumberTotal k n
  let L := ((n - k : ℕ) : ℝ) / ((t + k : ℕ) : ℝ)
  have hkt : k < t := ht
  have hden : 0 < ((t + k : ℕ) : ℝ) := by positivity
  have hnum : 0 < ((n - k : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - k by omega)
  have hL : 0 < L := div_pos hnum hden
  have hcomparison :
      simplexCoverNumber k L ≤ t + k := by
    dsimp [L, t]
    apply simplexCoverNumber_le_add_of_pathTokenBurningNumber_le hk hkn hkt
    simp [t, pathTokenBurningNumberTotal_eq hkn]
  have hlower := simplexCoverNumber_lower hk hη hL
  have hcomparisonReal :
      (simplexCoverNumber k L : ℝ) ≤ ((t + k : ℕ) : ℝ) := by
    exact_mod_cast hcomparison
  have hchain :
      (cubeBulkDensity k - η) *
          (L ^ k / Nat.factorial k) ≤
        ((t + k : ℕ) : ℝ) :=
    hlower.trans hcomparisonReal
  calc
    ((cubeBulkDensity k - η) / Nat.factorial k) *
          ((n - k : ℕ) : ℝ) ^ k =
        ((cubeBulkDensity k - η) *
            (L ^ k / Nat.factorial k)) *
          ((t + k : ℕ) : ℝ) ^ k := by
      dsimp [L]
      rw [div_pow]
      field_simp [hden.ne']
    _ ≤ ((t + k : ℕ) : ℝ) * ((t + k : ℕ) : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hchain (by positivity)
    _ = ((t + k : ℕ) : ℝ) ^ (k + 1) := by
      rw [pow_succ]
      ring

/-- The endpoint correction `(n-k)/n` tends to one.-/
theorem tendsto_shiftedNatRatio (k : ℕ) :
    Tendsto
      (fun n : ℕ ↦ ((n - k : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
  have hbase :
      Tendsto
        (fun n : ℕ ↦ ((n - k : ℕ) : ℝ) / (n : ℝ))
        atTop (𝓝 1) := by
    have hlimit :
        Tendsto (fun n : ℕ ↦ 1 - (k : ℝ) / (n : ℝ))
          atTop (𝓝 1) := by
      convert tendsto_const_nhds.sub
        (tendsto_const_div_atTop_nhds_zero_nat (k : ℝ)) using 1
      all_goals norm_num
    apply hlimit.congr'
    filter_upwards [eventually_ge_atTop k, eventually_gt_atTop 0] with n hkn hn
    rw [Nat.cast_sub hkn]
    field_simp
  exact hbase

/-- The endpoint correction `(n-k)^k/n^k` tends to one.-/
theorem tendsto_shiftedNatPowerRatio (k : ℕ) :
    Tendsto
      (fun n : ℕ ↦
        ((n - k : ℕ) : ℝ) ^ k / (n : ℝ) ^ k)
      atTop (𝓝 1) := by
  have hbase := tendsto_shiftedNatRatio k
  simpa only [div_pow, one_pow] using hbase.pow k

/-- The additive rank shift in the discrete-continuum transfer is negligible after normalization.-/
theorem tendsto_dimension_div_pathTokenScale (k : ℕ) (hk : 0 < k) :
    Tendsto
      (fun n : ℕ ↦ (k : ℝ) / pathTokenAsymptoticScale k n)
      atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pathTokenAsymptoticScale_atTop k hk)

/-- The integer trial width used for the normalized upper comparison.-/
noncomputable def pathTokenCandidateWidth (k : ℕ) (c : ℝ) (n : ℕ) : ℕ :=
  ⌈c * pathTokenAsymptoticScale k n⌉₊

theorem pathTokenCandidateWidth_spec {k : ℕ} {c : ℝ} (hc : 0 ≤ c) (n : ℕ) :
    c * pathTokenAsymptoticScale k n ≤
        (pathTokenCandidateWidth k c n : ℝ) ∧
      (pathTokenCandidateWidth k c n : ℝ) <
        c * pathTokenAsymptoticScale k n + 1 := by
  constructor
  · exact Nat.le_ceil _
  · rw [pathTokenCandidateWidth]
    apply Nat.ceil_lt_add_one
    exact mul_nonneg hc (pathTokenAsymptoticScale_nonneg k n)

theorem tendsto_pathTokenCandidateWidth_atTop {k : ℕ} (hk : 0 < k)
    {c : ℝ} (hc : 0 < c) :
    Tendsto (pathTokenCandidateWidth k c) atTop atTop := by
  have htarget :
      Tendsto (fun n : ℕ ↦ c * pathTokenAsymptoticScale k n)
        atTop atTop :=
    (tendsto_pathTokenAsymptoticScale_atTop k hk).const_mul_atTop hc
  convert tendsto_nat_ceil_atTop.comp htarget using 1
  funext n
  rfl

theorem tendsto_pathTokenCandidateWidth_div_scale {k : ℕ} (hk : 0 < k)
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        (pathTokenCandidateWidth k c n : ℝ) /
          pathTokenAsymptoticScale k n)
      atTop (𝓝 c) := by
  have herror :
      Tendsto
        (fun n : ℕ ↦ c + 1 / pathTokenAsymptoticScale k n)
        atTop (𝓝 c) := by
    simpa only [add_zero] using tendsto_const_nhds.add
      (tendsto_const_nhds.div_atTop
        (tendsto_pathTokenAsymptoticScale_atTop k hk))
  apply
    tendsto_of_tendsto_of_tendsto_of_le_of_le'
      tendsto_const_nhds herror
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hscale := pathTokenAsymptoticScale_pos (k := k) hn
    exact (le_div_iff₀ hscale).2 (pathTokenCandidateWidth_spec hc.le n).1
  · filter_upwards [eventually_gt_atTop 0] with n hn
    have hscale := pathTokenAsymptoticScale_pos (k := k) hn
    apply (div_le_iff₀ hscale).2
    calc
      (pathTokenCandidateWidth k c n : ℝ) ≤
          c * pathTokenAsymptoticScale k n + 1 :=
        (pathTokenCandidateWidth_spec hc.le n).2.le
      _ = (c + 1 / pathTokenAsymptoticScale k n) *
          pathTokenAsymptoticScale k n := by
        field_simp

theorem tendsto_pathTokenCandidateWidth_sub_div_scale {k : ℕ}
    (hk : 0 < k) {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun n : ℕ ↦
        ((pathTokenCandidateWidth k c n - k : ℕ) : ℝ) /
          pathTokenAsymptoticScale k n)
      atTop (𝓝 c) := by
  have hlimit :=
    (tendsto_pathTokenCandidateWidth_div_scale hk hc).sub
      (tendsto_dimension_div_pathTokenScale k hk)
  have hlimit' :
      Tendsto
        (fun n : ℕ ↦
          (pathTokenCandidateWidth k c n : ℝ) /
              pathTokenAsymptoticScale k n -
            (k : ℝ) / pathTokenAsymptoticScale k n)
        atTop (𝓝 c) := by
    simpa using hlimit
  apply hlimit'.congr'
  filter_upwards [(tendsto_pathTokenCandidateWidth_atTop hk hc).eventually_ge_atTop k]
      with n hn
  rw [Nat.cast_sub hn, sub_div]

private theorem natCast_div_pathTokenScale_eq_rpow {k n : ℕ} (hn : 0 < n) :
    (n : ℝ) / pathTokenAsymptoticScale k n =
      (n : ℝ) ^ ((1 : ℝ) / (k + 1 : ℝ)) := by
  have hnReal : 0 < (n : ℝ) := by positivity
  rw [pathTokenAsymptoticScale_eq_rpow]
  have h :=
    (Real.rpow_sub hnReal (1 : ℝ)
      ((k : ℝ) / (k + 1 : ℝ))).symm
  rw [Real.rpow_one] at h
  have hexp :
      (1 : ℝ) - (k : ℝ) / (k + 1 : ℝ) =
        (1 : ℝ) / (k + 1 : ℝ) := by
    field_simp
    ring
  rw [hexp] at h
  exact h

theorem tendsto_natCast_div_pathTokenScale_atTop (k : ℕ) :
    Tendsto
      (fun n : ℕ ↦ (n : ℝ) / pathTokenAsymptoticScale k n)
      atTop atTop := by
  have hexp : 0 < (1 : ℝ) / (k + 1 : ℝ) := by positivity
  have h :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  apply h.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  exact (natCast_div_pathTokenScale_eq_rpow hn).symm

/-- The simplex side length associated with the trial width.-/
noncomputable def pathTokenCandidateSimplexSide
    (k : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  ((n - k : ℕ) : ℝ) /
    ((pathTokenCandidateWidth k c n - k : ℕ) : ℝ)

theorem tendsto_pathTokenCandidateSimplexSide_atTop {k : ℕ}
    (hk : 0 < k) {c : ℝ} (hc : 0 < c) :
    Tendsto (pathTokenCandidateSimplexSide k c) atTop atTop := by
  have hnumerator :
      Tendsto
        (fun n : ℕ ↦
          (((n - k : ℕ) : ℝ) / (n : ℝ)) *
            ((n : ℝ) / pathTokenAsymptoticScale k n))
        atTop atTop :=
    (tendsto_shiftedNatRatio k).pos_mul_atTop zero_lt_one
      (tendsto_natCast_div_pathTokenScale_atTop k)
  have hdenominator :=
    tendsto_pathTokenCandidateWidth_sub_div_scale hk hc
  have hinverse :
      Tendsto
        (fun n : ℕ ↦
          (((pathTokenCandidateWidth k c n - k : ℕ) : ℝ) /
            pathTokenAsymptoticScale k n)⁻¹)
        atTop (𝓝 c⁻¹) :=
    hdenominator.inv₀ hc.ne'
  have hproduct :
      Tendsto
        (fun n : ℕ ↦
          ((((n - k : ℕ) : ℝ) / (n : ℝ)) *
              ((n : ℝ) / pathTokenAsymptoticScale k n)) *
            ((((pathTokenCandidateWidth k c n - k : ℕ) : ℝ) /
              pathTokenAsymptoticScale k n)⁻¹))
        atTop atTop :=
    hnumerator.atTop_mul_pos (inv_pos.mpr hc) hinverse
  apply hproduct.congr'
  filter_upwards [eventually_gt_atTop 0,
      (tendsto_pathTokenCandidateWidth_atTop hk hc).eventually_gt_atTop k]
      with n hn ht
  rw [pathTokenCandidateSimplexSide]
  have hscale := (pathTokenAsymptoticScale_pos (k := k) hn).ne'
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have ht0 :
      (((pathTokenCandidateWidth k c n - k : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast (show pathTokenCandidateWidth k c n - k ≠ 0 by omega)
  field_simp

/--
Every constant below the variational candidate is eventually a lower bound for the normalized
path-token burning number.-/
theorem eventually_constant_le_pathTokenBurningRatio_of_lt_limit
    (k : ℕ) (hk : 2 ≤ k) {c : ℝ}
    (hc : c < pathTokenLimitConstant k) :
    ∀ᶠ n : ℕ in atTop, c ≤ pathTokenBurningRatio k n := by
  by_cases hc0 : 0 ≤ c
  · let c' := (c + pathTokenLimitConstant k) / 2
    have hcc' : c < c' := by
      dsimp [c']
      linarith
    have hc'C : c' < pathTokenLimitConstant k := by
      dsimp [c']
      linarith
    have hc'0 : 0 ≤ c' := hc0.trans hcc'.le
    have hpower :
        c' ^ (k + 1) <
          cubeBulkDensity k / Nat.factorial k := by
      rw [← pathTokenLimitConstant_pow hk]
      exact
        (pow_lt_pow_iff_left₀ hc'0 (pathTokenLimitConstant_pos hk).le
          (by omega)).2 hc'C
    let d :=
      (c' ^ (k + 1) +
        cubeBulkDensity k / Nat.factorial k) / 2
    have hc'd : c' ^ (k + 1) < d := by
      dsimp [d]
      linarith
    have hdC : d < cubeBulkDensity k / Nat.factorial k := by
      dsimp [d]
      linarith
    let η := cubeBulkDensity k - d * Nat.factorial k
    have hη : 0 < η := by
      dsimp [η]
      have hfac : (0 : ℝ) < Nat.factorial k := by positivity
      apply sub_pos.mpr
      exact (lt_div_iff₀ hfac).mp hdC
    have hcoefficient :
        (cubeBulkDensity k - η) / Nat.factorial k = d := by
      dsimp [η]
      field_simp
      ring
    have hratio :
        Tendsto
          (fun n : ℕ ↦
            d * (((n - k : ℕ) : ℝ) ^ k / (n : ℝ) ^ k))
          atTop (𝓝 d) := by
      simpa only [mul_one] using
        tendsto_const_nhds.mul (tendsto_shiftedNatPowerRatio k)
    have hratioLower :
        ∀ᶠ n : ℕ in atTop,
          c' ^ (k + 1) ≤
            d * (((n - k : ℕ) : ℝ) ^ k / (n : ℝ) ^ k) :=
      (hratio.eventually (Ioi_mem_nhds hc'd)).mono fun _ hn ↦ hn.le
    have hshiftSmall :
        ∀ᶠ n : ℕ in atTop,
          (k : ℝ) / pathTokenAsymptoticScale k n ≤ c' - c := by
      have hpos : 0 < c' - c := sub_pos.mpr hcc'
      exact
        ((tendsto_dimension_div_pathTokenScale k (by omega)).eventually
          (Iio_mem_nhds hpos)).mono fun _ hn ↦ hn.le
    filter_upwards [eventually_density_power_lower k hk hη,
        hratioLower, hshiftSmall, eventually_gt_atTop 0] with
        n hdensity hratioN hshift hn
    have hscale : 0 < pathTokenAsymptoticScale k n :=
      pathTokenAsymptoticScale_pos hn
    have hnPow : 0 < (n : ℝ) ^ k := by positivity
    have hnormalized :
        c' ^ (k + 1) * (n : ℝ) ^ k ≤
          d * ((n - k : ℕ) : ℝ) ^ k := by
      calc
        c' ^ (k + 1) * (n : ℝ) ^ k ≤
            (d * (((n - k : ℕ) : ℝ) ^ k / (n : ℝ) ^ k)) *
              (n : ℝ) ^ k :=
          mul_le_mul_of_nonneg_right hratioN hnPow.le
        _ = d * ((n - k : ℕ) : ℝ) ^ k := by
          field_simp
    have hpowers :
        (c' * pathTokenAsymptoticScale k n) ^ (k + 1) ≤
          ((pathTokenBurningNumberTotal k n + k : ℕ) : ℝ) ^ (k + 1) := by
      rw [mul_pow, pathTokenAsymptoticScale_pow]
      exact hnormalized.trans (by simpa [hcoefficient] using hdensity)
    have hbases :
        c' * pathTokenAsymptoticScale k n ≤
          ((pathTokenBurningNumberTotal k n + k : ℕ) : ℝ) := by
      exact
        (pow_le_pow_iff_left₀ (mul_nonneg hc'0 hscale.le) (by positivity)
          (by omega)).mp hpowers
    have hshifted :
        c' ≤
          ((pathTokenBurningNumberTotal k n + k : ℕ) : ℝ) /
            pathTokenAsymptoticScale k n :=
      (le_div_iff₀ hscale).2 hbases
    rw [pathTokenBurningRatio]
    push_cast at hshifted
    rw [add_div] at hshifted
    linarith
  · have hcneg : c < 0 := lt_of_not_ge hc0
    exact Eventually.of_forall fun n ↦
      hcneg.le.trans (pathTokenBurningRatio_nonneg k n)

/-- Real-valued liminf lower bound for the normalized burning number.-/
theorem pathTokenLimitConstant_le_liminf (k : ℕ) (hk : 2 ≤ k) :
    pathTokenLimitConstant k ≤ liminf (pathTokenBurningRatio k) atTop := by
  have hupper :
      ∀ᶠ n in atTop,
        pathTokenBurningRatio k n ≤ generalUpperConstant k + 1 :=
    eventually_pathTokenBurningRatio_le_generalUpperConstant_add
      k (by omega) (by norm_num)
  have hcob :
      atTop.IsCoboundedUnder (· ≥ ·) (pathTokenBurningRatio k) :=
    isCoboundedUnder_ge_of_eventually_le atTop hupper
  have hbdd :
      atTop.IsBoundedUnder (· ≥ ·) (pathTokenBurningRatio k) := by
    change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, pathTokenBurningRatio k n ≥ b
    exact ⟨0, Eventually.of_forall (pathTokenBurningRatio_nonneg k)⟩
  apply (le_liminf_iff' hcob hbdd).2
  intro c hc
  exact eventually_constant_le_pathTokenBurningRatio_of_lt_limit k hk hc

/-- Variational formula for the candidate limit, with the cube infimum expanded.-/
theorem pathTokenLimitConstant_variational_formula (k : ℕ) :
    pathTokenLimitConstant k =
      ((1 / (Nat.factorial k : ℝ)) *
        sInf {x : ℝ | ∃ L : ℝ, 0 < L ∧
          x = (cubeCoverNumber k L : ℝ) / L ^ k}) ^
        (k + 1 : ℝ)⁻¹ := by
  rw [pathTokenLimitConstant, cubeBulkDensity]
  apply congrArg (fun x : ℝ ↦ x ^ (k + 1 : ℝ)⁻¹)
  rw [div_eq_mul_inv, one_div, mul_comm]

/-- Explicit two-sided bounds re-exported at the asymptotic layer.-/
theorem higherDimensionalConstant_bounds (k : ℕ) (hk : 2 ≤ k) :
    (((k + 1 : ℝ) / (2 : ℝ) ^ k) ^ (k + 1 : ℝ)⁻¹) ≤
        pathTokenLimitConstant k ∧
      pathTokenLimitConstant k ≤
        ((((k + 1 : ℕ) : ℝ) ^ (k + 1) /
          ((2 : ℝ) ^ k * Nat.factorial k)) ^
            (k + 1 : ℝ)⁻¹) :=
  pathTokenLimitConstant_bounds hk

/-- Once the matching limsup inequality is supplied, the real normalized sequence converges.-/
theorem tendsto_pathTokenBurningRatio_of_limsup_le (k : ℕ) (hk : 2 ≤ k)
    (hupper :
      limsup (pathTokenBurningRatio k) atTop ≤ pathTokenLimitConstant k) :
    Tendsto (pathTokenBurningRatio k) atTop
      (𝓝 (pathTokenLimitConstant k)) := by
  have hboundedAbove :
      atTop.IsBoundedUnder (· ≤ ·) (pathTokenBurningRatio k) := by
    change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, pathTokenBurningRatio k n ≤ b
    exact
      ⟨generalUpperConstant k + 1,
        eventually_pathTokenBurningRatio_le_generalUpperConstant_add
          k (by omega) (by norm_num)⟩
  have hboundedBelow :
      atTop.IsBoundedUnder (· ≥ ·) (pathTokenBurningRatio k) := by
    change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, pathTokenBurningRatio k n ≥ b
    exact ⟨0, Eventually.of_forall (pathTokenBurningRatio_nonneg k)⟩
  exact
    tendsto_of_le_liminf_of_limsup_le
      (pathTokenLimitConstant_le_liminf k hk) hupper
      hboundedAbove hboundedBelow

/-- The sharp two-token limit determines the exact two-dimensional bulk density.-/
theorem cubeBulkDensity_two :
    cubeBulkDensity 2 = (3 / 2 : ℝ) := by
  have hcandidate :
      pathTokenLimitConstant 2 ≤ shelfSharpConstant := by
    rw [← tendsto_pathTokenBurningRatio_two.liminf_eq]
    exact pathTokenLimitConstant_le_liminf 2 (by omega)
  have hpow :
      pathTokenLimitConstant 2 ^ 3 ≤ shelfSharpConstant ^ 3 :=
    (pow_le_pow_iff_left₀ (pathTokenLimitConstant_pos (by omega)).le
      shelfSharpConstant_pos.le (by norm_num : (3 : ℕ) ≠ 0)).2 hcandidate
  have hupper : cubeBulkDensity 2 ≤ (3 / 2 : ℝ) := by
    rw [pathTokenLimitConstant_pow (by omega),
      shelfSharpConstant_pow_three] at hpow
    norm_num at hpow ⊢
    linarith
  have hlower := cubeBulkDensity_lower (k := 2) (by omega)
  norm_num at hlower
  exact le_antisymm hupper hlower

end BurningPath
