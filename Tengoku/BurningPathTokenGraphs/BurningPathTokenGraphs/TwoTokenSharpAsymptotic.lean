import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.BaselineAsymptotic
import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.TwoTokenShelfTransfer
import Tengoku.Seed.Analysis.Asymptotics.AsymptoticEquivalent
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Continuity
import Tengoku.Seed.Topology.Order.LiminfLimsup
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sharp two-token asymptotic

The finite shelf cover gives an eventual upper bound. The ceiling and the
shift by two have no effect on the normalized limit, and the resulting limsup
bound matches the exact lower-bound liminf.
-/

open Asymptotics Filter Topology

namespace BurningPath

/-- The burning number of the two-token path graph, normalized by the sharp `n^(2/3)` scale.-/
noncomputable def twoTokenNormalizedBurning (n : ℕ) : ℝ :=
  (pathTokenBurningNumberTotal 2 n : ℝ) / (n : ℝ) ^ (2 / 3 : ℝ)

theorem twoTokenNormalizedBurning_nonneg (n : ℕ) :
    0 ≤ twoTokenNormalizedBurning n := by
  exact div_nonneg (Nat.cast_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/--
The eventual finite shelf inequality, with `N = n - 2`, stated for the
totalized burning number.-/
theorem eventually_twoTokenBurning_le_shelfInitialWidth {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop,
      pathTokenBurningNumberTotal 2 n ≤ shelfInitialWidth ε (n - 2) := by
  have hlarge :=
    (tendsto_sub_atTop_nat 2).eventually (eventually_shelf_large_conditions hε.1)
  filter_upwards [hlarge, eventually_ge_atTop 2] with n hnlarge hn
  rw [pathTokenBurningNumberTotal_eq hn]
  exact
    pathTokenBurningNumber_le_shelfInitialWidth_of_large_conditions
      hε.1 hn hnlarge.1 hnlarge.2

/-- Threshold form of the eventual finite shelf inequality.-/
theorem exists_twoTokenBurning_upper_threshold {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ nε : ℕ, ∀ n ≥ nε,
      pathTokenBurningNumberTotal 2 n ≤ shelfInitialWidth ε (n - 2) := by
  exact eventually_atTop.1 (eventually_twoTokenBurning_le_shelfInitialWidth hε)

/-- Threshold inequality for the actual two-token burning number.-/
theorem exists_twoTokenBurning_upper_threshold_actual {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ nε : ℕ, ∀ n ≥ nε, ∀ hn : 2 ≤ n,
      pathTokenBurningNumber n 2 hn ≤ shelfInitialWidth ε (n - 2) := by
  obtain ⟨nε, hthreshold⟩ := exists_twoTokenBurning_upper_threshold hε
  refine ⟨nε, ?_⟩
  intro n hnε hn
  have htotal := hthreshold n hnε
  rwa [pathTokenBurningNumberTotal_eq hn] at htotal

/-- Subtracting two from the path length has asymptotically negligible relative effect.-/
theorem tendsto_sub_two_div_natCast :
    Tendsto
      (fun n : ℕ ↦ ((n - 2 : ℕ) : ℝ) / (n : ℝ))
      atTop (𝓝 1) := by
  have htwo :
      Tendsto (fun n : ℕ ↦ (2 : ℝ) / (n : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
  have h :
      Tendsto
        (fun n : ℕ ↦ (1 : ℝ) - 2 / (n : ℝ))
        atTop (𝓝 1) :=
    by
      simpa using
        (show Tendsto (fun _ : ℕ ↦ (1 : ℝ)) atTop (𝓝 1) from
          tendsto_const_nhds).sub htwo
  apply h.congr'
  filter_upwards [eventually_ge_atTop 2, eventually_gt_atTop 0] with n hn hnpos
  rw [Nat.cast_sub hn]
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num

/-- The shifted shelf scale divided by the unshifted two-token scale tends to one.-/
theorem tendsto_shelfWidthScale_sub_two_div_twoTokenScale :
    Tendsto
      (fun n : ℕ ↦
        shelfWidthScale (n - 2) / (n : ℝ) ^ (2 / 3 : ℝ))
      atTop (𝓝 1) := by
  have h :=
    Filter.Tendsto.rpow_const tendsto_sub_two_div_natCast
      (p := (2 / 3 : ℝ)) (Or.inl one_ne_zero)
  have h' :
      Tendsto
        (fun n : ℕ ↦
          (((n - 2 : ℕ) : ℝ) / (n : ℝ)) ^ (2 / 3 : ℝ))
        atTop (𝓝 1) := by
    simpa using h
  apply h'.congr'
  filter_upwards with n
  simpa only [shelfWidthScale] using
    (Real.div_rpow
      (show 0 ≤ ((n - 2 : ℕ) : ℝ) by positivity)
      (show 0 ≤ (n : ℝ) by positivity) (2 / 3 : ℝ))

/-- The unrounded global shelf width has the expected shifted sharp-scale limit.-/
theorem tendsto_shelfIdealWidth_sub_two_div_twoTokenScale {ε : ℝ} :
    Tendsto
      (fun n : ℕ ↦
        shelfIdealWidth ε (n - 2) / (n : ℝ) ^ (2 / 3 : ℝ))
      atTop (𝓝 ((1 + ε) * shelfSharpConstant)) := by
  have hconst :
      Tendsto
        (fun _ : ℕ ↦ (1 + ε) * shelfSharpConstant)
        atTop (𝓝 ((1 + ε) * shelfSharpConstant)) :=
    tendsto_const_nhds
  have h :=
    hconst.mul tendsto_shelfWidthScale_sub_two_div_twoTokenScale
  simpa only [shelfIdealWidth, mul_div_assoc, mul_one] using h

/-- Ceiling the global shelf width preserves its shifted sharp-scale limit.-/
theorem tendsto_shelfInitialWidth_sub_two_div_twoTokenScale {ε : ℝ}
    (hε : 0 < ε) :
    Tendsto
      (fun n : ℕ ↦
        (shelfInitialWidth ε (n - 2) : ℝ) /
          (n : ℝ) ^ (2 / 3 : ℝ))
      atTop (𝓝 ((1 + ε) * shelfSharpConstant)) := by
  have hidealTop :
      Tendsto (fun n : ℕ ↦ shelfIdealWidth ε (n - 2)) atTop atTop :=
    (tendsto_shelfIdealWidth_atTop hε).comp (tendsto_sub_atTop_nat 2)
  have hceil :
      Tendsto
        (fun n : ℕ ↦
          (shelfInitialWidth ε (n - 2) : ℝ) /
            shelfIdealWidth ε (n - 2))
        atTop (𝓝 1) := by
    simpa only [shelfInitialWidth, Function.comp_def] using
      (tendsto_nat_ceil_div_atTop (R := ℝ)).comp hidealTop
  have hproduct :=
    hceil.mul
      (tendsto_shelfIdealWidth_sub_two_div_twoTokenScale (ε := ε))
  have heq :
      (fun n : ℕ ↦
        ((shelfInitialWidth ε (n - 2) : ℝ) /
            shelfIdealWidth ε (n - 2)) *
          (shelfIdealWidth ε (n - 2) /
            (n : ℝ) ^ (2 / 3 : ℝ))) =ᶠ[atTop]
        (fun n : ℕ ↦
          (shelfInitialWidth ε (n - 2) : ℝ) /
            (n : ℝ) ^ (2 / 3 : ℝ)) := by
    filter_upwards [hidealTop.eventually_gt_atTop 0, eventually_gt_atTop 0]
      with n hideal hn
    have hscale : (n : ℝ) ^ (2 / 3 : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos (by positivity) _).ne'
    field_simp [hideal.ne', hscale]
  simpa only [one_mul] using hproduct.congr' heq

/-- The finite shelf bound after division by `n^(2/3)`.-/
theorem eventually_twoTokenNormalizedBurning_le_shelfWidthRatio {ε : ℝ}
    (hε : ε ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ᶠ n : ℕ in atTop,
      twoTokenNormalizedBurning n ≤
        (shelfInitialWidth ε (n - 2) : ℝ) /
          (n : ℝ) ^ (2 / 3 : ℝ) := by
  filter_upwards [eventually_twoTokenBurning_le_shelfInitialWidth hε]
    with n hn
  unfold twoTokenNormalizedBurning
  exact div_le_div_of_nonneg_right (by exact_mod_cast hn)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- The normalized two-token burning number has sharp limsup at most `(3/4)^(1/3)`.-/
theorem twoTokenSharpUpper_limsup :
    limsup twoTokenNormalizedBurning atTop ≤ shelfSharpConstant := by
  have hcob :
      atTop.IsCoboundedUnder (· ≤ ·) twoTokenNormalizedBurning :=
    isCoboundedUnder_le_of_le atTop twoTokenNormalizedBurning_nonneg
  apply le_of_forall_pos_le_add
  intro η hη
  let ε : ℝ := min (1 / 2 : ℝ) (η / (2 * shelfSharpConstant))
  have hεpos : 0 < ε := by
    dsimp [ε]
    exact lt_min (by norm_num) (div_pos hη (mul_pos two_pos shelfSharpConstant_pos))
  have hεlt : ε < 1 := by
    dsimp [ε]
    exact (min_le_left _ _).trans_lt (by norm_num)
  have hεc :
      ε * shelfSharpConstant < η := by
    have hle : ε ≤ η / (2 * shelfSharpConstant) := by
      exact min_le_right _ _
    have hc := shelfSharpConstant_pos
    have hmul :=
      mul_le_mul_of_nonneg_right hle hc.le
    have heq :
        η / (2 * shelfSharpConstant) * shelfSharpConstant = η / 2 := by
      field_simp [hc.ne']
    rw [heq] at hmul
    linarith
  have hlimit :
      (1 + ε) * shelfSharpConstant < shelfSharpConstant + η := by
    nlinarith
  have henvelope :=
    (tendsto_shelfInitialWidth_sub_two_div_twoTokenScale hεpos).eventually
      (Iio_mem_nhds hlimit)
  have hupper :=
    eventually_twoTokenNormalizedBurning_le_shelfWidthRatio
      (show ε ∈ Set.Ioo (0 : ℝ) 1 from ⟨hεpos, hεlt⟩)
  exact limsup_le_of_le hcob <|
    (hupper.and henvelope).mono fun _ hn ↦ hn.1.trans hn.2.le

private theorem twoTokenNormalizedBurning_bddAbove :
    atTop.IsBoundedUnder (· ≤ ·) twoTokenNormalizedBurning := by
  let ε : ℝ := 1 / 2
  have hε : ε ∈ Set.Ioo (0 : ℝ) 1 := by
    dsimp [ε]
    norm_num
  have hupper :=
    eventually_twoTokenNormalizedBurning_le_shelfWidthRatio hε
  have henvelope :=
    (tendsto_shelfInitialWidth_sub_two_div_twoTokenScale hε.1).eventually
      (Iio_mem_nhds
        (lt_add_one ((1 + ε) * shelfSharpConstant)))
  refine ⟨(1 + ε) * shelfSharpConstant + 1, ?_⟩
  exact
    (hupper.and henvelope).mono fun _ hn ↦
      hn.1.trans hn.2.le

private theorem twoTokenNormalizedBurning_bddBelow :
    atTop.IsBoundedUnder (· ≥ ·) twoTokenNormalizedBurning := by
  change ∃ b : ℝ, ∀ᶠ n : ℕ in atTop, twoTokenNormalizedBurning n ≥ b
  exact ⟨0, Eventually.of_forall twoTokenNormalizedBurning_nonneg⟩

/-- The normalized two-token burning number converges to the sharp constant.-/
theorem tendsto_twoTokenNormalizedBurning :
    Tendsto twoTokenNormalizedBurning atTop (𝓝 shelfSharpConstant) := by
  apply tendsto_of_le_liminf_of_limsup_le
  · change
      ((3 / 4 : ℝ) ^ (3 : ℝ)⁻¹) ≤
        liminf
          (fun n : ℕ ↦
            (pathTokenBurningNumberTotal 2 n : ℝ) /
              (n : ℝ) ^ (2 / 3 : ℝ))
          atTop
    exact twoTokenLowerAsymptotic_liminf
  · exact twoTokenSharpUpper_limsup
  · exact twoTokenNormalizedBurning_bddAbove
  · exact twoTokenNormalizedBurning_bddBelow

/-- The sharp two-token limit in the common fixed-dimensional ratio notation.-/
theorem tendsto_pathTokenBurningRatio_two :
    Tendsto (pathTokenBurningRatio 2) atTop (𝓝 shelfSharpConstant) := by
  have hfun :
      pathTokenBurningRatio 2 = twoTokenNormalizedBurning := by
    funext n
    rw [pathTokenBurningRatio, pathTokenAsymptoticScale_eq_rpow,
      twoTokenNormalizedBurning]
    norm_num
  rw [hfun]
  exact tendsto_twoTokenNormalizedBurning

/--
Sharp two-token asymptotic equivalence:
`b(F₂(Pₙ)) = (3/4)^(1/3) n^(2/3) + o(n^(2/3))`.-/
theorem twoTokenBurning_isEquivalent_sharp :
    (fun n : ℕ ↦ (pathTokenBurningNumberTotal 2 n : ℝ)) ~[atTop]
      (fun n : ℕ ↦
        shelfSharpConstant * (n : ℝ) ^ (2 / 3 : ℝ)) := by
  apply isEquivalent_of_tendsto_one
  change
    Tendsto
      (fun n : ℕ ↦
        (pathTokenBurningNumberTotal 2 n : ℝ) /
          (shelfSharpConstant * (n : ℝ) ^ (2 / 3 : ℝ)))
      atTop (𝓝 1)
  have hdiv :=
    tendsto_twoTokenNormalizedBurning.div_const shelfSharpConstant
  have hquot :
      (fun n : ℕ ↦
        (pathTokenBurningNumberTotal 2 n : ℝ) /
          (shelfSharpConstant * (n : ℝ) ^ (2 / 3 : ℝ))) =
        (fun n : ℕ ↦
          twoTokenNormalizedBurning n / shelfSharpConstant) := by
    funext n
    by_cases hn : n = 0
    · subst n
      simp [twoTokenNormalizedBurning]
    · have hnpos : 0 < (n : ℝ) := by positivity
      have hscale : (n : ℝ) ^ (2 / 3 : ℝ) ≠ 0 :=
        (Real.rpow_pos_of_pos hnpos _).ne'
      unfold twoTokenNormalizedBurning
      field_simp [twoTokenNormalizedBurning, shelfSharpConstant_pos.ne', hscale]
  rw [hquot]
  simpa only [div_self shelfSharpConstant_pos.ne'] using hdiv

end BurningPath
