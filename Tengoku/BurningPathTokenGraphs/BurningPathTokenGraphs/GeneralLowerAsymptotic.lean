import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetricGraphLower
import Tengoku.Seed.Analysis.SpecialFunctions.Choose
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Topology.Order.LiminfLimsup
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The fixed-dimensional asymptotic volume lower bound

This file derives part (A)'s sharp fixed-`k` liminf constant from the exact ranked-volume
threshold lower bound.
-/

open Asymptotics Filter Topology

namespace BurningPath

/-- The sum of the coefficients of the lower-degree terms in the ranked volume polynomial.-/
def lowerRankedVolumeCoefficient (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.range k, 2 ^ j * k.choose j

/-- The ranked volume polynomial is monotone in its length argument.
@isnad1 id=monotone.0h1v.s3.576e7fb5befa from=translated src=- shape=f736e2c1 vocab=c2992715
-/
theorem rankedVolumePolynomial_mono (k : ℕ) :
    Monotone (rankedVolumePolynomial k) := by
  intro a b hab
  unfold rankedVolumePolynomial
  apply Finset.sum_le_sum
  intro j hj
  exact Nat.mul_le_mul_left _ (Nat.choose_le_choose (j + 1) hab)

/--
The top-degree summand is kept exact, while all lower-degree summands are bounded by a fixed
coefficient times `t^k`.
@isnad1 id=le.1h2v.s6.6b00fd1b7407 from=translated src=- shape=c4f281b8 vocab=5dfbb835
-/
theorem rankedVolumePolynomial_le_lower_add_leading (k t : ℕ) (ht : 1 ≤ t) :
    rankedVolumePolynomial k t ≤
      lowerRankedVolumeCoefficient k * t ^ k + 2 ^ k * t.choose (k + 1) := by
  unfold rankedVolumePolynomial lowerRankedVolumeCoefficient
  rw [Finset.sum_range_succ]
  simp only [Nat.choose_self, mul_one]
  apply Nat.add_le_add_right
  calc
    ∑ j ∈ Finset.range k, 2 ^ j * k.choose j * t.choose (j + 1) ≤
        ∑ j ∈ Finset.range k, (2 ^ j * k.choose j) * t ^ k := by
      apply Finset.sum_le_sum
      intro j hj
      apply Nat.mul_le_mul_left
      exact (Nat.choose_le_pow t (j + 1)).trans <|
        Nat.pow_le_pow_right (by omega) (by simpa using Finset.mem_range.mp hj)
    _ = (∑ j ∈ Finset.range k, 2 ^ j * k.choose j) * t ^ k := by
      rw [Finset.sum_mul]

/-- The exact threshold inequality holds at the path-token burning number itself.
@isnad1 id=le.1h2v.s4.4be322797123 from=translated src=- shape=ac80b1a6 vocab=560a76b2
-/
theorem choose_le_rankedVolumePolynomial_pathToken {n k : ℕ} (hk : k ≤ n) :
    n.choose k ≤ rankedVolumePolynomial k (pathTokenBurningNumberTotal k n) := by
  rw [pathTokenBurningNumberTotal_eq hk]
  exact (volumeThreshold_spec k (n.choose k)).2.trans <|
    rankedVolumePolynomial_mono k (pathToken_volumeThreshold_lower_of_le hk)

/-- For positive fixed dimension, `choose n k` tends to infinity.
@isnad1 id=tendsto.1h1v.s4.4deb9616d7f0 from=translated src=- shape=57bb9501 vocab=9f3ebfc1
-/
theorem tendsto_choose_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (fun n : ℕ ↦ n.choose k) atTop atTop := by
  rw [← tendsto_natCast_atTop_iff (R := ℝ)]
  apply (isEquivalent_choose k).symm.tendsto_atTop
  have hpow : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ k) atTop atTop :=
    (tendsto_pow_atTop (α := ℝ) hk.ne').comp tendsto_natCast_atTop_atTop
  exact hpow.atTop_div_const (by positivity : (0 : ℝ) < k.factorial)

/-- The usual fixed-`k` normalization of the binomial coefficient.
@isnad1 id=tendsto.0h1v.s6.3656f662faeb from=translated src=- shape=2f069499 vocab=6a70ca90
-/
theorem tendsto_choose_div_pow (k : ℕ) :
    Tendsto (fun n : ℕ ↦ (n.choose k : ℝ) / (n : ℝ) ^ k) atTop
      (𝓝 (1 / (k.factorial : ℝ))) := by
  have heq := (isEquivalent_choose k).div
    (IsEquivalent.refl : (fun n : ℕ ↦ (n : ℝ) ^ k) ~[atTop]
      (fun n : ℕ ↦ (n : ℝ) ^ k))
  apply heq.symm.tendsto_nhds
  apply tendsto_congr' _ |>.mpr tendsto_const_nhds
  filter_upwards [eventually_gt_atTop 0] with n hn
  change (((n : ℝ) ^ k / k.factorial) / (n : ℝ) ^ k) = 1 / k.factorial
  have hn0 : (n : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by positivity)
  field_simp

/-- The leading coefficient `2^k/(k+1)!` of the ranked volume polynomial.-/
noncomputable def leadingRankedVolumeCoefficient (k : ℕ) : ℝ :=
  (2 : ℝ) ^ k / (k + 1).factorial

/-- A real-valued upper bound separating the leading and lower-degree terms.
@isnad1 id=le.1h2v.s6.faaa4bc33ff8 from=translated src=- shape=d65ecb80 vocab=e91c6371
-/
theorem cast_rankedVolumePolynomial_le (k t : ℕ) (ht : 1 ≤ t) :
    (rankedVolumePolynomial k t : ℝ) ≤
      (lowerRankedVolumeCoefficient k : ℝ) * (t : ℝ) ^ k +
        leadingRankedVolumeCoefficient k * (t : ℝ) ^ (k + 1) := by
  have hnat := rankedVolumePolynomial_le_lower_add_leading k t ht
  calc
    (rankedVolumePolynomial k t : ℝ) ≤
        ((lowerRankedVolumeCoefficient k * t ^ k +
          2 ^ k * t.choose (k + 1) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    _ = (lowerRankedVolumeCoefficient k : ℝ) * (t : ℝ) ^ k +
        (2 : ℝ) ^ k * (t.choose (k + 1) : ℝ) := by norm_cast
    _ ≤ (lowerRankedVolumeCoefficient k : ℝ) * (t : ℝ) ^ k +
        (2 : ℝ) ^ k * ((t : ℝ) ^ (k + 1) / (k + 1).factorial) := by
      gcongr
      exact Nat.choose_le_pow_div (k + 1) t
    _ = (lowerRankedVolumeCoefficient k : ℝ) * (t : ℝ) ^ k +
        leadingRankedVolumeCoefficient k * (t : ℝ) ^ (k + 1) := by
      rw [leadingRankedVolumeCoefficient]
      ring

/-- The normalized binomial coefficient is eventually above any smaller constant.
@isnad1 id=eventual.1h2v.s6.0d0e24a1353a from=translated src=- shape=4bb52529 vocab=84f328a0
-/
theorem eventually_choose_lower (k : ℕ) {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      (1 / (k.factorial : ℝ) - η) * (n : ℝ) ^ k ≤ (n.choose k : ℝ) := by
  have hratio := (tendsto_choose_div_pow k).eventually
    (Ioi_mem_nhds (sub_lt_self (1 / (k.factorial : ℝ)) hη))
  filter_upwards [hratio, eventually_gt_atTop 0] with n hnratio hn
  have hpow : 0 < (n : ℝ) ^ k := by positivity
  calc
    (1 / (k.factorial : ℝ) - η) * (n : ℝ) ^ k ≤
        ((n.choose k : ℝ) / (n : ℝ) ^ k) * (n : ℝ) ^ k :=
      (mul_le_mul_of_nonneg_right hnratio.le hpow.le)
    _ = (n.choose k : ℝ) := by field_simp

/-- For fixed positive dimension, the totalized path-token burning sequence tends to infinity.
@isnad1 id=tendsto.1h1v.s4.6705f2fda714 from=translated src=- shape=52e44ca1 vocab=9a49af53
-/
theorem tendsto_pathTokenBurningNumberTotal_atTop (k : ℕ) (hk : 0 < k) :
    Tendsto (pathTokenBurningNumberTotal k) atTop atTop := by
  apply tendsto_atTop.2
  intro M
  filter_upwards [(tendsto_choose_atTop k hk).eventually_gt_atTop
      (rankedVolumePolynomial k M), eventually_ge_atTop k] with n hn hkn
  have hvolume := choose_le_rankedVolumePolynomial_pathToken hkn
  by_contra hM
  have hle : pathTokenBurningNumberTotal k n ≤ M := by omega
  have hpoly := rankedVolumePolynomial_mono k hle
  omega

/-- Along the burning sequence, the lower-degree volume terms can be absorbed into any `η > 0`.
@isnad1 id=eventual.2h2v.s6.b3922bd9acb4 from=translated src=- shape=661fd143 vocab=c85a598e
-/
theorem eventually_rankedVolumePolynomial_pathToken_upper (k : ℕ) (hk : 0 < k)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n : ℕ in atTop,
      (rankedVolumePolynomial k (pathTokenBurningNumberTotal k n) : ℝ) ≤
        (leadingRankedVolumeCoefficient k + η) *
          (pathTokenBurningNumberTotal k n : ℝ) ^ (k + 1) := by
  have ht := tendsto_pathTokenBurningNumberTotal_atTop k hk
  have htCast :
      Tendsto (fun n ↦ (pathTokenBurningNumberTotal k n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp ht
  filter_upwards [ht.eventually_ge_atTop 1,
      htCast.eventually_ge_atTop ((lowerRankedVolumeCoefficient k : ℝ) / η)] with n hn hlarge
  have hcoefficient :
      (lowerRankedVolumeCoefficient k : ℝ) ≤
        (pathTokenBurningNumberTotal k n : ℝ) * η :=
    (div_le_iff₀ hη).mp hlarge
  have habsorb :
      (lowerRankedVolumeCoefficient k : ℝ) *
          (pathTokenBurningNumberTotal k n : ℝ) ^ k ≤
        η * (pathTokenBurningNumberTotal k n : ℝ) ^ (k + 1) := by
    calc
      (lowerRankedVolumeCoefficient k : ℝ) *
          (pathTokenBurningNumberTotal k n : ℝ) ^ k ≤
          ((pathTokenBurningNumberTotal k n : ℝ) * η) *
            (pathTokenBurningNumberTotal k n : ℝ) ^ k :=
        mul_le_mul_of_nonneg_right hcoefficient (by positivity)
      _ = η * (pathTokenBurningNumberTotal k n : ℝ) ^ (k + 1) := by
        rw [pow_succ]
        ring
  calc
    (rankedVolumePolynomial k (pathTokenBurningNumberTotal k n) : ℝ) ≤
        (lowerRankedVolumeCoefficient k : ℝ) *
            (pathTokenBurningNumberTotal k n : ℝ) ^ k +
          leadingRankedVolumeCoefficient k *
            (pathTokenBurningNumberTotal k n : ℝ) ^ (k + 1) :=
      cast_rankedVolumePolynomial_le k _ hn
    _ ≤ η * (pathTokenBurningNumberTotal k n : ℝ) ^ (k + 1) +
        leadingRankedVolumeCoefficient k *
          (pathTokenBurningNumberTotal k n : ℝ) ^ (k + 1) :=
      add_le_add_left habsorb _
    _ = (leadingRankedVolumeCoefficient k + η) *
        (pathTokenBurningNumberTotal k n : ℝ) ^ (k + 1) := by ring

/-- The `(k+1)`-st power of the asymptotic constant.-/
noncomputable def volumeLowerPowerConstant (k : ℕ) : ℝ :=
  (k + 1 : ℝ) / (2 : ℝ) ^ k

/--
@isnad1 id=lt.0h1v.s3.4313a9339ef8 from=translated src=- shape=b9369acb vocab=22f657f7
-/
theorem volumeLowerPowerConstant_pos (k : ℕ) :
    0 < volumeLowerPowerConstant k := by
  rw [volumeLowerPowerConstant]
  positivity

/--
@isnad1 id=eq.0h1v.s5.d4adbfe6879c from=translated src=- shape=eec7492d vocab=c3c347b2
-/
theorem volumeLowerPowerConstant_mul_leading (k : ℕ) :
    volumeLowerPowerConstant k * leadingRankedVolumeCoefficient k =
      1 / (k.factorial : ℝ) := by
  rw [volumeLowerPowerConstant, leadingRankedVolumeCoefficient, Nat.factorial_succ]
  norm_num
  field_simp

/--
Every constant strictly below `(k+1)/2^k` is eventually a lower bound for the normalized
`(k+1)`-st power of the burning number.
@isnad1 id=eventual.3h2v.s6.ccca7ad16527 from=translated src=- shape=0fde3eb2 vocab=4d846eb6
-/
theorem eventually_pathTokenBurningNumberTotal_pow_lower (k : ℕ) (hk : 0 < k)
    {d : ℝ} (hd0 : 0 ≤ d) (hd : d < volumeLowerPowerConstant k) :
    ∀ᶠ n : ℕ in atTop,
      d * (n : ℝ) ^ k ≤ (pathTokenBurningNumberTotal k n : ℝ) ^ (k + 1) := by
  let A := leadingRankedVolumeCoefficient k
  let gap := 1 / (k.factorial : ℝ) - d * A
  let η₁ := gap / 2
  let η₂ := gap / (2 * (d + 1))
  have hA : 0 < A := by
    dsimp [A, leadingRankedVolumeCoefficient]
    positivity
  have hgap : 0 < gap := by
    dsimp [gap, A]
    rw [← volumeLowerPowerConstant_mul_leading k]
    exact sub_pos.mpr (mul_lt_mul_of_pos_right hd hA)
  have hη₁ : 0 < η₁ := by dsimp [η₁]; positivity
  have hη₂ : 0 < η₂ := by
    dsimp [η₂]
    positivity
  have hcoefficient : d * (A + η₂) ≤ 1 / (k.factorial : ℝ) - η₁ := by
    have hd1 : 0 < d + 1 := by positivity
    have heq :
        (1 / (k.factorial : ℝ) - η₁) - d * (A + η₂) =
          gap / (2 * (d + 1)) := by
      dsimp [η₁, η₂, gap]
      field_simp [ne_of_gt hd1]
      ring
    apply sub_nonneg.mp
    rw [heq]
    positivity
  filter_upwards [eventually_choose_lower k hη₁,
      eventually_rankedVolumePolynomial_pathToken_upper k hk hη₂,
      eventually_ge_atTop k] with n hchoose hvolume hnk
  have hexact :
      (n.choose k : ℝ) ≤
        (rankedVolumePolynomial k (pathTokenBurningNumberTotal k n) : ℝ) := by
    exact_mod_cast choose_le_rankedVolumePolynomial_pathToken hnk
  have hchain :
      (1 / (k.factorial : ℝ) - η₁) * (n : ℝ) ^ k ≤
        (A + η₂) * (pathTokenBurningNumberTotal k n : ℝ) ^ (k + 1) :=
    hchoose.trans (hexact.trans hvolume)
  have hAη : 0 < A + η₂ := by positivity
  apply (mul_le_mul_iff_of_pos_left hAη).mp
  calc
    (A + η₂) * (d * (n : ℝ) ^ k) =
        (d * (A + η₂)) * (n : ℝ) ^ k := by ring
    _ ≤ (1 / (k.factorial : ℝ) - η₁) * (n : ℝ) ^ k :=
      mul_le_mul_of_nonneg_right hcoefficient (by positivity)
    _ ≤ (A + η₂) * (pathTokenBurningNumberTotal k n : ℝ) ^ (k + 1) :=
      hchain

/-- The natural fixed-`k` scale, written so that its `(k+1)`-st power is exactly `n^k`.-/
noncomputable def pathTokenAsymptoticScale (k n : ℕ) : ℝ :=
  ((n : ℝ) ^ k) ^ (k + 1 : ℝ)⁻¹

/--
@isnad1 id=eq.0h2v.s5.059609a2af2f from=translated src=- shape=54a9d814 vocab=ac25978b
-/
@[simp]
theorem pathTokenAsymptoticScale_pow (k n : ℕ) :
    pathTokenAsymptoticScale k n ^ (k + 1) = (n : ℝ) ^ k := by
  simpa [pathTokenAsymptoticScale] using
    (Real.rpow_inv_natCast_pow (x := (n : ℝ) ^ k) (n := k + 1)
      (pow_nonneg (Nat.cast_nonneg n) k) (by omega))

/-- The scale above is the standard `n^(k/(k+1))` normalization.
@isnad1 id=eq.0h2v.s5.765b0441a4cc from=translated src=- shape=3e289321 vocab=f4472838
-/
theorem pathTokenAsymptoticScale_eq_rpow (k n : ℕ) :
    pathTokenAsymptoticScale k n = (n : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)) := by
  simpa [pathTokenAsymptoticScale, div_eq_mul_inv, Real.rpow_natCast] using
    (Real.rpow_mul (show 0 ≤ (n : ℝ) by positivity) (k : ℝ) (k + 1 : ℝ)⁻¹).symm

/--
@isnad1 id=le.0h2v.s4.d02165decb23 from=translated src=- shape=5ffe46ab vocab=d8b7f7ca
-/
theorem pathTokenAsymptoticScale_nonneg (k n : ℕ) :
    0 ≤ pathTokenAsymptoticScale k n := by
  rw [pathTokenAsymptoticScale]
  positivity

/--
@isnad1 id=lt.1h2v.s4.f908c7e5c752 from=translated src=- shape=cee548f2 vocab=c9f95c86
-/
theorem pathTokenAsymptoticScale_pos {k n : ℕ} (hn : 0 < n) :
    0 < pathTokenAsymptoticScale k n := by
  rw [pathTokenAsymptoticScale]
  apply Real.rpow_pos_of_pos
  positivity

/-- The sharp constant obtained by taking the positive `(k+1)`-st root.-/
noncomputable def volumeLowerConstant (k : ℕ) : ℝ :=
  volumeLowerPowerConstant k ^ (k + 1 : ℝ)⁻¹

/--
@isnad1 id=lt.0h1v.s3.a6f19aa55ba7 from=translated src=- shape=b9369acb vocab=6ab3f2d1
-/
theorem volumeLowerConstant_pos (k : ℕ) :
    0 < volumeLowerConstant k := by
  exact Real.rpow_pos_of_pos (volumeLowerPowerConstant_pos k) _

/--
@isnad1 id=eq.0h1v.s5.f5564d45df41 from=translated src=- shape=729b7206 vocab=8c574ba2
-/
@[simp]
theorem volumeLowerConstant_pow (k : ℕ) :
    volumeLowerConstant k ^ (k + 1) = volumeLowerPowerConstant k := by
  simpa [volumeLowerConstant] using
    (Real.rpow_inv_natCast_pow (x := volumeLowerPowerConstant k) (n := k + 1)
      (volumeLowerPowerConstant_pos k).le (by omega))

/-- The path-token burning number divided by its fixed-dimensional power scale.-/
noncomputable def pathTokenBurningRatio (k n : ℕ) : ℝ :=
  (pathTokenBurningNumberTotal k n : ℝ) / pathTokenAsymptoticScale k n

/--
@isnad1 id=le.0h2v.s4.acad05641e21 from=translated src=- shape=5ffe46ab vocab=965c8e1e
-/
theorem pathTokenBurningRatio_nonneg (k n : ℕ) :
    0 ≤ pathTokenBurningRatio k n := by
  exact div_nonneg (Nat.cast_nonneg _) (pathTokenAsymptoticScale_nonneg k n)

/-- The nonnegative extended-real ratio, whose liminf also covers divergence to `+∞`.-/
noncomputable def pathTokenBurningRatioENNReal (k n : ℕ) : ENNReal :=
  ENNReal.ofReal (pathTokenBurningRatio k n)

/--
Every constant strictly below the sharp root constant is eventually a lower bound for the
normalized burning number.
@isnad1 id=eventual.2h2v.s5.52562a084721 from=translated src=- shape=60f2be6a vocab=cd7437a8
-/
theorem eventually_constant_le_pathTokenBurningRatio (k : ℕ) (hk : 0 < k)
    {c : ℝ} (hc : c < volumeLowerConstant k) :
    ∀ᶠ n : ℕ in atTop, c ≤ pathTokenBurningRatio k n := by
  by_cases hc0 : 0 ≤ c
  · have hdpow : c ^ (k + 1) < volumeLowerPowerConstant k := by
      rw [← volumeLowerConstant_pow]
      exact (pow_lt_pow_iff_left₀ hc0 (volumeLowerConstant_pos k).le (by omega)).2 hc
    filter_upwards [
        eventually_pathTokenBurningNumberTotal_pow_lower k hk (pow_nonneg hc0 _) hdpow,
        eventually_gt_atTop 0] with n hpower hn
    have hscale : 0 < pathTokenAsymptoticScale k n :=
      pathTokenAsymptoticScale_pos hn
    apply (le_div_iff₀ hscale).2
    apply (pow_le_pow_iff_left₀ (n := k + 1) (mul_nonneg hc0 hscale.le)
      (Nat.cast_nonneg _) (by omega)).mp
    simpa [mul_pow] using hpower
  · have hcneg : c < 0 := lt_of_not_ge hc0
    exact Eventually.of_forall fun n ↦
      hcneg.le.trans (pathTokenBurningRatio_nonneg k n)

/--
The sharp constant is a lower bound for the extended-real liminf of the normalized burning
numbers. Using `ℝ≥0∞` makes this statement independent of any asymptotic upper bound.
@isnad1 id=le.1h1v.s5.34587141513e from=translated src=- shape=0ed46b91 vocab=7294f372
-/
theorem volumeLowerConstant_le_liminf_pathTokenBurningRatio (k : ℕ) (hk : 0 < k) :
    ENNReal.ofReal (volumeLowerConstant k) ≤
      liminf (pathTokenBurningRatioENNReal k) atTop := by
  apply ENNReal.le_of_forall_nnreal_lt
  intro c hc
  have hcReal : (c : ℝ) < volumeLowerConstant k := by
    rw [← ENNReal.ofReal_lt_ofReal_iff (volumeLowerConstant_pos k)]
    simpa using hc
  apply le_liminf_of_le (by isBoundedDefault)
  exact (eventually_constant_le_pathTokenBurningRatio k hk hcReal).mono fun n hn ↦ by
    simpa [pathTokenBurningRatioENNReal] using ENNReal.ofReal_le_ofReal hn

/--
Part (A2), in standard notation: for fixed `k ≥ 2`, the normalized burning numbers have
extended-real liminf at least `((k+1)/2^k)^(1/(k+1))`.
@isnad1 id=le.1h1v.s7.ca2040a614f9 from=translated src=- shape=42a6fc45 vocab=e72bf69f
-/
theorem generalLowerAsymptotic_liminf (k : ℕ) (hk : 2 ≤ k) :
    ENNReal.ofReal
        (((k + 1 : ℝ) / (2 : ℝ) ^ k) ^ (k + 1 : ℝ)⁻¹) ≤
      liminf
        (fun n : ℕ ↦ ENNReal.ofReal
          ((pathTokenBurningNumberTotal k n : ℝ) /
            (n : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ))))
        atTop := by
  simp_rw [← pathTokenAsymptoticScale_eq_rpow]
  change ENNReal.ofReal (volumeLowerConstant k) ≤
    liminf (pathTokenBurningRatioENNReal k) atTop
  exact volumeLowerConstant_le_liminf_pathTokenBurningRatio k (by omega)

/--
Equivalent `ε`-form of (A2): every positive loss from the sharp constant gives an eventual
real-valued lower bound in the usual `n^(k/(k+1))` scale.
@isnad1 id=eventual.2h2v.s7.5d16ae417f7d from=translated src=- shape=49b8caf0 vocab=6708540b
-/
theorem eventually_generalLowerAsymptotic (k : ℕ) (hk : 2 ≤ k)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((((k + 1 : ℝ) / (2 : ℝ) ^ k) ^ (k + 1 : ℝ)⁻¹) - ε) *
          (n : ℝ) ^ ((k : ℝ) / (k + 1 : ℝ)) ≤
        (pathTokenBurningNumberTotal k n : ℝ) := by
  have heventually :=
    eventually_constant_le_pathTokenBurningRatio k (by omega)
      (sub_lt_self (volumeLowerConstant k) hε)
  filter_upwards [heventually, eventually_gt_atTop 0] with n hnratio hn
  have hscale : 0 < pathTokenAsymptoticScale k n :=
    pathTokenAsymptoticScale_pos hn
  have hmul := (le_div_iff₀ hscale).mp hnratio
  rw [pathTokenAsymptoticScale_eq_rpow] at hmul
  simpa only [volumeLowerConstant, volumeLowerPowerConstant] using hmul

end BurningPath
