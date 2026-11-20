import Tengoku.Seed.Analysis.Real.Sqrt
import Tengoku.Seed.Algebra.BigOperators.Field
import Tengoku.Seed.Tactic.NormNum
import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms sqrt_one_sub_lower` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms sqrt_one_sub_upper` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bentP_lower_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms four_dimensional_intermediate_gap` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms four_dimensional_weighted_hellinger_gap` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms twoRootR_gap_bound` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms twoRootR_gap_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms twoNoiseR_hellinger_strict` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fourthMomentExpression_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms four_low_noise_ratio_gt_one` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Real estimates for the bent-function Hellinger argument

This file verifies analytic inequalities from Appendix C of the manuscript.
The finite-distribution theorem takes the second- and fourth-moment identities
as explicit hypotheses; it does not assert their Boolean/Fourier derivation.
The Bernstein certificate proves a full-interval lower bound for `bentP`.
No numerical sampling or endpoint-only inference is used.
-/

set_option autoImplicit false

noncomputable section

namespace Hellinger.BentEstimates

open scoped BigOperators

/-- The lower polynomial approximation in (C.9), on its whole domain.
@isnad1 id=le.2h1v.s6.c9726c3bfed9 from=translated src=- shape=4338ded0 vocab=177add60
-/
theorem sqrt_one_sub_lower (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    1 - z / 2 - z ^ 2 / 2 ≤ Real.sqrt (1 - z) := by
  apply Real.le_sqrt_of_sq_le
  have h : 0 ≤ z ^ 2 * (1 - z) * (z + 3) / 4 := by positivity
  nlinarith only [h]

/-- The upper polynomial approximation in (C.9), on its whole domain.
@isnad1 id=le.2h1v.s6.f722ec905543 from=translated src=- shape=337a86bd vocab=177add60
-/
theorem sqrt_one_sub_upper (z : ℝ) (hz0 : 0 ≤ z) (hz1 : z ≤ 1) :
    Real.sqrt (1 - z) ≤ 1 - z / 2 - z ^ 2 / 8 := by
  have hz2 : z ^ 2 ≤ z := by nlinarith [mul_nonneg hz0 (sub_nonneg.mpr hz1)]
  apply Real.sqrt_le_iff.mpr
  constructor
  · nlinarith
  · have h : 0 ≤ z ^ 3 * (8 + z) / 64 := by positivity
    nlinarith only [h]

/-- The fourth-moment polynomial from (C.8).-/
def bentH (t : ℝ) : ℝ := t ^ 4 + 12 * t ^ 3 - 10 * t ^ 2 + 12 * t + 1

/-- The intermediate-noise lower polynomial from (C.10).-/
def bentP (t : ℝ) : ℝ :=
  t / 2 + t ^ 2 / 8 + 1 / 32 - (1 + t) ^ 4 / 32 - bentH t ^ 2 / 512

/-- A positive-coefficient Bernstein certificate, in the nonnegative variables
`t - 1/16` and `7/10 - t`. The stronger constant `1/100` is obtained by this
formal reproof; the manuscript only needs strict positivity.-/
private def pCertificate (t : ℝ) : ℝ :=
  (6378257657609375 * (t - 1 / 16) ^ 0 * (7 / 10 - t) ^ 8
    + 211351796599000000 * (t - 1 / 16) ^ 1 * (7 / 10 - t) ^ 7
    + 1207788983492000000 * (t - 1 / 16) ^ 2 * (7 / 10 - t) ^ 6
    + 3190878237145600000 * (t - 1 / 16) ^ 3 * (7 / 10 - t) ^ 5
    + 4692521589539840000 * (t - 1 / 16) ^ 4 * (7 / 10 - t) ^ 4
    + 4006545675157504000 * (t - 1 / 16) ^ 5 * (7 / 10 - t) ^ 3
    + 1901092419534848000 * (t - 1 / 16) ^ 6 * (7 / 10 - t) ^ 2
    + 414781447119831040 * (t - 1 / 16) ^ 7 * (7 / 10 - t) ^ 1
    + 15730137853067264 * (t - 1 / 16) ^ 8 * (7 / 10 - t) ^ 0) / 23433187620045312

private theorem pCertificate_identity (t : ℝ) :
    bentP t = 1 / 100 + pCertificate t := by
  unfold bentP bentH pCertificate
  ring

/-- A uniform positive lower bound on the complete intermediate-noise interval.
@isnad1 id=le.2h1v.s6.b00ddac8b025 from=translated src=- shape=d610ec2d vocab=5a0ecb11
-/
theorem bentP_lower_bound (t : ℝ) (ht0 : 1 / 16 ≤ t) (ht1 : t ≤ 7 / 10) :
    (1 : ℝ) / 100 ≤ bentP t := by
  have hl : 0 ≤ t - 1 / 16 := sub_nonneg.mpr ht0
  have hr : 0 ≤ 7 / 10 - t := sub_nonneg.mpr ht1
  have hc : 0 ≤ pCertificate t := by
    unfold pCertificate
    positivity
  rw [pCertificate_identity]
  linarith

/-- In particular, positivity holds for every point, not merely the endpoints.
@isnad1 id=lt.2h1v.s6.63d8c2592fb5 from=translated src=- shape=5c3dea10 vocab=ad7e7635
-/
theorem bentP_pos (t : ℝ) (ht0 : 1 / 16 ≤ t) (ht1 : t ≤ 7 / 10) :
    0 < bentP t := by
  linarith [bentP_lower_bound t ht0 ht1]

/-- The strict four-dimensional bias margin used in (C.10).
@isnad1 id=lt.0h0v.s6.38f3457c07b6 from=translated src=- shape=32d0b123 vocab=56eb3141
-/
theorem four_dimensional_bias_margin :
    (1 : ℝ) / 32 < 1 - Real.sqrt 15 / 4 := by
  have hs : Real.sqrt (15 : ℝ) < 31 / 8 := by
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).mpr
    norm_num
  linarith

/-- Averaging the lower square-root approximation over a finite distribution.
@isnad1 id=le.3h3v.s8.e950dbc10b8a from=translated src=- shape=534a84b9 vocab=2fa6cbfa
-/
theorem finite_posterior_lower_bound {ι : Type*} [Fintype ι]
    (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, (u i) ^ 2 ≤ 1) :
    1 - (∑ i, w i * (u i) ^ 2) / 2 - (∑ i, w i * (u i) ^ 4) / 2 ≤
      ∑ i, w i * Real.sqrt (1 - (u i) ^ 2) := by
  have hpoint : ∀ i, w i * (1 - (u i) ^ 2 / 2 - ((u i) ^ 2) ^ 2 / 2) ≤
      w i * Real.sqrt (1 - (u i) ^ 2) := by
    intro i
    exact mul_le_mul_of_nonneg_left
      (sqrt_one_sub_lower ((u i) ^ 2) (sq_nonneg _) (hu i)) (hw i)
  have havg := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hpoint i)
  have hid : (∑ i, w i * (1 - (u i) ^ 2 / 2 - ((u i) ^ 2) ^ 2 / 2)) =
      1 - (∑ i, w i * (u i) ^ 2) / 2 - (∑ i, w i * (u i) ^ 4) / 2 := by
    simp_rw [mul_sub, mul_one, ← mul_div_assoc, ← pow_mul]
    norm_num [Finset.sum_sub_distrib, ← Finset.sum_div, hsum]
  rw [hid] at havg
  exact havg

/-- The scalar implication of the second- and fourth-moment estimates.
The moment bounds are hypotheses, so no Fourier identity is silently assumed.
@isnad1 id=lt.5h4v.s8.bbe96a607af0 from=translated src=- shape=c8138944 vocab=cbfb51b4
-/
theorem gap_gt_bentP (t R Q₂ Q₄ : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hR : 1 - Q₂ / 2 - Q₄ / 2 ≤ R)
    (hQ₂ : Q₂ = (1 + t) ^ 4 / 16)
    (hQ₄ : Q₄ ≤ bentH t ^ 2 / 256) :
    bentP t < R - Real.sqrt 15 / 4 + 1 - Real.sqrt (1 - t) := by
  have hs := sqrt_one_sub_upper t ht0 ht1
  have hb := four_dimensional_bias_margin
  rw [hQ₂] at hR
  unfold bentP
  linarith

/-- A full-interval lower bound with the FIXED bias term `sqrt 15 / 4`.
For an arbitrary finite distribution this is not its own Hellinger gap, unless
its squared mean is `1/16`. See `four_dimensional_weighted_hellinger_gap` for
the theorem tying this expression to the actual mean. Moment identities
remain explicit hypotheses; their Boolean/Fourier derivation is separate.
@isnad1 id=lt.7h4v.s8.6e57f8bdc230 from=translated src=- shape=7018a2a2 vocab=e1278e5e
-/
theorem four_dimensional_intermediate_gap {ι : Type*} [Fintype ι]
    (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, (u i) ^ 2 ≤ 1)
    (t : ℝ) (ht0 : 1 / 16 ≤ t) (ht1 : t ≤ 7 / 10)
    (hQ₂ : (∑ i, w i * (u i) ^ 2) = (1 + t) ^ 4 / 16)
    (hQ₄ : (∑ i, w i * (u i) ^ 4) ≤ bentH t ^ 2 / 256) :
    (1 : ℝ) / 100 < (∑ i, w i * Real.sqrt (1 - (u i) ^ 2)) -
      Real.sqrt 15 / 4 + 1 - Real.sqrt (1 - t) := by
  exact lt_of_le_of_lt (bentP_lower_bound t ht0 ht1)
    (gap_gt_bentP t _ _ _ (by linarith) (by linarith)
      (finite_posterior_lower_bound w u hw hsum hu) hQ₂ hQ₄)

/-- The actual weighted Hellinger gap, with the squared-mean hypothesis explicit.
The mean, second moment, and fourth-moment bound are all supplied independently;
none is inferred from the other two.
@isnad1 id=lt.8h4v.s9.f32eb478415d from=translated src=- shape=ea559bc6 vocab=e1278e5e
-/
theorem four_dimensional_weighted_hellinger_gap {ι : Type*} [Fintype ι]
    (w u : ι → ℝ) (hw : ∀ i, 0 ≤ w i) (hsum : ∑ i, w i = 1)
    (hu : ∀ i, (u i) ^ 2 ≤ 1)
    (t : ℝ) (ht0 : 1 / 16 ≤ t) (ht1 : t ≤ 7 / 10)
    (hmean : (∑ i, w i * u i) ^ 2 = 1 / 16)
    (hQ₂ : (∑ i, w i * (u i) ^ 2) = (1 + t) ^ 4 / 16)
    (hQ₄ : (∑ i, w i * (u i) ^ 4) ≤ bentH t ^ 2 / 256) :
    (1 : ℝ) / 100 < (∑ i, w i * Real.sqrt (1 - (u i) ^ 2)) -
      Real.sqrt (1 - (∑ i, w i * u i) ^ 2) + 1 - Real.sqrt (1 - t) := by
  have hroot : Real.sqrt (1 - (∑ i, w i * u i) ^ 2) = Real.sqrt 15 / 4 := by
    rw [hmean]
    norm_num only [show (1 : ℝ) - 1 / 16 = 15 / 16 by norm_num]
    rw [Real.sqrt_div' _ (show 0 ≤ (16 : ℝ) by norm_num)]
    have hs16 : Real.sqrt (16 : ℝ) = 4 := by
      rw [show (16 : ℝ) = (4 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [hs16]
  rw [hroot]
  exact four_dimensional_intermediate_gap w u hw hsum hu t ht0 ht1 hQ₂ hQ₄

/-- A chord bound for the square root, proved algebraically on the whole segment.
@isnad1 id=le.4h3v.s7.7bf352a1201c from=translated src=- shape=183fbea2 vocab=ef4deeb7
-/
theorem sqrt_chord (a b t : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 - t) * Real.sqrt a + t * Real.sqrt b ≤ Real.sqrt ((1 - t) * a + t * b) := by
  apply Real.le_sqrt_of_sq_le
  calc
    ((1 - t) * Real.sqrt a + t * Real.sqrt b) ^ 2 ≤
        (1 - t) * Real.sqrt a ^ 2 + t * Real.sqrt b ^ 2 := by
      have h : 0 ≤ t * (1 - t) * (Real.sqrt a - Real.sqrt b) ^ 2 := by positivity
      nlinarith only [h]
    _ = (1 - t) * a + t * b := by rw [Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- The two-variable root-pair comparison from (C.2), including both endpoints.
@isnad1 id=le.2h1v.s7.cf45e02c527c from=translated src=- shape=31868a58 vocab=3bfce676
-/
theorem two_root_pair (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    2 * Real.sqrt (3 - ρ ^ 2) ≤
      Real.sqrt (3 + ρ ^ 2 - 4 * ρ) + Real.sqrt (3 + ρ ^ 2 + 4 * ρ) := by
  have ht : ρ ^ 2 ≤ 1 := by nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hρ1)]
  have hA : 0 ≤ 3 + ρ ^ 2 - 4 * ρ := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hρ1) (show 0 ≤ 3 - ρ by linarith)]
  have hB : 0 ≤ 3 + ρ ^ 2 + 4 * ρ := by positivity
  have hC : 0 ≤ 3 - ρ ^ 2 := by linarith
  have hprod : 3 * (1 - ρ ^ 2) ≤
      Real.sqrt (3 + ρ ^ 2 - 4 * ρ) * Real.sqrt (3 + ρ ^ 2 + 4 * ρ) := by
    rw [← Real.sqrt_mul hA]
    apply Real.le_sqrt_of_sq_le
    have h : 0 ≤ 8 * ρ ^ 2 * (1 - ρ ^ 2) := by positivity
    nlinarith only [h]
  apply (sq_le_sq₀ (by positivity) (by positivity)).mp
  nlinarith only [hprod, Real.sq_sqrt hA, Real.sq_sqrt hB, Real.sq_sqrt hC]

/-- The explicit posterior expression in (C.2). Its identification with a
Boolean noise posterior is a separate upstream calculation.-/
def twoRootR (ρ : ℝ) : ℝ :=
  Real.sqrt (1 - ρ ^ 2) / 8 *
    (Real.sqrt (3 + ρ ^ 2 - 4 * ρ) + Real.sqrt (3 + ρ ^ 2 + 4 * ρ) +
      2 * Real.sqrt (3 + ρ ^ 2))

/-- The complete chord estimate (C.3), without a concavity hypothesis.
@isnad1 id=le.2h1v.s7.671b8fde425b from=translated src=- shape=a152d1b4 vocab=778f125c
-/
theorem twoRootR_chord (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    Real.sqrt (1 - ρ ^ 2) *
        ((1 - ρ ^ 2) * (Real.sqrt 3 / 2) + ρ ^ 2 * ((2 + Real.sqrt 2) / 4)) ≤
      twoRootR ρ := by
  have ht0 : 0 ≤ ρ ^ 2 := sq_nonneg _
  have ht1 : ρ ^ 2 ≤ 1 := by nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hρ1)]
  have hm := sqrt_chord 3 2 (ρ ^ 2) (by norm_num) (by norm_num) ht0 ht1
  have hp := sqrt_chord 3 4 (ρ ^ 2) (by norm_num) (by norm_num) ht0 ht1
  have hmarg : (1 - ρ ^ 2) * 3 + ρ ^ 2 * 2 = 3 - ρ ^ 2 := by ring
  have hparg : (1 - ρ ^ 2) * 3 + ρ ^ 2 * 4 = 3 + ρ ^ 2 := by ring
  rw [hmarg] at hm
  rw [hparg] at hp
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [hs4] at hp
  have hc := Real.sqrt_nonneg (1 - ρ ^ 2)
  have hch : (1 - ρ ^ 2) * (Real.sqrt 3 / 2) + ρ ^ 2 * ((2 + Real.sqrt 2) / 4) ≤
      (Real.sqrt (3 - ρ ^ 2) + Real.sqrt (3 + ρ ^ 2)) / 4 := by linarith
  have hchm := mul_le_mul_of_nonneg_left hch hc
  have hpair := mul_le_mul_of_nonneg_left (two_root_pair ρ hρ0 hρ1)
    (show 0 ≤ Real.sqrt (1 - ρ ^ 2) / 8 by positivity)
  unfold twoRootR
  nlinarith only [hchm, hpair]

/-- The strictly positive coefficient in the two-dimensional gap (C.4).
@isnad1 id=lt.0h0v.s6.d3f97503d728 from=translated src=- shape=9ffac78e vocab=2cc20a5a
-/
theorem two_gap_coefficient_pos : 0 < (4 + Real.sqrt (2 : ℝ) - 3 * Real.sqrt 3) / 4 := by
  have h2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have h3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  have hl : (9 : ℝ) / 8 < Real.sqrt 2 := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  have hs : (3 * Real.sqrt (3 : ℝ)) ^ 2 < (4 + Real.sqrt 2) ^ 2 := by nlinarith
  have h := (sq_lt_sq₀ (by positivity) (by positivity)).mp hs
  linarith

private theorem two_coefficients_order : (2 + Real.sqrt (2 : ℝ)) / 4 ≤ Real.sqrt 3 / 2 := by
  have h2 := Real.sq_sqrt (show 0 ≤ (2 : ℝ) by norm_num)
  have h3 := Real.sq_sqrt (show 0 ≤ (3 : ℝ) by norm_num)
  have hl : Real.sqrt (2 : ℝ) < 3 / 2 := by
    apply (Real.sqrt_lt (by norm_num) (by norm_num)).mpr
    norm_num
  have hs : (2 + Real.sqrt (2 : ℝ)) ^ 2 ≤ (2 * Real.sqrt 3) ^ 2 := by nlinarith
  have h := (sq_le_sq₀ (by positivity) (by positivity)).mp hs
  linarith

/-- Quantitative two-dimensional Hellinger gap on the entire noise interval.
@isnad1 id=le.2h1v.s7.6d7551c00236 from=translated src=- shape=dee606b9 vocab=778f125c
-/
theorem twoRootR_gap_bound (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (4 + Real.sqrt (2 : ℝ) - 3 * Real.sqrt 3) / 4 * ρ ^ 2 ≤
      twoRootR ρ - Real.sqrt 3 / 2 + 1 - Real.sqrt (1 - ρ ^ 2) := by
  have ht0 : 0 ≤ ρ ^ 2 := sq_nonneg _
  have ht1 : ρ ^ 2 ≤ 1 := by nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hρ1)]
  have hc0 := Real.sqrt_nonneg (1 - ρ ^ 2)
  have hc1 : Real.sqrt (1 - ρ ^ 2) ≤ 1 := by
    apply Real.sqrt_le_iff.mpr
    constructor <;> nlinarith
  have ha : Real.sqrt (3 : ℝ) / 2 ≤ 1 := by
    have hs : Real.sqrt (3 : ℝ) ≤ 2 := by
      apply Real.sqrt_le_iff.mpr
      norm_num
    linarith
  have hab := two_coefficients_order
  have hsq := Real.sq_sqrt (show 0 ≤ 1 - ρ ^ 2 by linarith)
  have hR := twoRootR_chord ρ hρ0 hρ1
  have h₁ : 0 ≤ (1 - Real.sqrt (3 : ℝ) / 2) * (1 - Real.sqrt (1 - ρ ^ 2)) ^ 2 / 2 := by
    positivity
  have h₂ : 0 ≤ (Real.sqrt (3 : ℝ) / 2 - (2 + Real.sqrt 2) / 4) * ρ ^ 2 *
      (1 - Real.sqrt (1 - ρ ^ 2)) := by positivity
  have heq : ρ ^ 2 = 1 - Real.sqrt (1 - ρ ^ 2) ^ 2 := by linarith
  -- Multiplying the square-root identity by the coefficient justifies the
  -- cubic terms appearing in the nonnegative remainder identity.
  have heq' : (1 - Real.sqrt (3 : ℝ) / 2) *
      (Real.sqrt (1 - ρ ^ 2) ^ 2 - (1 - ρ ^ 2)) = 0 := by rw [hsq]; ring
  nlinarith only [hR, h₁, h₂, heq']

/-- Strictness at every positive correlation, for the explicit two-variable expression.
@isnad1 id=lt.2h1v.s6.7b9395d37e5c from=translated src=- shape=5cfcffb2 vocab=afef20c2
-/
theorem twoRootR_gap_pos (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    0 < twoRootR ρ - Real.sqrt 3 / 2 + 1 - Real.sqrt (1 - ρ ^ 2) := by
  have h := twoRootR_gap_bound ρ (le_of_lt hρ0) hρ1
  have hp : 0 < (4 + Real.sqrt (2 : ℝ) - 3 * Real.sqrt 3) / 4 * ρ ^ 2 :=
    mul_pos two_gap_coefficient_pos (sq_pos_of_pos hρ0)
  linarith

/-- The average of the four square-root posterior terms for the canonical
quadratic function in two variables. The middle value has multiplicity two.-/
def twoNoiseR (ρ : ℝ) : ℝ :=
  (Real.sqrt (1 - ((1 + 2 * ρ - ρ ^ 2) / 2) ^ 2) +
    2 * Real.sqrt (1 - ((1 + ρ ^ 2) / 2) ^ 2) +
    Real.sqrt (1 - ((1 - 2 * ρ - ρ ^ 2) / 2) ^ 2)) / 4

/-- All three complementary-square factorizations leading to (C.2).
@isnad1 id=eq.2h1v.s4.b20e231bcd04 from=translated src=- shape=df5c752e vocab=485217fe
-/
theorem twoNoiseR_eq_twoRootR (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    twoNoiseR ρ = twoRootR ρ := by
  have ht1 : ρ ^ 2 ≤ 1 := by nlinarith [mul_nonneg hρ0 (sub_nonneg.mpr hρ1)]
  have hc : 0 ≤ 1 - ρ ^ 2 := by linarith
  have ha : 1 - ((1 + 2 * ρ - ρ ^ 2) / 2) ^ 2 =
      ((1 - ρ ^ 2) * (3 + ρ ^ 2 - 4 * ρ)) / 4 := by ring
  have hb : 1 - ((1 + ρ ^ 2) / 2) ^ 2 =
      ((1 - ρ ^ 2) * (3 + ρ ^ 2)) / 4 := by ring
  have hd : 1 - ((1 - 2 * ρ - ρ ^ 2) / 2) ^ 2 =
      ((1 - ρ ^ 2) * (3 + ρ ^ 2 + 4 * ρ)) / 4 := by ring
  have hs4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  unfold twoNoiseR twoRootR
  rw [ha, hb, hd]
  simp_rw [Real.sqrt_div' _ (show 0 ≤ (4 : ℝ) by norm_num), Real.sqrt_mul hc, hs4]
  ring

/-- Quantitative Hellinger bound for the complete four-value posterior formula,
valid at every correlation in `[0,1]`, including both endpoints.
@isnad1 id=le.2h1v.s7.8a43ae42c853 from=translated src=- shape=dee606b9 vocab=c4977345
-/
theorem twoNoiseR_gap_bound (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) :
    (4 + Real.sqrt (2 : ℝ) - 3 * Real.sqrt 3) / 4 * ρ ^ 2 ≤
      twoNoiseR ρ - Real.sqrt 3 / 2 + 1 - Real.sqrt (1 - ρ ^ 2) := by
  rw [twoNoiseR_eq_twoRootR ρ hρ0 hρ1]
  exact twoRootR_gap_bound ρ hρ0 hρ1

/-- Strict Hellinger inequality for the canonical two-variable posterior formula.
@isnad1 id=lt.2h1v.s6.b64a662ee0ba from=translated src=- shape=2b725850 vocab=85c239fb
-/
theorem twoNoiseR_hellinger_strict (ρ : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) :
    Real.sqrt 3 / 2 - twoNoiseR ρ < 1 - Real.sqrt (1 - ρ ^ 2) := by
  rw [twoNoiseR_eq_twoRootR ρ (le_of_lt hρ0) hρ1]
  linarith [twoRootR_gap_pos ρ hρ0 hρ1]

/-- The exact four-dimensional moment expression (C.7), as a real polynomial.-/
def fourthMomentExpression (e t : ℝ) : ℝ :=
  ((1 - t) ^ 8 + 32 * t * (1 - t) ^ 6 + (384 - 48 * e) * t ^ 2 * (1 - t) ^ 4 +
    512 * t ^ 3 * (1 - t) ^ 2 + 256 * t ^ 4) / 256

/-- The identity behind the fourth-moment upper bound is valid for all real inputs.
@isnad1 id=eq.0h2v.s7.80706db118b7 from=translated src=- shape=a6752ca8 vocab=1b23445f
-/
theorem fourthMomentExpression_identity (e t : ℝ) :
    fourthMomentExpression e t = bentH t ^ 2 / 256 -
      3 / 16 * (e - 2) * t ^ 2 * (1 - t) ^ 4 := by
  unfold fourthMomentExpression bentH
  ring

/-- Once the graph/rank argument supplies `e ≥ 2`, the moment upper bound follows.
@isnad1 id=le.1h2v.s5.61404d7bf63f from=translated src=- shape=38ce99d5 vocab=afb0bb1f
-/
theorem fourthMomentExpression_le (e t : ℝ) (he : 2 ≤ e) :
    fourthMomentExpression e t ≤ bentH t ^ 2 / 256 := by
  rw [fourthMomentExpression_identity]
  have h : 0 ≤ 3 / 16 * (e - 2) * t ^ 2 * (1 - t) ^ 4 := by positivity
  linarith

/-- The strict sensitivity constant in (C.12); its binomial provenance is separate.
@isnad1 id=lt.0h0v.s6.7b560146187b from=translated src=- shape=14c9b21c vocab=bd0eb148
-/
theorem four_sensitivity_constant :
    (4 : ℝ) / 3 < (3 + 3 * Real.sqrt 2 + 2 * Real.sqrt 3) / 8 := by
  have h2 : (141 : ℝ) / 100 < Real.sqrt 2 := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  have h3 : (173 : ℝ) / 100 < Real.sqrt 3 := by
    apply (Real.lt_sqrt (by norm_num)).mpr
    norm_num
  linarith

/-- Uniform low-noise strictness from the sensitivity lower estimate, for the
whole interval `α ≤ 1/12`. The probabilistic event estimate is an explicit input.
@isnad1 id=lt.3h3v.s7.5ce55067cef9 from=translated src=- shape=797e289c vocab=e7d2045c
-/
theorem four_low_noise_ratio_gt_one (α S ratio : ℝ) (hα : α ≤ 1 / 12)
    (hS : (3 + 3 * Real.sqrt 2 + 2 * Real.sqrt 3) / 8 ≤ S)
    (hratio : (1 - α) ^ 3 * S ≤ ratio) : 1 < ratio := by
  have hS' : (4 : ℝ) / 3 < S := lt_of_lt_of_le four_sensitivity_constant hS
  have hpow : ((11 : ℝ) / 12) ^ 3 ≤ (1 - α) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have hmul := mul_le_mul_of_nonneg_right hpow (show 0 ≤ S by linarith)
  norm_num at hmul
  linarith

/-- Exact rational curvature comparison (4.8).
@isnad1 id=lt.0h0v.s7.bb07091ee281 from=translated src=- shape=8b66aeb6 vocab=39ed9922
-/
theorem high_noise_curvature_constant :
    ((109 : ℝ) ^ 3 / 4000000) ^ 2 < (1 - (169 / 200 : ℝ) ^ 4) ^ 3 := by
  norm_num

end Hellinger.BentEstimates
