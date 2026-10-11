/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Campanato
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.ParabolicHolderVecOn

/-!
# Campanato Holder

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open scoped ENNReal NNReal Topology
open MeasureTheory MeasureTheory.Measure Set Metric Filter
noncomputable section
namespace CKN.Foundation.Parabolic
/-- Normalized Lᵖ oscillation about the mean on a closed parabolic ball. -/
def ParabolicBallLpOscillation (f : ParabolicPoint → ℝ) (z : ParabolicPoint)
    (r p : ℝ) : ℝ :=
  (⨍ y in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r,
    |f y - ⨍ x in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r, f x| ^ p) ^
      (1 / p)
/-- Uniform Campanato oscillation bound for balls centered in a given set. -/
def ParabolicBallCampanatoBoundOn (f : ParabolicPoint → ℝ) (U : Set ParabolicPoint)
    (R α K p : ℝ) : Prop :=
  ∀ z ∈ U, ∀ {r : ℝ}, 0 < r → r ≤ R →
    ParabolicBallLpOscillation f z r p ≤ K * r ^ α
/-- Campanato oscillation bound at every point and positive radius. -/
def GlobalParabolicBallCampanatoBound (f : ParabolicPoint → ℝ) (α K p : ℝ) : Prop :=
  ∀ z : ParabolicPoint, ∀ {r : ℝ}, 0 < r →
    ParabolicBallLpOscillation f z r p ≤ K * r ^ α
/-- Local integrability data needed to use ball averages and Lᵖ oscillations. -/
def ParabolicBallLpDataOn (f : ParabolicPoint → ℝ) (U : Set ParabolicPoint)
    (R p : ℝ) : Prop :=
  ∀ z ∈ U, ∀ {r : ℝ}, 0 < r → r ≤ R →
    IntegrableOn f (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume ∧
    IntegrableOn (fun q => |f q - ⨍ x in
      @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r, f x| ^ p)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume
/-- Averages over a dyadically shrinking sequence of closed parabolic balls. -/
def ParabolicBallMeanSeq (f : ParabolicPoint → ℝ) (R : ℝ) (z : ParabolicPoint)
    (n : ℕ) : ℝ :=
  ⨍ y in @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z (R / (2 : ℝ) ^ n), f y
/-- Candidate regular representative obtained as the limit of shrinking-ball averages. -/
def parabolicBallRepresentative (f : ParabolicPoint → ℝ) (R : ℝ) (z : ParabolicPoint) : ℝ :=
  limUnder atTop (ParabolicBallMeanSeq f R z)
private lemma ball_dyadic_pos {R : ℝ} (hR : 0 < R) (n : ℕ) : 0 < R / (2 : ℝ) ^ n := by positivity
private lemma ball_dyadic_antitone {R : ℝ} (hR : 0 < R) {m n : ℕ} (hmn : m ≤ n) :
    R / (2 : ℝ) ^ n ≤ R / (2 : ℝ) ^ m := by
  exact div_le_div_of_nonneg_left hR.le (by positivity) (pow_le_pow_right₀ (by norm_num) hmn)
private lemma ball_dyadic_le {R : ℝ} (hR : 0 < R) (n : ℕ) : R / (2 : ℝ) ^ n ≤ R := by
  simpa using ball_dyadic_antitone hR (Nat.zero_le n)
private lemma ball_dyadic_rpow {R : ℝ} (hR : 0 ≤ R) (α : ℝ) : ∀ n : ℕ,
      (R / (2 : ℝ) ^ n) ^ α = R ^ α * ((2 : ℝ) ^ (-α)) ^ n
  | 0 => by simp
  | n + 1 => by
      have hsplit :
          R / (2 : ℝ) ^ (n + 1) = (R / (2 : ℝ) ^ n) / 2 := by
        rw [pow_succ]
        ring
      have hrn : 0 ≤ R / (2 : ℝ) ^ n := div_nonneg hR (by positivity)
      rw [hsplit, Real.div_rpow hrn (by norm_num), ball_dyadic_rpow hR α n,
        pow_succ, Real.rpow_neg (by norm_num)]
      field_simp
/-- Closed Euclidean ball in native spatial coordinates. -/
def vec3ClosedBall (x : Vec3) (r : ℝ) : Set Vec3 :=
  {y | vec3EuclideanNorm (y - x) ≤ r}
/-- Linear spatial dilation used to compute the volumes of scaled balls. -/
def campanatoHolderVec3ScaleLinear (a : ℝ) : Vec3 →ₗ[ℝ] Vec3 :=
  a • LinearMap.id
private lemma vec3ScaleLinear_apply (a : ℝ) (v : Vec3) :
    campanatoHolderVec3ScaleLinear a v = a • v := by
  rfl
private lemma vec3ScaleLinear_det (a : ℝ) :
    LinearMap.det (campanatoHolderVec3ScaleLinear a) = a ^ 3 := by
  simp [campanatoHolderVec3ScaleLinear, LinearMap.det_smul, LinearMap.det_id]
theorem parabolicBall_dyadic_pos {R : ℝ} (hR : 0 < R) (n : ℕ) :
    0 < R / (2 : ℝ) ^ n :=
  ball_dyadic_pos hR n
theorem parabolicBall_dyadic_le {R : ℝ} (hR : 0 < R) (n : ℕ) :
    R / (2 : ℝ) ^ n ≤ R :=
  ball_dyadic_le hR n
theorem parabolicBall_dyadic_rpow {R : ℝ} (hR : 0 ≤ R) (α : ℝ) (n : ℕ) :
    (R / (2 : ℝ) ^ n) ^ α = R ^ α * ((2 : ℝ) ^ (-α)) ^ n :=
  ball_dyadic_rpow hR α n
private theorem average_sub_const_le_rpow_outer
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {A B : Set α} {c p D : ℝ} (hBA : B ⊆ A)
    (hApos : 0 < μ A) (hAtop : μ A < ∞)
    (hBpos : 0 < μ B) (hBtop : μ B < ∞)
    (hfA : IntegrableOn f A μ)
    (hfpA : IntegrableOn (fun x => |f x - c| ^ p) A μ)
    (hp : 1 ≤ p) (hD : (μ A).toReal / (μ B).toReal ≤ D) :
    |(⨍ x in B, f x ∂μ) - c| ≤
      D ^ (1 / p) * (⨍ x in A, |f x - c| ^ p ∂μ) ^ (1 / p) := by
  have hfB : IntegrableOn f B μ := hfA.mono_set hBA
  have hconstA : IntegrableOn (fun _ : α => c) A μ := integrableOn_const hAtop.ne
  have hconstB : IntegrableOn (fun _ : α => c) B μ := integrableOn_const hBtop.ne
  have hdiff :
      (⨍ x in B, (f - fun _ : α => c) x ∂μ) =
        (⨍ x in B, f x ∂μ) - c := by
    rw [MeasureTheory.setAverage_sub hfB hconstB,
      MeasureTheory.setAverage_const hBpos.ne' hBtop.ne]
  have hpowB : IntegrableOn (fun x => |f x - c| ^ p) B μ := hfpA.mono_set hBA
  have hfirst :
      |(⨍ x in B, f x ∂μ) - c| ≤
        (⨍ x in B, |f x - c| ^ p ∂μ) ^ (1 / p) := by
    rw [← hdiff]
    simpa only [Real.norm_eq_abs, Pi.sub_apply, one_div, one_mul] using
      (Integration.setAverage_abs_le_rpow_mean hp hBpos hBtop
        (hfB.sub hconstB) hpowB)
  have houter := average_abs_le_outer_average_abs hBA hApos hAtop hBpos hBtop
    hfpA
  have houter' :
      (⨍ x in B, |f x - c| ^ p ∂μ) ≤
        (μ A).toReal / (μ B).toReal *
          (⨍ x in A, |f x - c| ^ p ∂μ) := by
    simpa only [abs_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)] using houter
  have hroot : 0 ≤ (1 / p : ℝ) := by positivity
  have hnonnegB : 0 ≤ ⨍ x in B, |f x - c| ^ p ∂μ :=
    Integration.setAverage_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (abs_nonneg _) _)
  have hnonnegA : 0 ≤ ⨍ x in A, |f x - c| ^ p ∂μ :=
    Integration.setAverage_nonneg_of_ae (Filter.Eventually.of_forall fun x =>
      Real.rpow_nonneg (abs_nonneg _) _)
  have hD0 : 0 ≤ D := by
    exact le_trans (div_nonneg (ENNReal.toReal_nonneg) (by positivity)) hD
  have hroot' := Real.rpow_le_rpow hnonnegB houter' hroot
  calc
    _ ≤ (⨍ x in B, |f x - c| ^ p ∂μ) ^ (1 / p) := hfirst
    _ ≤ ((μ A).toReal / (μ B).toReal *
        (⨍ x in A, |f x - c| ^ p ∂μ)) ^ (1 / p) := hroot'
    _ ≤ (D * (⨍ x in A, |f x - c| ^ p ∂μ)) ^ (1 / p) := by
      gcongr
    _ = D ^ (1 / p) * (⨍ x in A, |f x - c| ^ p ∂μ) ^ (1 / p) := by
      rw [Real.mul_rpow hD0 hnonnegA]
theorem abs_setAverage_sub_setAverage_le
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f : α → ℝ} {A B : Set α} {p D : ℝ} (hBA : B ⊆ A)
    (hApos : 0 < μ A) (hAtop : μ A < ∞)
    (hBpos : 0 < μ B) (hBtop : μ B < ∞)
    (hfA : IntegrableOn f A μ)
    (hfpA : IntegrableOn
      (fun x => |f x - ⨍ y in A, f y ∂μ| ^ p) A μ)
    (hp : 1 ≤ p) (hD : (μ A).toReal / (μ B).toReal ≤ D) :
    |(⨍ x in B, f x ∂μ) - ⨍ x in A, f x ∂μ| ≤
      D ^ (1 / p) *
        (⨍ x in A, |f x - ⨍ y in A, f y ∂μ| ^ p ∂μ) ^ (1 / p) := by
  simpa only using
    (average_sub_const_le_rpow_outer hBA hApos hAtop hBpos hBtop hfA hfpA hp hD)
theorem abs_parabolicBallRepresentative_sub_meanSeq_le
    {f : ParabolicPoint → ℝ} {R α C : ℝ} {z : ParabolicPoint}
    (hα : 0 < α) (hstep : ∀ n : ℕ,
      dist (ParabolicBallMeanSeq f R z n)
          (ParabolicBallMeanSeq f R z (n + 1)) ≤
        C * ((2 : ℝ) ^ (-α)) ^ n) (n : ℕ) :
    |parabolicBallRepresentative f R z - ParabolicBallMeanSeq f R z n| ≤
      parabolicCampanatoTailConstant α * C * ((2 : ℝ) ^ (-α)) ^ n := by
  have hq : (2 : ℝ) ^ (-α) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith only [hα])
  have htendsto : Tendsto (ParabolicBallMeanSeq f R z) atTop
      (𝓝 (parabolicBallRepresentative f R z)) :=
    (cauchySeq_of_le_geometric ((2 : ℝ) ^ (-α)) C hq hstep).tendsto_limUnder
  have hbase := dist_le_of_le_geometric_of_tendsto
    ((2 : ℝ) ^ (-α)) C hq hstep
    htendsto n
  rw [Real.dist_eq, abs_sub_comm] at hbase
  refine hbase.trans_eq ?_
  unfold parabolicCampanatoTailConstant
  field_simp
/-- Integrability data for ball averages and oscillations at all points and radii. -/
def GlobalParabolicBallLpData
    (f : ParabolicPoint → ℝ) (p : ℝ) : Prop :=
  ∀ z : ParabolicPoint, ∀ {r : ℝ}, 0 < r →
    IntegrableOn f
        (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume ∧
    IntegrableOn
      (fun q => |f q - ⨍ x in
        @Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r, f x| ^ p)
      (@Metric.closedBall ParabolicPoint parabolicPseudoMetricSpace z r) volume
/-- Explicit coefficient converting a Campanato bound to a Hölder bound. -/
def parabolicCampanatoHolderConstant (α p : ℝ) : ℝ :=
  (2 * parabolicCampanatoTailConstant α + 1) *
    (2 : ℝ) ^ (5 / p) * (8 : ℝ) ^ α

theorem parabolicBallRepresentative_ae_eq
    {f : ParabolicPoint → ℝ} {R : ℝ}
    (hlim : ∀ᵐ z ∂(volume : Measure ParabolicPoint),
      Tendsto (ParabolicBallMeanSeq f R z) atTop (𝓝 (f z))) :
    parabolicBallRepresentative f R =ᵐ[volume] f := by
  filter_upwards [hlim] with z hz
  exact hz.limUnder_eq
end CKN.Foundation.Parabolic
