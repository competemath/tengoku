import Tengoku.OpenaiMath.OAI.MathematicalPhysics.CriticalSK.CubeOverlap
import Tengoku.OpenaiMath.OAI.MathematicalPhysics.CriticalSK.OverlapMoments

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

open scoped BigOperators NNReal ENNReal Topology Pointwise Matrix.Norms.Elementwise

open Set Metric MeasureTheory MeasureTheory.Measure

open scoped ENNReal NNReal Topology

open MeasureTheory MeasureTheory.Measure Set Metric

open scoped BigOperators ENNReal Topology

open Set MeasureTheory

open scoped BigOperators ENNReal

open MeasureTheory

open Finset Real

open Finset Real Filter

open scoped Topology

open MeasureTheory Filter Set Real

open scoped ENNReal NNReal BigOperators

open scoped NNReal ENNReal BigOperators

open scoped NNReal ENNReal

open ProbabilityTheory

open Metric Set MeasureTheory

open scoped ENNReal Pointwise

open MeasureTheory Filter Set
namespace CriticalSK

section

def rotatedCubePair {n : ℕ} (lam : Fin n → ℝ) (g : ℝ → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  (Fintype.card (Spin n) : ℝ)⁻¹^2 * ∑ x : Spin n, ∑ y : Spin n,
    g (cubeOverlap x y)*Real.exp ((diagonalEnergy lam (orthogonalIsometry U (cubeVector x))+
      diagonalEnergy lam (orthogonalIsometry U (cubeVector y)))/2)

lemma rotatedCubePair_continuous {n : ℕ} (lam : Fin n → ℝ) (g : ℝ → ℝ) :
    Continuous (rotatedCubePair lam g) := by
  apply Continuous.const_mul
  apply continuous_finsetSum
  intro x _
  apply continuous_finsetSum
  intro y _
  exact (cube_pair_energy_continuous lam x y).const_mul _

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
lemma sphereRestricted_as_tilted (lam : ι → ℝ) (a r b : ℝ) (i : ι) :
    sphereAverage (fun u => if |(r • u.val) i| ≤ b then
      Real.exp (a/2*diagonalEnergy lam (r • u.val)) else 0) =
      spherePartition lam a r * (sphereTilted lam a r).real
        {u : unitSphere ι | |(r • u.val) i| ≤ b} := by
  have hA : MeasurableSet {u : unitSphere ι | |(r • u.val) i| ≤ b} :=
    measurableSet_le (by fun_prop) measurable_const
  rw [Measure.real,sphereTilted_apply_real lam a r hA,← integral_indicator hA]
  unfold spherePartition sphereAverage
  have hZ := (sphereWeight_integral_pos lam a r).ne'
  have he : (fun u : unitSphere ι => if |(r • u.val) i| ≤ b then
      Real.exp (a/2*diagonalEnergy lam (r • u.val)) else 0) =
      {u : unitSphere ι | |(r • u.val) i| ≤ b}.indicator
        (fun u => Real.exp (a/2*diagonalEnergy lam (r • u.val))) := rfl
  rw [he]
  simp only [div_mul_eq_mul_div] at hZ ⊢
  field_simp [hZ]

end

def rotatedCubeRestricted {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  (Fintype.card (Spin n):ℝ)⁻¹ * ∑ x : Spin n,
    if |(orthogonalIsometry U (cubeVector x)) i| ≤ b then
      Real.exp (a/2*diagonalEnergy lam (orthogonalIsometry U (cubeVector x))) else 0

lemma rotatedCubeRestricted_measurable {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n) :
    Measurable (rotatedCubeRestricted lam a b i) := by
  unfold rotatedCubeRestricted
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro x _
  have hc := orthogonalIsometry_fixed_continuous (cubeVector x)
  apply Measurable.ite (measurableSet_le ((EuclideanSpace.proj i).continuous.comp hc).abs.measurable measurable_const)
  · exact ((continuous_const.mul ((diagonalEnergy_continuous lam).comp hc)).rexp).measurable
  · exact measurable_const

lemma rotatedCubeRestricted_nonneg {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 ≤ rotatedCubeRestricted lam a b i U := by
  unfold rotatedCubeRestricted
  positivity

lemma rotatedCubeRestricted_le {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : rotatedCubeRestricted lam a b i U ≤ rotatedCubePartition lam a U := by
  unfold rotatedCubeRestricted rotatedCubePartition
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Finset.sum_le_sum
  intro x _
  split_ifs
  · exact le_rfl
  · exact (Real.exp_pos _).le

lemma rotatedCubeRestricted_integrable {n : ℕ} (lam : Fin n → ℝ) (a b : ℝ) (i : Fin n) :
    Integrable (rotatedCubeRestricted lam a b i) (orthogonalHaar (Fin n)) := by
  apply (orthogonalHaar_integrable (rotatedCubePartition_continuous lam a)).mono'
    (rotatedCubeRestricted_measurable lam a b i).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun U => by
    rw [Real.norm_eq_abs,abs_of_nonneg (rotatedCubeRestricted_nonneg lam a b i U)]
    exact rotatedCubeRestricted_le lam a b i U)

lemma divided_mass_variance_bound {A Z S : ℝ} (hA : 0 ≤ A) (hAZ : A ≤ Z)
    (hZ : 0 < Z) (hS : 0 < S) : A/Z ≤ 2*A/S+4*(Z/S-1)^2 := by
  by_cases hz : S/2 ≤ Z
  · have hh : A/Z ≤ 2*A/S := by
      rw [div_le_div_iff₀ hZ hS]
      nlinarith [mul_nonneg hA (sub_nonneg.mpr hz)]
    linarith [sq_nonneg (Z/S-1)]
  · have hratio : A/Z ≤ 1 := (div_le_one hZ).mpr hAZ
    have hfrac : Z/S < 1/2 := (div_lt_iff₀ hS).mpr (by linarith)
    have hfrac0 : 0 ≤ Z/S := div_nonneg hZ.le hS.le
    have he : 1 ≤ 4*(Z/S-1)^2 := by nlinarith [sq_nonneg (Z/S)]
    have hnon : 0 ≤ 2*A/S := by positivity
    linarith

lemma normalized_pair_event_bound {B Z S K : ℝ} (hB : 0 ≤ B) (hZ : 0 < Z)
    (hS : 0 < S) (hK : 0 < K) (hlarge : K ≤ B/Z^2) :
    1 ≤ 4*(Z/S-1)^2+4*(B/S^2)/K := by
  by_cases hz : S/2 ≤ Z
  · have hf : 1 ≤ 4*(B/S^2)/K := by
      have hb := (le_div_iff₀ (sq_pos_of_pos hZ)).mp hlarge
      have hsq : S^2 ≤ 4*Z^2 := by nlinarith
      apply (le_div_iff₀ hK).mpr
      rw [← mul_div_assoc]
      apply (le_div_iff₀ (sq_pos_of_pos hS)).mpr
      nlinarith [mul_le_mul_of_nonneg_left hsq hK.le]
    linarith [sq_nonneg (Z/S-1)]
  · have hfrac : Z/S < 1/2 := (div_lt_iff₀ hS).mpr (by linarith)
    have hfrac0 : 0 ≤ Z/S := div_nonneg hZ.le hS.le
    have he : 1 ≤ 4*(Z/S-1)^2 := by nlinarith [sq_nonneg (Z/S)]
    have hnon : 0 ≤ 4*(B/S^2)/K := by positivity
    linarith

lemma integral_dominates_event {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    [IsFiniteMeasure μ] {E : Set Ω} {f : Ω → ℝ}
    (hi : Integrable f μ) (hf : ∀ x, 0 ≤ f x) (he : ∀ x ∈ E, 1 ≤ f x) :
    μ.real E ≤ ∫ x, f x ∂μ := by
  apply (measureReal_mono (show E ⊆ {x | 1 ≤ f x} from he)).trans
  simpa only [one_mul] using mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall hf) hi 1

lemma rotatedCubePartition_pos {n : ℕ} (lam : Fin n → ℝ) (a : ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 < rotatedCubePartition lam a U := by
  unfold rotatedCubePartition
  apply mul_pos (by positivity)
  exact Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

def rotatedCubeSmallBall {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  rotatedCubeRestricted lam 1 b i U/rotatedCubePartition lam 1 U

lemma rotatedCubeSmallBall_measurable {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n) :
    Measurable (rotatedCubeSmallBall lam b i) :=
  (rotatedCubeRestricted_measurable lam 1 b i).div (rotatedCubePartition_continuous lam 1).measurable

lemma rotatedCubeSmallBall_nonneg {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 ≤ rotatedCubeSmallBall lam b i U :=
  div_nonneg (rotatedCubeRestricted_nonneg lam 1 b i U) (rotatedCubePartition_pos lam 1 U).le

lemma rotatedCubeSmallBall_le_one {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : rotatedCubeSmallBall lam b i U ≤ 1 :=
  (div_le_one (rotatedCubePartition_pos lam 1 U)).mpr (rotatedCubeRestricted_le lam 1 b i U)

lemma rotatedCubeSmallBall_integrable {n : ℕ} (lam : Fin n → ℝ) (b : ℝ) (i : Fin n) :
    Integrable (rotatedCubeSmallBall lam b i) (orthogonalHaar (Fin n)) := by
  apply (integrable_const (1:ℝ)).mono' (rotatedCubeSmallBall_measurable lam b i).aestronglyMeasurable
  filter_upwards [] with U
  rw [Real.norm_eq_abs,abs_of_nonneg (rotatedCubeSmallBall_nonneg lam b i U)]
  exact rotatedCubeSmallBall_le_one lam b i U

def rotatedCubeOverlap {n : ℕ} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : ℝ :=
  rotatedCubePair lam (fun q => q^2) U/rotatedCubePartition lam 1 U^2

lemma rotatedCubePair_square_nonneg {n : ℕ} (lam : Fin n → ℝ)
    (U : Matrix.orthogonalGroup (Fin n) ℝ) : 0 ≤ rotatedCubePair lam (fun q => q^2) U := by
  unfold rotatedCubePair
  positivity

lemma rotatedCubeOverlap_probability {n : ℕ} (hn : 0 < n) (lam : Fin n → ℝ) {K : ℝ} (hK : 0 < K) :
    (orthogonalHaar (Fin n)).real {U | K ≤ rotatedCubeOverlap lam U} ≤
      4*(∫ U, (rotatedCubePartition lam 1 U/spherePartition lam 1 (Real.sqrt n)-1)^2 ∂orthogonalHaar (Fin n))+
      4*((∫ U, rotatedCubePair lam (fun q => q^2) U ∂orthogonalHaar (Fin n))/spherePartition lam 1 (Real.sqrt n)^2)/K := by
  let : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  let S := spherePartition lam 1 (Real.sqrt n)
  have hS : 0 < S := spherePartition_pos _ _ _
  have hV : Integrable (fun U => (rotatedCubePartition lam 1 U / S - 1)^2) (orthogonalHaar (Fin n)) := orthogonalHaar_integrable (((rotatedCubePartition_continuous lam 1).div_const S).sub continuous_const |>.pow 2)
  have hB := orthogonalHaar_integrable (rotatedCubePair_continuous lam (fun q => q^2))
  have hh := integral_dominates_event ((hV.const_mul 4).add (((hB.div_const (S^2)).const_mul 4).div_const K))
    (fun U => by dsimp; have := rotatedCubePair_square_nonneg lam U; positivity) (fun U hU => normalized_pair_event_bound
      (rotatedCubePair_square_nonneg lam U) (rotatedCubePartition_pos lam 1 U) hS hK hU)
  simp only [Pi.add_apply] at hh
  rw [integral_add (hV.const_mul 4) (((hB.div_const (S^2)).const_mul 4).div_const K),
    integral_const_mul,integral_div,integral_const_mul,integral_div] at hh
  exact hh

end CriticalSK

end

end OAI
