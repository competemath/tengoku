import Tengoku.OpenaiMath.OAI.MathematicalPhysics.CriticalSK.SphereSaddle

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
namespace CriticalSK

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
lemma sphereInner_rotation (U : Matrix.orthogonalGroup ι ℝ) (x y : unitSphere ι) :
    inner ℝ (orthogonalSphere U x).val (orthogonalSphere U y).val = inner ℝ x.val y.val :=
  (orthogonalIsometry U).inner_map_map x.val y.val

omit [DecidableEq ι] in
lemma sphereTilted_uniform_integral (lam : ι → ℝ) (a r : ℝ) (F : unitSphere ι → ℝ) :
    (∫ u, F u ∂sphereTilted lam a r) =
      (∫ u, Real.exp (a/2*diagonalEnergy lam (r • u.val))*F u ∂sphereUniform) /
        spherePartition lam a r := by
  rw [sphereTilted_integral,sphereUniform_integral,spherePartition,sphereAverage,sphereAverage]
  have ha := ne_of_gt (sphereArea_pos (ι := ι))
  field_simp [ha]

omit [DecidableEq ι] in
lemma sphereTilted_pair_integral (lam : ι → ℝ) (r : ℝ)
    (F : unitSphere ι × unitSphere ι → ℝ) (hF : Continuous F) :
    (∫ p, F p ∂((sphereTilted lam 1 r).prod (sphereTilted lam 1 r))) =
      (∫ p, spherePairEnergy lam r p*F p ∂(sphereUniform.prod sphereUniform)) /
        spherePartition lam 1 r^2 := by
  have hi : Integrable F ((sphereTilted lam 1 r).prod (sphereTilted lam 1 r)) := by
    simpa only [integrableOn_univ] using hF.continuousOn.integrableOn_compact isCompact_univ
  have hi' : Integrable (fun p => spherePairEnergy lam r p*F p)
      (sphereUniform.prod sphereUniform) := by
    have hc : Continuous (fun p : unitSphere ι × unitSphere ι => spherePairEnergy lam r p * F p) :=
      (spherePairEnergy_continuous lam r).mul hF
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [integral_prod _ hi,integral_prod _ hi']
  simp_rw [sphereTilted_uniform_integral]
  simp_rw [spherePairEnergy_factor,mul_assoc,integral_const_mul]
  simp_rw [← mul_div_assoc,integral_div]
  rw [div_div,← pow_two]

end

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateReflection (i : ι) : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι :=
  LinearIsometryEquiv.piLpCongrRight 2 (fun j =>
    if j=i then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ)

lemma coordinateReflection_apply (i j : ι) (x : EuclideanSpace ℝ ι) :
    coordinateReflection i x j = if j=i then -x j else x j := by
  classical
  simp only [coordinateReflection, LinearIsometryEquiv.piLpCongrRight_apply, PiLp.toLp_apply]
  split_ifs <;> rfl

lemma coordinateReflection_energy (lam : ι → ℝ) (i : ι) (x : EuclideanSpace ℝ ι) :
    diagonalEnergy lam (coordinateReflection i x) = diagonalEnergy lam x := by
  unfold diagonalEnergy
  apply Finset.sum_congr rfl
  intro j _
  rw [coordinateReflection_apply]
  split_ifs <;> ring

omit [DecidableEq ι] in
lemma sphereMap_measurableEmbedding (U : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] EuclideanSpace ℝ ι) :
    MeasurableEmbedding (sphereMap U) := by
  apply (sphereMap_continuous U).measurableEmbedding
  intro u w h
  apply Subtype.ext
  exact U.injective (congrArg Subtype.val h)

variable [Nonempty ι]

lemma sphereTilted_coordinate_cross (lam : ι → ℝ) (a r : ℝ) (i j : ι) (hij : i ≠ j) :
    (∫ u : unitSphere ι, ((r • u.val) i) * ((r • u.val) j) ∂sphereTilted lam a r) = 0 := by
  rw [sphereTilted_integral]
  suffices hn : (∫ u : unitSphere ι, Real.exp (a/2*diagonalEnergy lam (r • u.val)) *
      ((r • u.val) i * (r • u.val) j) ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) = 0 by
    rw [hn, zero_div]
  let F := fun u : unitSphere ι => Real.exp (a/2*diagonalEnergy lam (r • u.val)) *
      ((r • u.val) i * (r • u.val) j)
  have he (u : unitSphere ι) : F (sphereMap (coordinateReflection i) u) = -F u := by
    dsimp [F, sphereMap]
    rw [← (coordinateReflection i).map_smul, coordinateReflection_energy]
    simp only [coordinateReflection_apply]
    simp only [ite_eq_left, ite_eq_right hij.symm]
    ring
  have hi := (sphereMap_preserving (coordinateReflection i)).integral_comp
    (sphereMap_measurableEmbedding _) F
  simp_rw [he, integral_neg] at hi
  change (∫ u, F u ∂(volume : Measure (EuclideanSpace ℝ ι)).toSphere) = 0
  linarith only [hi]

end

section

lemma gaussianPairPrefactor_antitone {a b c d : ℝ≥0} (ha : a ≠ 0) (hb : b ≠ 0)
    (hac : a ≤ c) (hbd : b ≤ d) :
    gaussianPairPrefactor c d ≤ gaussianPairPrefactor a b := by
  unfold gaussianPairPrefactor
  have ha' : 0 < (a:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ha)
  have hb' : 0 < (b:ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hb)
  apply inv_anti₀ (by positivity)
  apply mul_le_mul
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hac) (by positivity))
  · exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (NNReal.coe_le_coe.mpr hbd) (by positivity))
  · positivity
  · positivity

variable {n : ℕ}

end

section

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] in
lemma sphereTilted_continuous_integrable (lam : ι → ℝ) (a r : ℝ) {f : unitSphere ι → ℝ}
    (hf : Continuous f) : Integrable f (sphereTilted lam a r) := by
  simpa only [integrableOn_univ] using hf.continuousOn.integrableOn_compact isCompact_univ

lemma sphereTilted_linear_square (lam : ι → ℝ) (a r : ℝ) (c : ι → ℝ) :
    (∫ u : unitSphere ι, (∑ i, c i * (r • u.val) i)^2 ∂sphereTilted lam a r) =
      ∑ i, c i^2 * (∫ u : unitSphere ι, ((r • u.val) i)^2 ∂sphereTilted lam a r) := by
  have hh (u : unitSphere ι) : (∑ i, c i*(r • u.val) i)^2 =
      ∑ i, ∑ j, c i*c j*((r • u.val) i*(r • u.val) j) := by
    simp only [pow_two, Finset.sum_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp_rw [hh]
  rw [integral_finsetSum _ (fun i _ => sphereTilted_continuous_integrable lam a r (by fun_prop))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_finsetSum _ (fun j _ => sphereTilted_continuous_integrable lam a r (by fun_prop))]
  simp_rw [integral_const_mul]
  rw [Finset.sum_eq_single i]
  · simp only [pow_two]
  · intro j _ hji
    rw [sphereTilted_coordinate_cross lam a r i j hji.symm, mul_zero]
  · simp

lemma sphereTilted_linear_square_le (lam : ι → ℝ) (a r : ℝ) (C : ℝ)
    (hC : ∀ i, (∫ u : unitSphere ι, ((r • u.val) i)^2 ∂sphereTilted lam a r) ≤ C)
    (c : ι → ℝ) :
    (∫ u : unitSphere ι, (∑ i, c i*(r • u.val) i)^2 ∂sphereTilted lam a r) ≤
      C*(∑ i, c i^2) := by
  rw [sphereTilted_linear_square, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_comm C] using mul_le_mul_of_nonneg_left (hC i) (sq_nonneg (c i))

end

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma sphereTilted_overlap_moment (lam : ι → ℝ) (a r : ℝ) :
    (∫ p : unitSphere ι × unitSphere ι,
      (inner ℝ (r • p.1.val) (r • p.2.val))^2
      ∂((sphereTilted lam a r).prod (sphereTilted lam a r))) =
      ∑ i, (∫ u : unitSphere ι, ((r • u.val) i)^2 ∂sphereTilted lam a r)^2 := by
  have hc : Continuous (fun p : unitSphere ι × unitSphere ι =>
      (inner ℝ (r • p.1.val) (r • p.2.val))^2) := by fun_prop
  have hi : Integrable (fun p : unitSphere ι × unitSphere ι =>
      (inner ℝ (r • p.1.val) (r • p.2.val))^2)
      ((sphereTilted lam a r).prod (sphereTilted lam a r)) := by
    simpa only [integrableOn_univ] using hc.continuousOn.integrableOn_compact isCompact_univ
  rw [integral_prod _ hi]
  simp_rw [EuclideanSpace.inner_eq_star_dotProduct,star_trivial,dotProduct,mul_comm]
  simp_rw [sphereTilted_linear_square]
  rw [integral_finsetSum _ (fun i _ => sphereTilted_continuous_integrable lam a r (by fun_prop))]
  simp_rw [integral_mul_const,pow_two]

lemma sphereTilted_overlap_bound (lam : ι → ℝ) (a r C : ℝ) (v : ι → ℝ)
    (hm : ∀ i, (∫ u : unitSphere ι, ((r • u.val) i)^2 ∂sphereTilted lam a r) ≤ C*v i) :
    (∫ p : unitSphere ι × unitSphere ι,
      (inner ℝ (r • p.1.val) (r • p.2.val))^2
      ∂((sphereTilted lam a r).prod (sphereTilted lam a r))) ≤ C^2*(∑ i, v i^2) := by
  rw [sphereTilted_overlap_moment,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  simpa only [mul_pow] using pow_le_pow_left₀
    (integral_nonneg (fun _ => sq_nonneg _)) (hm i) 2

end CriticalSK

end

end OAI
