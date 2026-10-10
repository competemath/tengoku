import Tengoku.OpenaiMath.OAI.Analysis.SegmentLenses.Pairing

namespace OAI

/-!
# Atomic polar descriptions of finite unit balls
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

section FiniteBodies
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

@[ext] theorem SegmentFamily.ext {F G : SegmentFamily V} (h : F.sets = G.sets) : F = G := by
  have _ := decidableEqV
  cases F
  cases G
  cases h
  rfl

abbrev LocalFamily (K : Finset V) := {F : SegmentFamily V // ∀ S ∈ F.sets, S ⊆ K}

instance localFamilyFinite (K : Finset V) : Finite (LocalFamily K) := by
  let f : LocalFamily K → {s // s ∈ K.powerset.powerset} := fun F =>
    ⟨F.val.sets, Finset.mem_powerset.mpr (fun S hS => Finset.mem_powerset.mpr (F.property S hS))⟩
  exact Finite.of_injective f (fun F G h => Subtype.ext (SegmentFamily.ext
    (congrArg Subtype.val h)))

instance localFamilyFintype (K : Finset V) : Fintype (LocalFamily K) := Fintype.ofFinite _

abbrev FamilyCoefficients (F : SegmentFamily V) := EuclideanSpace ℝ F.sets

abbrev LocalCoefficients (K : Finset V) := (F : LocalFamily K) → FamilyCoefficients F.val

def familyValue (F : SegmentFamily V) : FamilyCoefficients F →ₗ[ℝ] FullDual V where
  toFun c := ∑ S, c S • segmentFunctional S.val
  map_add' c d := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a c := by simp [Finset.smul_sum, mul_smul]

@[simp] theorem familyValue_apply (F : SegmentFamily V) (c : FamilyCoefficients F) (u : Test V) :
    familyValue F c (u : Primal V) = ∑ S, c S * ∑ v ∈ S.val, u.coeff v := by
  have _ := decidableEqV
  simp only [familyValue, LinearMap.coe_mk, AddHom.coe_mk, _root_.sum_apply,
    _root_.smul_apply, smul_eq_mul, segmentFunctional_apply]

def localValue (K : Finset V) : LocalCoefficients K →ₗ[ℝ] FullDual V where
  toFun c := ∑ F, familyValue F.val (c F)
  map_add' c d := by simp [map_add, Finset.sum_add_distrib]
  map_smul' a c := by simp [map_smul, Finset.smul_sum]

def coefficientBudget (K : Finset V) (c : LocalCoefficients K) : ℝ := ∑ F, ‖c F‖

@[continuity, fun_prop] theorem continuous_coefficientBudget (K : Finset V) :
    Continuous (coefficientBudget K) := by
  unfold coefficientBudget
  fun_prop

theorem coefficientBudget_nonneg (K : Finset V) (c : LocalCoefficients K) :
    0 ≤ coefficientBudget K c := Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem norm_le_coefficientBudget (K : Finset V) (c : LocalCoefficients K) :
    ‖c‖ ≤ coefficientBudget K c := by
  apply (pi_norm_le_iff_of_nonneg (coefficientBudget_nonneg K c)).mpr
  intro F
  exact Finset.single_le_sum (fun _ _ => norm_nonneg _) (Finset.mem_univ F)

theorem compact_coefficientBall (K : Finset V) {R : ℝ} (_hR : 0 ≤ R) :
    IsCompact {c : LocalCoefficients K | coefficientBudget K c ≤ R} := by
  apply (isCompact_closedBall (0 : LocalCoefficients K) R).of_isClosed_subset
    (isClosed_le (continuous_coefficientBudget K) continuous_const)
  intro c hc
  simpa only [Metric.mem_closedBall, dist_zero_right] using (norm_le_coefficientBudget K c).trans hc

theorem convex_coefficientBall (K : Finset V) (R : ℝ) :
    Convex ℝ {c : LocalCoefficients K | coefficientBudget K c ≤ R} := by
  intro c hc d hd a b ha hb hab
  change (∑ F, ‖a • c F + b • d F‖) ≤ R
  calc
    (∑ F, ‖a • c F + b • d F‖) ≤ ∑ F, (a * ‖c F‖ + b * ‖d F‖) := by
      apply Finset.sum_le_sum
      intro F hF
      simpa only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb] using
        norm_add_le (a • c F) (b • d F)
    _ = a * coefficientBudget K c + b * coefficientBudget K d := by
      simp only [coefficientBudget, Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ a * R + b * R := add_le_add (mul_le_mul_of_nonneg_left hc ha)
      (mul_le_mul_of_nonneg_left hd hb)
    _ = R := by rw [← add_mul, hab, one_mul]

def atomicBody (K : Finset V) (R : ℝ) : Set (FullDual V) :=
  localValue K '' {c : LocalCoefficients K | coefficientBudget K c ≤ R}

end FiniteBodies

section FinitePolar
variable {V : Type*} [decidableEqV : DecidableEq V] [segmentSystemV : SegmentSystem V]

def Test.ofFinite (K : Finset V) (a : V → ℝ) : Test V :=
  ∑ v ∈ K, a v • Test.ofFinsupp (Finsupp.single v 1)

@[simp] theorem Test.coeff_ofFinite (K : Finset V) (a : V → ℝ) (v : V) :
    (Test.ofFinite K a).coeff v = if v ∈ K then a v else 0 := by
  have _ := segmentSystemV
  change (∑ w ∈ K, a w • Finsupp.single w 1) v = _
  simp [Finsupp.smul_single, Finsupp.single_apply, eq_comm]

theorem Test.support_ofFinite (K : Finset V) (a : V → ℝ) :
    (Test.ofFinite K a).coeff.support ⊆ K := by
  intro v hv
  by_contra hn
  exact Finsupp.mem_support_iff.mp hv (by simp [hn])

@[simp] theorem Test.coe_ofFinite (K : Finset V) (a : V → ℝ) :
    ((Test.ofFinite K a : Test V) : Primal V) = ∑ v ∈ K, a v • unitVector v := by
  have _ := decidableEqV
  change (UniformSpace.Completion.toComplL : Test V →L[ℝ] Primal V) (Test.ofFinite K a) = _
  simp only [Test.ofFinite, map_sum, map_smul]; rfl

@[simp] theorem dual_apply_ofFinite (K : Finset V) (a : V → ℝ) (z : FullDual V) :
    z ((Test.ofFinite K a : Test V) : Primal V) = ∑ v ∈ K, a v * z (unitVector v) := by
  rw [Test.coe_ofFinite]
  simp only [map_sum, map_smul, smul_eq_mul]

def polarTest (K : Finset V) (f : FullDual V →L[ℝ] ℝ) : Test V :=
  Test.ofFinite K (fun v => f (coordinate v))

end FinitePolar

section EuclideanNormalization
variable {ι : Type*} [Fintype ι]

theorem norm_normalized_le (q : EuclideanSpace ℝ ι) : ‖‖q‖⁻¹ • q‖ ≤ 1 := by
  by_cases hq : ‖q‖ = 0
  · simp [hq]
  · rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr (norm_nonneg q)),
      inv_mul_cancel₀ hq]

theorem normalized_pairing (q : EuclideanSpace ℝ ι) :
    (∑ i, (‖q‖⁻¹ • q) i * q i) = ‖q‖ := by
  have hs : (∑ i, q i ^ 2) = ‖q‖ ^ 2 := by
    simp only [EuclideanSpace.norm_sq_eq, Real.norm_eq_abs, sq_abs]
  simp only [PiLp.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
  simp_rw [← sq]
  rw [hs]
  by_cases hq : ‖q‖ = 0
  · simp [hq]
  · field_simp

end EuclideanNormalization

section AtomicSeparation
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V] [TreeOrder V]
  [SegmentSystem V] [IntervalSegments V]

end AtomicSeparation

end SegmentLenses

end

end OAI
