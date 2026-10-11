/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
module

public import Tengoku.BrownianMotion.BrownianMotion.Auxiliary.MeasureTheory
public import Tengoku.BrownianMotion.BrownianMotion.Auxiliary.NNReal
public import Tengoku.BrownianMotion.BrownianMotion.Gaussian.Gaussian
public import Tengoku

/-!
# Pre-Brownian motion as a projective limit

-/

@[expose] public section

open MeasureTheory NormedSpace Set
open scoped ENNReal NNReal

namespace L2

variable {ι : Type*} [Finite ι]
variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/- In an `L2` space, the matrix of intersections of pairs of sets is positive semi-definite. -/
/--
@isnad1 id=possemid.1h6v.s7.f0734ca61a5e from=translated src=- shape=bee88248 vocab=3e7570d1
-/
lemma posSemidef_interMatrix {μ : Measure α} {v : ι → (Set α)}
    (hv₁ : ∀ j, MeasurableSet (v j)) (hv₂ : ∀ j, μ (v j) ≠ ∞ := by finiteness) :
    Matrix.PosSemidef (Matrix.of fun i j : ι ↦ μ.real (v i ∩ v j)) := by
  simp only [hv₁, ne_eq, hv₂, not_false_eq_true,
    ← L2.real_inner_indicatorConstLp_one_indicatorConstLp_one]
  exact Matrix.posSemidef_gram ℝ _

end L2

namespace ProbabilityTheory

variable {ι : Type*} {d : ℕ}

def brownianCovMatrix (I : Finset ℝ≥0) : Matrix I I ℝ := Matrix.of fun s t ↦ min s.1 t.1

/--
@isnad1 id=eq.0h3v.s6.71cca20cf3a3 from=translated src=- shape=0b65a989 vocab=74890623
-/
lemma brownianCovMatrix_apply {I : Finset ℝ≥0} (s t : I) :
    brownianCovMatrix I s t = min s.1 t.1 := rfl

/--
@isnad1 id=eq.1h2v.s8.ed5caf2f71f1 from=translated src=- shape=c7bb87cf vocab=8e96d0cc
-/
lemma brownianCovMatrix_submatrix {I J : Finset ℝ≥0} (hJI : J ⊆ I) :
    (brownianCovMatrix I).submatrix (fun i : J ↦ ⟨i.1, hJI i.2⟩) (fun i : J ↦ ⟨i.1, hJI i.2⟩) =
    brownianCovMatrix J := rfl

/--
@isnad1 id=possemid.0h1v.s4.1c07d6d719e4 from=translated src=- shape=557e19fe vocab=2dfd6159
-/
lemma posSemidef_brownianCovMatrix (I : Finset ℝ≥0) :
    (brownianCovMatrix I).PosSemidef := by
  have h : brownianCovMatrix I =
      fun s t ↦ volume.real ((Icc 0 s.1.toReal) ∩ (Icc 0 t.1.toReal)) := by
    simp [Icc_inter_Icc, max_self, Real.volume_real_Icc, sub_zero, le_inf_iff,
      NNReal.zero_le_coe, and_self, sup_of_le_left]
    rfl
  exact h ▸ L2.posSemidef_interMatrix (fun j ↦ measurableSet_Icc)
    (fun j ↦ isCompact_Icc.measure_ne_top)

variable [DecidableEq ι]

noncomputable
def gaussianProjectiveFamily (I : Finset ℝ≥0) : Measure (I → ℝ) :=
  multivariateGaussian 0 (brownianCovMatrix I) |>.map (MeasurableEquiv.toLp 2 (I → ℝ)).symm

/--
@isnad1 id=measurep.0h1v.s10.ea80885b8681 from=translated src=- shape=a40bb3d0 vocab=58202678
-/
lemma measurePreserving_equiv_multivariateGaussian (I : Finset ℝ≥0) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (I → ℝ)).symm
      (multivariateGaussian 0 (brownianCovMatrix I)) (gaussianProjectiveFamily I) where
  measurable := by fun_prop
  map_eq := rfl

/--
@isnad1 id=measurep.0h1v.s10.8d8b113b7ed1 from=translated src=- shape=6d0a9868 vocab=58202678
-/
lemma measurePreserving_equiv_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    MeasurePreserving (MeasurableEquiv.toLp 2 (I → ℝ)).symm.symm (gaussianProjectiveFamily I)
      (multivariateGaussian 0 (brownianCovMatrix I)) where
  measurable := by fun_prop
  map_eq := by
    rw [gaussianProjectiveFamily, Measure.map_map, MeasurableEquiv.symm_comp_self,
      Measure.map_id]
    all_goals fun_prop

/--
@isnad1 id=eq.0h3v.s11.990e1ad65520 from=translated src=- shape=2757af39 vocab=d9ce1974
-/
lemma integral_gaussianProjectiveFamily {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (I : Finset ℝ≥0) (f : (I → ℝ) → E) :
    ∫ x, f x ∂gaussianProjectiveFamily I =
      ∫ x, f (EuclideanSpace.equiv I ℝ x)
        ∂multivariateGaussian 0 (brownianCovMatrix I) := by
  simp only [gaussianProjectiveFamily, integral_map_equiv, MeasurableEquiv.toLp_symm_apply]
  rfl

/--
@isnad1 id=isgaussi.0h1v.s7.95a26dfbde81 from=translated src=- shape=a5866a25 vocab=1f029265
-/
instance isGaussian_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    IsGaussian (gaussianProjectiveFamily I) := by
  unfold gaussianProjectiveFamily
  rw [MeasurableEquiv.coe_toLp_symm_eq]
  infer_instance

/--
@isnad1 id=eq.0h1v.s8.cf5cb49fbc7d from=translated src=- shape=58b792e6 vocab=025932bd
-/
@[simp]
lemma integral_id_gaussianProjectiveFamily (I : Finset ℝ≥0) :
    ∫ x, x ∂(gaussianProjectiveFamily I) = 0 := by
  rw [integral_gaussianProjectiveFamily, ← ContinuousLinearEquiv.coe_coe,
    ContinuousLinearMap.integral_comp_id_comm IsGaussian.integrable_id,
    integral_id_multivariateGaussian, map_zero]

/--
@isnad1 id=eq.0h1v.s8.4ec447f02371 from=translated src=- shape=f07a9ec4 vocab=9685b297
-/
lemma integral_id_gaussianProjectiveFamily' (I : Finset ℝ≥0) :
    ∫ x, id x ∂(gaussianProjectiveFamily I) = 0 := integral_id_gaussianProjectiveFamily I

open scoped RealInnerProductSpace in
/--
@isnad1 id=eq.0h3v.s7.48261701cd2b from=translated src=- shape=2dd278fd vocab=c1c5be05
-/
lemma covariance_eval_gaussianProjectiveFamily (I : Finset ℝ≥0) (s t : I) :
    cov[fun x ↦ x s, fun x ↦ x t; gaussianProjectiveFamily I] = min s.1 t.1 := by
  rw [gaussianProjectiveFamily, covariance_map_equiv]
  change cov[fun x : EuclideanSpace ℝ I ↦ x s, fun x ↦ x t; _] = _
  have (u : I) : (fun x : EuclideanSpace ℝ I ↦ x u) =
      fun x ↦ ⟪EuclideanSpace.basisFun I ℝ u, x⟫ := by ext; simp [PiLp.inner_apply]
  rw [this, this, ← covarianceBilin_apply_eq_cov,
    covarianceBilin_multivariateGaussian (posSemidef_brownianCovMatrix I)]
  · simp [brownianCovMatrix_apply]
  · exact IsGaussian.memLp_two_id

/--
@isnad1 id=eq.0h2v.s7.c45776b941c5 from=translated src=- shape=8ef95dc7 vocab=c1cf6915
-/
lemma variance_eval_gaussianProjectiveFamily {I : Finset ℝ≥0} (s : I) :
    Var[fun x ↦ x s; gaussianProjectiveFamily I] = s := by
  rw [← covariance_self, covariance_eval_gaussianProjectiveFamily, min_self]
  exact Measurable.aemeasurable <| by fun_prop

/--
@isnad1 id=haslaw.0h2v.s7.a6aba29f518f from=translated src=- shape=9d9cf2b6 vocab=ef1d0a67
-/
lemma hasLaw_eval_gaussianProjectiveFamily {I : Finset ℝ≥0} (s : I) :
    HasLaw (fun x ↦ x s) (gaussianReal 0 s) (gaussianProjectiveFamily I) where
  aemeasurable := Measurable.aemeasurable <| by fun_prop
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_eval_gaussianProjectiveFamily,
      Real.toNNReal_coe]
    swap
    · exact IsGaussian.hasGaussianLaw_id.eval s
    conv => enter [1, 1, 2]; change fun x ↦ ContinuousLinearMap.proj (R := ℝ) s x
    rw [ContinuousLinearMap.integral_comp_id_comm, integral_id_gaussianProjectiveFamily, map_zero]
    exact IsGaussian.integrable_id

open ContinuousLinearMap in
/--
@isnad1 id=haslaw.0h3v.s7.eee4f36c7511 from=translated src=- shape=49c1fc5e vocab=c65f9a71
-/
lemma hasLaw_eval_sub_eval_gaussianProjectiveFamily (I : Finset ℝ≥0) (s t : I) :
    HasLaw ((fun x ↦ x s - x t)) (gaussianReal 0 (max (s - t) (t - s)))
      (gaussianProjectiveFamily I) where
  map_eq := by
    rw [HasGaussianLaw.map_eq_gaussianReal, variance_fun_sub,
      variance_eval_gaussianProjectiveFamily, variance_eval_gaussianProjectiveFamily,
      covariance_eval_gaussianProjectiveFamily]
    · conv =>
        enter [1, 1, 2];
        change fun x ↦ (proj (R := ℝ) (φ := fun i : I ↦ ℝ) s -
          proj (R := ℝ) (φ := fun i : I ↦ ℝ) t) x
      rw [integral_comp_id_comm, integral_id_gaussianProjectiveFamily, map_zero]
      · norm_cast
        rw [sub_add_eq_add_sub, ← NNReal.coe_add, ← NNReal.coe_sub, Real.toNNReal_coe,
          NNReal.add_sub_two_mul_min_eq_max]
        nth_grw 1 [two_mul, min_le_left, min_le_right]
      · exact IsGaussian.integrable_id
    · exact (IsGaussian.hasGaussianLaw_id.eval s).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.eval t).memLp_two
    · exact (IsGaussian.hasGaussianLaw_id.prodMk s t).sub

/--
@isnad1 id=isprojec.0h0v.s3.07229c23170b from=translated src=- shape=d26e3920 vocab=a6763940
-/
lemma isProjectiveMeasureFamily_gaussianProjectiveFamily :
    IsProjectiveMeasureFamily (α := fun _ ↦ ℝ) gaussianProjectiveFamily := by
  intro I J hJI
  nth_rw 2 [gaussianProjectiveFamily]
  rw [Measure.map_map]
  · have : (Finset.restrict₂ (π := fun _ ↦ ℝ) hJI ∘ (MeasurableEquiv.toLp 2 (I → ℝ)).symm) =
        (MeasurableEquiv.toLp 2 (J → ℝ)).symm ∘ (EuclideanSpace.restrict₂ hJI) := by
      ext; simp
    rw [this, ((measurePreserving_equiv_multivariateGaussian J).comp
      (measurePreserving_restrict₂_multivariateGaussian
        (posSemidef_brownianCovMatrix I) hJI)).map_eq]
  · exact Finset.measurable_restrict₂ _ -- fun_prop fails
  · fun_prop

/--
@isnad1 id=measurep.1h2v.s7.aa7b3b247b9d from=translated src=- shape=d89baea4 vocab=ee104c22
-/
lemma measurePreserving_restrict_gaussianProjectiveFamily {I J : Finset ℝ≥0} (hIJ : I ⊆ J) :
    MeasurePreserving (Finset.restrict₂ (π := fun _ ↦ ℝ) hIJ) (gaussianProjectiveFamily J)
      (gaussianProjectiveFamily I) where
  measurable := Finset.measurable_restrict₂ _
  map_eq := isProjectiveMeasureFamily_gaussianProjectiveFamily J I hIJ |>.symm

end ProbabilityTheory
