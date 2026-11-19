import Tengoku.OddcyclegoodmanLean.OddCycleBound.Spectral.GraphonL2Operator
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.KrylovCompression
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.MomentExpansion
import Tengoku.Seed.Analysis.InnerProductSpace.Rayleigh

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace OddCycleBound.DenseRegion

open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega → Omega → ℝ}

/--
@isnad1 id=eq.1h3v.s7.2046557db43e from=translated src=- shape=f3820536 vocab=aa8a2940
-/
lemma inner_oneL2_goodL2_eq_mean {f : Omega → ℝ} (hf : Good f) :
    inner ℝ (oneL2 (Omega := Omega) mu) (goodL2 (mu := mu) hf) = mean mu f := by
  rw [← goodL2_one_eq_oneL2 (Omega := Omega) (mu := mu),
    inner_goodL2_eq_integral_mul]
  simp [mean]

/--
@isnad1 id=good.0h2v.s3.b88c2110a2b8 from=translated src=- shape=ab6ac2c4 vocab=48def5ae
-/
lemma good_const (c : ℝ) : Good (fun _ : Omega => c) := by
  exact ⟨stronglyMeasurable_const, ⟨|c|, abs_nonneg c, fun _ => le_rfl⟩⟩

/--
@isnad1 id=eq.0h3v.s11.0788baef3cbe from=translated src=- shape=87bf0b36 vocab=8bf902ce
-/
lemma goodL2_const (c : ℝ) :
    goodL2 (mu := mu) (good_const (Omega := Omega) c) =
      c • oneL2 (Omega := Omega) mu := by
  rw [Lp.ext_iff]
  filter_upwards [goodL2_ae_eq (mu := mu) (good_const (Omega := Omega) c),
    Lp.coeFn_smul c (oneL2 (Omega := Omega) mu),
    oneL2_ae_eq_one (Omega := Omega) (mu := mu)] with x hconst hsmul hone
  rw [hconst, hsmul]
  simp [Pi.smul_apply, hone]

noncomputable def centerProjection :
  Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu :=
  1 - InnerProductSpace.rankOne ℝ
    (oneL2 (Omega := Omega) mu) (oneL2 (Omega := Omega) mu)

/--
@isnad1 id=eq.1h3v.s12.25f4ebe5811f from=translated src=- shape=f54018ab vocab=156e5728
-/
lemma centerProjection_apply_goodL2 {f : Omega → ℝ} (hf : Good f) :
    centerProjection (Omega := Omega) (mu := mu) (goodL2 (mu := mu) hf) =
      goodL2 (mu := mu)
        (good_sub hf (good_const (Omega := Omega) (mean mu f))) := by
  unfold centerProjection
  simp only [sub_apply, one_apply_eq_self, InnerProductSpace.rankOne_apply]
  rw [inner_oneL2_goodL2_eq_mean hf,
    goodL2_sub hf (good_const (Omega := Omega) (mean mu f)), goodL2_const]

/--
@isnad1 id=eq.2h3v.s12.79d69ec78d40 from=translated src=- shape=6a8587c1 vocab=65fccc9e
-/
lemma centerProjection_apply_of_mean_zero {f : Omega → ℝ} (hf : Good f)
    (hmean : mean mu f = 0) :
    centerProjection (Omega := Omega) (mu := mu) (goodL2 (mu := mu) hf) =
      goodL2 (mu := mu) hf := by
  unfold centerProjection
  simp only [sub_apply, one_apply_eq_self, InnerProductSpace.rankOne_apply,
    inner_oneL2_goodL2_eq_mean hf, hmean, zero_smul,
    sub_zero]

/--
@isnad1 id=eq.2h4v.s12.4a3e06b3f946 from=translated src=- shape=182bee7d vocab=4d4528b1
-/
lemma kernelOpCLM_goodL2_eq_goodL2 (hW : IsGraphon W mu)
    {f : Omega → ℝ} (hf : Good f) :
    kernelOpCLM (mu := mu) hW (goodL2 (mu := mu) hf) =
      goodL2 (mu := mu) (good_kernelOp hW hf) := by
  rw [kernelOpCLM_goodL2 (mu := mu) hW hf]
  exact MemLp.toLp_congr
    (kernelOp_memLp_two hW hf)
    (good_memLp_two (good_kernelOp hW hf))
    (ae_of_all _ fun _ => rfl)

noncomputable def centeredGraphonOp (hW : IsGraphon W mu) :
    Lp ℝ 2 mu →L[ℝ] Lp ℝ 2 mu :=
  (centerProjection (Omega := Omega) (mu := mu)).comp
    ((kernelOpCLM (mu := mu) hW).comp
      (centerProjection (Omega := Omega) (mu := mu)))

/--
@isnad1 id=issymmet.0h2v.s11.2fb27f95bd8e from=translated src=- shape=d31dfa74 vocab=fe693572
-/
lemma centerProjection_isSymmetric :
    (centerProjection (Omega := Omega) (mu := mu)).toLinearMap.IsSymmetric := by
  exact LinearMap.IsSymmetric.sub LinearMap.IsSymmetric.one
    (InnerProductSpace.isSymmetric_rankOne_self (oneL2 (Omega := Omega) mu))

/--
@isnad1 id=issymmet.0h2v.s11.eeba72c3eec7 from=translated src=- shape=d31dfa74 vocab=1602a855
-/
lemma centerProjection_isSymmetricProjection :
    (centerProjection (Omega := Omega) (mu := mu)).toLinearMap.IsSymmetricProjection := by
  have hone : ‖oneL2 (Omega := Omega) mu‖ = 1 := by
    have hs := norm_oneL2_sq (Omega := Omega) (mu := mu)
    nlinarith [norm_nonneg (oneL2 (Omega := Omega) mu)]
  have hQ := InnerProductSpace.isSymmetricProjection_rankOne_self
    (𝕜 := ℝ) (E := Lp ℝ 2 mu) hone
  have hI : (1 : Module.End ℝ (Lp ℝ 2 mu)).IsSymmetricProjection := by
    exact ⟨IsIdempotentElem.one, LinearMap.IsSymmetric.one⟩
  have hQI : LinearMap.range (InnerProductSpace.rankOne ℝ
      (oneL2 (Omega := Omega) mu) (oneL2 (Omega := Omega) mu)).toLinearMap ≤
      LinearMap.range (1 : Module.End ℝ (Lp ℝ 2 mu)) := by
    intro x _hx
    exact ⟨x, rfl⟩
  simpa only [centerProjection, ContinuousLinearMap.toLinearMap_sub,
    ContinuousLinearMap.toLinearMap_one] using hQ.sub_of_range_le_range hI hQI

/--
@isnad1 id=le.0h3v.s12.b24c8389ff9f from=translated src=- shape=031217c3 vocab=72b5fb8e
-/
lemma norm_centerProjection_apply_le (f : Lp ℝ 2 mu) :
    ‖centerProjection (Omega := Omega) (mu := mu) f‖ ≤ ‖f‖ := by
  let P := (centerProjection (Omega := Omega) (mu := mu)).toLinearMap
  have hP : P.IsSymmetricProjection :=
    centerProjection_isSymmetricProjection (Omega := Omega) (mu := mu)
  have hsq : ‖P f‖ ^ 2 = inner ℝ (P f) f := by
    calc
      ‖P f‖ ^ 2 = inner ℝ (P f) (P f) := by rw [real_inner_self_eq_norm_sq]
      _ = inner ℝ (P (P f)) f := (hP.isSymmetric (P f) f).symm
      _ = inner ℝ (P f) f := by
        rw [← Module.End.mul_apply, hP.isIdempotentElem]
  have hcs : ‖P f‖ ^ 2 ≤ ‖P f‖ * ‖f‖ := by
    rw [hsq]
    exact real_inner_le_norm _ _
  change ‖P f‖ ≤ ‖f‖
  nlinarith [norm_nonneg (P f), norm_nonneg f]

/--
@isnad1 id=issymmet.1h3v.s11.3a5743c4f38f from=translated src=- shape=841eb4ed vocab=5eaf5244
-/
lemma centeredGraphonOp_isSymmetric (hW : IsGraphon W mu) :
    (centeredGraphonOp hW).toLinearMap.IsSymmetric := by
  intro f g
  have hP := centerProjection_isSymmetric (Omega := Omega) (mu := mu)
  have hT := kernelOpCLM_isSymmetric (mu := mu) hW
  change inner ℝ
      (centerProjection (Omega := Omega) (mu := mu)
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu) f))) g =
    inner ℝ f
      (centerProjection (Omega := Omega) (mu := mu)
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu) g)))
  calc
    _ = inner ℝ
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu) f))
        (centerProjection (Omega := Omega) (mu := mu) g) := hP.apply_clm _ _
    _ = inner ℝ
        (centerProjection (Omega := Omega) (mu := mu) f)
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu) g)) := hT.apply_clm _ _
    _ = _ := hP.apply_clm _ _

/--
@isnad1 id=eq.3h4v.s12.ff72445d475f from=translated src=- shape=d3dfabc1 vocab=5beab70f
-/
lemma centeredGraphonOp_apply_mean_zero_goodL2 (hW : IsGraphon W mu)
    {f : Omega → ℝ} (hf : Good f) (hmean : mean mu f = 0) :
    centeredGraphonOp hW (goodL2 (mu := mu) hf) =
      goodL2 (mu := mu) (good_compress hW hf) := by
  unfold centeredGraphonOp
  change centerProjection (Omega := Omega) (mu := mu)
      (kernelOpCLM (mu := mu) hW
        (centerProjection (Omega := Omega) (mu := mu) (goodL2 (mu := mu) hf))) = _
  rw [centerProjection_apply_of_mean_zero hf hmean]
  rw [kernelOpCLM_goodL2_eq_goodL2 hW hf]
  rw [centerProjection_apply_goodL2 (good_kernelOp hW hf)]
  exact MemLp.toLp_congr
    (good_memLp_two
      (good_sub (good_kernelOp hW hf)
        (good_const (Omega := Omega) (mean mu (kernelOp W mu f)))))
    (good_memLp_two (good_compress hW hf))
    (ae_of_all _ fun _ => by rfl)

noncomputable def centeredDegreeL2 (hW : IsGraphon W mu) : Lp ℝ 2 mu :=
  goodL2 (mu := mu) (good_degCentered hW)

/--
@isnad1 id=eq.1h4v.s11.a71aee5ed9e9 from=translated src=- shape=1fe528b0 vocab=31e03e6a
-/
theorem linearIter_centeredGraphonOp (hW : IsGraphon W mu) : ∀ j : ℕ,
    linearIter (centeredGraphonOp hW).toLinearMap j (centeredDegreeL2 hW) =
      goodL2 (mu := mu) (good_compressIter hW j)
  | 0 => rfl
  | j + 1 => by
      rw [linearIter_succ, linearIter_centeredGraphonOp hW j]
      exact centeredGraphonOp_apply_mean_zero_goodL2 hW
        (good_compressIter hW j) (mean_compressIter hW j)

/--
@isnad1 id=eq.1h4v.s11.b746252ec03d from=translated src=- shape=83b393db vocab=f575129a
-/
theorem inner_linearIter_centeredGraphonOp_eq_specMoment (hW : IsGraphon W mu) (j : ℕ) :
    inner ℝ (centeredDegreeL2 hW)
        (linearIter (centeredGraphonOp hW).toLinearMap j (centeredDegreeL2 hW)) =
      specMoment W mu j := by
  rw [linearIter_centeredGraphonOp hW j]
  exact inner_goodL2_eq_integral_mul (good_degCentered hW) (good_compressIter hW j)

noncomputable def graphonAtomEigenvalue (hW : IsGraphon W mu) (d : ℕ) :
    Fin (Module.finrank ℝ
      (krylovSubspace (centeredGraphonOp hW) (centeredDegreeL2 hW) d)) → ℝ :=
  finiteAtomEigenvalue
    (krylovCompression (centeredGraphonOp hW) (centeredDegreeL2 hW) d).toLinearMap
    (krylovCompression_isSymmetric _ _ _ (centeredGraphonOp_isSymmetric hW))

noncomputable def graphonAtomWeight (hW : IsGraphon W mu) (d : ℕ) :
    Fin (Module.finrank ℝ
      (krylovSubspace (centeredGraphonOp hW) (centeredDegreeL2 hW) d)) → ℝ :=
  finiteAtomWeight
    (krylovCompression (centeredGraphonOp hW) (centeredDegreeL2 hW) d).toLinearMap
    (krylovCompression_isSymmetric _ _ _ (centeredGraphonOp_isSymmetric hW))
    (krylovVector (centeredGraphonOp hW) (centeredDegreeL2 hW) d)

/--
@isnad1 id=le.1h5v.s13.f46c5137f57f from=translated src=- shape=08e1a9ec vocab=6c590224
-/
lemma graphonAtomWeight_nonneg (hW : IsGraphon W mu) (d : ℕ) (i) :
    0 ≤ graphonAtomWeight hW d i := by
  exact finiteAtomWeight_nonneg _ _ _ i

/--
@isnad1 id=eq.2h5v.s14.0c25c72d2a5f from=translated src=- shape=be9006da vocab=e1379cc1
-/
theorem specMoment_eq_graphonAtomicMoment (hW : IsGraphon W mu)
    {d j : ℕ} (hj : j ≤ d) :
    specMoment W mu j =
      atomicMoment (graphonAtomWeight hW d) (graphonAtomEigenvalue hW d) j := by
  rw [← inner_linearIter_centeredGraphonOp_eq_specMoment hW j]
  simpa only [graphonAtomWeight, graphonAtomEigenvalue] using
    inner_linearIter_eq_krylovAtomicMoment
      (centeredGraphonOp hW) (centeredDegreeL2 hW)
      (centeredGraphonOp_isSymmetric hW) hj

/--
@isnad1 id=mem.2h5v.s13.1cbea413cd44 from=translated src=- shape=9fdf9373 vocab=5130a2bb
-/
theorem graphonAtomEigenvalue_mem_halfInterval_of_norm (hW : IsGraphon W mu) (d : ℕ)
    (hnorm : ‖centeredGraphonOp hW‖ ≤ (1 : ℝ) / 2) (i) :
    graphonAtomEigenvalue hW d i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  exact krylovAtomEigenvalue_mem_halfInterval
    (centeredGraphonOp hW) (centeredDegreeL2 hW) d
    (centeredGraphonOp_isSymmetric hW) hnorm i

/--
@isnad1 id=le.3h4v.s7.a4f2dfcbbc54 from=translated src=- shape=d6f8921d vocab=daba37bb
-/
lemma abs_integral_mul_kernelOp_le_half (hW : IsGraphon W mu)
    {f : Omega → ℝ} (hf : Good f) (hmean : mean mu f = 0) :
    |∫ x, f x * kernelOp W mu f x ∂mu| ≤
      (1 : ℝ) / 2 * ∫ x, f x * f x ∂mu := by
  let U := compl W
  have hU : IsGraphon U mu := isGraphon_compl hW
  have hdomW :
      |∫ x, f x * kernelOp W mu f x ∂mu| ≤
        ∫ x, |f x| * kernelOp W mu (fun y => |f y|) x ∂mu := by
    simpa only [inner_goodL2_kernelOpL2OfGood_eq_integral] using
      (abs_inner_goodL2_kernelOpL2OfGood_self_le_abs (mu := mu) hW hf)
  have hdomU :
      |∫ x, f x * kernelOp U mu f x ∂mu| ≤
        ∫ x, |f x| * kernelOp U mu (fun y => |f y|) x ∂mu := by
    simpa only [inner_goodL2_kernelOpL2OfGood_eq_integral] using
      (abs_inner_goodL2_kernelOpL2OfGood_self_le_abs (mu := mu) hU hf)
  have hcomp :
      (∫ x, f x * kernelOp U mu f x ∂mu) =
        -(∫ x, f x * kernelOp W mu f x ∂mu) := by
    calc
      (∫ x, f x * kernelOp U mu f x ∂mu) =
          ∫ x, -(f x * kernelOp W mu f x) ∂mu := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            change f x * kernelOp (compl W) mu f x = _
            rw [kernelOp_compl hW hf x, hmean]
            ring
      _ = -(∫ x, f x * kernelOp W mu f x ∂mu) := by rw [integral_neg]
  have hdomU' :
      |∫ x, f x * kernelOp W mu f x ∂mu| ≤
        ∫ x, |f x| * kernelOp U mu (fun y => |f y|) x ∂mu := by
    simpa only [hcomp, abs_neg] using hdomU
  have hsum :
      (∫ x, |f x| * kernelOp W mu (fun y => |f y|) x ∂mu) +
          (∫ x, |f x| * kernelOp U mu (fun y => |f y|) x ∂mu) =
        (∫ x, |f x| ∂mu) ^ 2 := by
    have hWa := (good_abs hf).mul (good_kernelOp hW (good_abs hf))
    have hUa := (good_abs hf).mul (good_kernelOp hU (good_abs hf))
    rw [← integral_add hWa.integrable hUa.integrable]
    calc
      (∫ x,
          (|f x| * kernelOp W mu (fun y => |f y|) x +
            |f x| * kernelOp U mu (fun y => |f y|) x) ∂mu) =
          ∫ x, (∫ y, |f y| ∂mu) * |f x| ∂mu := by
            refine integral_congr_ae (ae_of_all _ fun x => ?_)
            change _ + |f x| * kernelOp (compl W) mu (fun y => |f y|) x = _
            rw [kernelOp_compl hW (good_abs hf) x]
            simp only [mean]
            ring
      _ = (∫ x, |f x| ∂mu) ^ 2 := by
            rw [integral_const_mul]
            ring
  have hL1 := integral_abs_sq_le_integral_mul_self (mu := mu) hf
  linarith

/--
@isnad1 id=le.2h4v.s12.5bace421cb95 from=translated src=- shape=9b3917c6 vocab=6556b12f
-/
lemma abs_inner_centeredGraphonOp_goodL2_le_half (hW : IsGraphon W mu)
    {f : Omega → ℝ} (hf : Good f) :
    |inner ℝ (goodL2 (mu := mu) hf)
        (centeredGraphonOp hW (goodL2 (mu := mu) hf))| ≤
      (1 : ℝ) / 2 * ‖goodL2 (mu := mu) hf‖ ^ 2 := by
  let fc : Omega → ℝ := fun x => f x - mean mu f
  have hfc : Good fc := good_sub hf (good_const (Omega := Omega) (mean mu f))
  have hfc_mean : mean mu fc = 0 := by
    unfold fc mean
    rw [integral_sub hf.integrable (integrable_const _)]
    simp
  have hP : centerProjection (Omega := Omega) (mu := mu)
      (goodL2 (mu := mu) hf) = goodL2 (mu := mu) hfc := by
    simpa only [fc] using centerProjection_apply_goodL2 (mu := mu) hf
  have hpoint := abs_integral_mul_kernelOp_le_half (mu := mu) hW hfc hfc_mean
  have hcontract := norm_centerProjection_apply_le (Omega := Omega) (mu := mu)
    (goodL2 (mu := mu) hf)
  have hsquare : ‖goodL2 (mu := mu) hfc‖ ^ 2 ≤
      ‖goodL2 (mu := mu) hf‖ ^ 2 := by
    rw [hP] at hcontract
    nlinarith [norm_nonneg (goodL2 (mu := mu) hfc),
      norm_nonneg (goodL2 (mu := mu) hf)]
  have hquad :
      |inner ℝ (goodL2 (mu := mu) hfc)
          (kernelOpCLM (mu := mu) hW (goodL2 (mu := mu) hfc))| ≤
        (1 : ℝ) / 2 * ‖goodL2 (mu := mu) hfc‖ ^ 2 := by
    rw [kernelOpCLM_goodL2_eq_goodL2 hW hfc,
      inner_goodL2_eq_integral_mul,
      norm_goodL2_sq_eq_integral_mul]
    exact hpoint
  change |inner ℝ (goodL2 (mu := mu) hf)
      (centerProjection (Omega := Omega) (mu := mu)
        (kernelOpCLM (mu := mu) hW
          (centerProjection (Omega := Omega) (mu := mu)
            (goodL2 (mu := mu) hf))))| ≤ _
  rw [← (centerProjection_isSymmetric (Omega := Omega) (mu := mu)).apply_clm,
    hP]
  linarith

/--
@isnad1 id=le.1h4v.s12.2a7b242e89e6 from=translated src=- shape=a8ce75a6 vocab=251cfe39
-/
lemma abs_inner_centeredGraphonOp_self_le_half (hW : IsGraphon W mu)
    (f : Lp ℝ 2 mu) :
    |inner ℝ f (centeredGraphonOp hW f)| ≤ (1 : ℝ) / 2 * ‖f‖ ^ 2 := by
  let p : Lp ℝ 2 mu → Prop := fun f =>
    |inner ℝ f (centeredGraphonOp hW f)| ≤ (1 : ℝ) / 2 * ‖f‖ ^ 2
  change p f
  exact DenseRange.induction_on
    (denseRange_goodL2 (Omega := Omega) (mu := mu)) f
    (by
      dsimp [p]
      exact isClosed_le (by fun_prop) (by fun_prop))
    (by
      intro a
      rcases a with ⟨g, hg⟩
      dsimp [p]
      exact abs_inner_centeredGraphonOp_goodL2_le_half (mu := mu) hW hg)

/--
@isnad1 id=le.1h3v.s11.32a462a2f039 from=translated src=- shape=693488a7 vocab=edb6ddc5
-/
theorem norm_centeredGraphonOp_le_half (hW : IsGraphon W mu) :
    ‖centeredGraphonOp hW‖ ≤ (1 : ℝ) / 2 := by
  rw [(centeredGraphonOp hW).norm_eq_iSup_rayleighQuotient
    (centeredGraphonOp_isSymmetric hW)]
  refine ciSup_le fun f => ?_
  by_cases hf : f = 0
  · simp [hf]
  have hnorm : 0 < ‖f‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  have hquad := abs_inner_centeredGraphonOp_self_le_half (mu := mu) hW f
  rw [ContinuousLinearMap.rayleighQuotient,
    ContinuousLinearMap.reApplyInnerSelf_apply]
  simp only [RCLike.re_to_real, abs_div, abs_sq]
  rw [div_le_iff₀ hnorm]
  simpa only [real_inner_comm, mul_assoc] using hquad

/--
@isnad1 id=mem.1h5v.s13.c5379d033a4b from=translated src=- shape=bcc2ebe3 vocab=781f30a8
-/
theorem graphonAtomEigenvalue_mem_halfInterval (hW : IsGraphon W mu) (d : ℕ) (i) :
    graphonAtomEigenvalue hW d i ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2) := by
  exact graphonAtomEigenvalue_mem_halfInterval_of_norm hW d
    (norm_centeredGraphonOp_le_half hW) i

/--
@isnad1 id=eq.1h5v.s14.5ffc3edb4773 from=translated src=- shape=0e37a508 vocab=199523eb
-/
theorem momentPhi_specMoment_eq_graphonAtomicMoment (hW : IsGraphon W mu)
    (m : ℕ) (q : ℝ) :
    momentPhi m q (specMoment W mu) =
      momentPhi m q
        (atomicMoment (graphonAtomWeight hW m) (graphonAtomEigenvalue hW m)) := by
  apply momentPhi_congr_of_le q
  intro j hj
  exact specMoment_eq_graphonAtomicMoment hW hj

/-- Lemma 3.3: `Φ_m ≥ 0` as soon as every excursion polynomial `P_{m,r}` is nonnegative on
`[-1/2, 1/2]^r`.
@isnad1 id=le.4h5v.s7.97172c24e631 from=translated src=- shape=5050cf7b vocab=6781c6f0
-/
theorem momentPhi_specMoment_nonneg' {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hW : IsGraphon W mu) (q : ℝ)
    (hP : ∀ r, 1 ≤ r ∧ 2 * r < m → ∀ L : List ℝ, L.length = r →
      (∀ x ∈ L, x ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2)) → 0 ≤ multiKernel m r q L) :
    0 ≤ momentPhi m q (specMoment W mu) := by
  rw [momentPhi_specMoment_eq_graphonAtomicMoment hW m q]
  exact momentPhi_nonneg_of_atomic' hm hm3 q
    (graphonAtomWeight hW m) (graphonAtomEigenvalue hW m)
    (graphonAtomWeight_nonneg hW m)
    (graphonAtomEigenvalue_mem_halfInterval hW m)
    (fun r hr hrm => hP r ⟨hr, hrm⟩)

/--
@isnad1 id=le.4h5v.s7.568e76148a3c from=translated src=- shape=c24a9f07 vocab=621a7e49
-/
theorem momentPhi_specMoment_nonneg {m : ℕ} (hm : Odd m) (hm3 : 3 ≤ m)
    (hW : IsGraphon W mu) (q : ℝ)
    (hdiag : ∀ r, 1 ≤ r ∧ 2 * r < m →
      ∀ ell ∈ Set.Icc (-(1 : ℝ) / 2) (1 / 2), 0 ≤ diagKernel m r q ell) :
    0 ≤ momentPhi m q (specMoment W mu) := by
  rw [momentPhi_specMoment_eq_graphonAtomicMoment hW m q]
  exact momentPhi_nonneg_of_atomic hm hm3 q
    (graphonAtomWeight hW m) (graphonAtomEigenvalue hW m)
    (graphonAtomWeight_nonneg hW m)
    (graphonAtomEigenvalue_mem_halfInterval hW m)
    (fun r hr hrm => hdiag r ⟨hr, hrm⟩)

end OddCycleBound.DenseRegion
