import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.CenteredOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory

noncomputable section

namespace OddCycleBound.IntermediateRegion

open OddCycleBound.DenseRegion
open OddCycleBound.Spectral.L2Kernel

universe u

variable {Omega : Type u} [MeasurableSpace Omega]
variable {mu : Measure Omega} [IsProbabilityMeasure mu]
variable {W : Omega -> Omega -> Real}

def centeredInput (mu : Measure Omega) (f : Omega -> Real) : Omega -> Real :=
  fun x => f x - mean mu f

omit [IsProbabilityMeasure mu] in
/--
@isnad1 id=good.1h3v.s4.07c186907b2a from=translated src=- shape=e78d908f vocab=a982a408
-/
lemma good_centeredInput {f : Omega -> Real} (hf : Good f) :
    Good (centeredInput mu f) := by
  exact good_sub hf (DenseRegion.good_const (Omega := Omega) (mean mu f))

/--
@isnad1 id=eq.1h3v.s5.aa3067232aaf from=translated src=- shape=666a1921 vocab=c1889b71
-/
lemma mean_centeredInput {f : Omega -> Real} (hf : Good f) :
    mean mu (centeredInput mu f) = 0 := by
  unfold centeredInput mean
  rw [integral_sub hf.integrable (integrable_const _)]
  simp

noncomputable def centeredKernelOp (hW : IsGraphon W mu) :
    Lp Real 2 mu →L[Real] Lp Real 2 mu :=
  kernelOpGoodKCLM (mu := mu) (centeredKernel_goodK hW)
    (by norm_num : (0 : Real) <= 4) (abs_centeredKernel_le_four hW)

/--
@isnad1 id=eq.2h5v.s5.1c94d7fdded3 from=translated src=- shape=46651e91 vocab=64a46bd1
-/
lemma kernelOp_centeredKernel_eq_compress_centeredInput
    (hW : IsGraphon W mu) {f : Omega -> Real} (hf : Good f) (x : Omega) :
    kernelOp (centeredKernel W mu) mu f x =
      compress W mu (centeredInput mu f) x := by
  let c : Real := mean mu f
  let fc : Omega -> Real := centeredInput mu f
  have hfc : Good fc := good_centeredInput (mu := mu) hf
  have hWf : Integrable (fun y => W x y * f y) mu := integrable_Uf hW hf x
  have hxf : Integrable (fun y => degree W mu x * f y) mu :=
    hf.integrable.const_mul _
  have hyf : Integrable (fun y => degree W mu y * f y) mu :=
    ((good_degree hW).mul hf).integrable
  have hqf : Integrable (fun y => edgeDensity W mu * f y) mu :=
    hf.integrable.const_mul _
  have hleft :
      kernelOp (centeredKernel W mu) mu f x =
        kernelOp W mu f x - degree W mu x * mean mu f -
          (∫ y, degree W mu y * f y ∂mu) +
            edgeDensity W mu * mean mu f := by
    unfold kernelOp centeredKernel
    calc
      (∫ y,
          (W x y - degree W mu x - degree W mu y + edgeDensity W mu) * f y ∂mu) =
          ∫ y,
            (W x y * f y - degree W mu x * f y - degree W mu y * f y +
              edgeDensity W mu * f y) ∂mu := by
            refine integral_congr_ae (ae_of_all _ fun y => by ring)
      _ = _ := by
        let a : Omega -> Real := fun y => W x y * f y
        let b : Omega -> Real := fun y => degree W mu x * f y
        let d : Omega -> Real := fun y => degree W mu y * f y
        let e : Omega -> Real := fun y => edgeDensity W mu * f y
        change integral mu (((a - b) - d) + e) = _
        have ha : Integrable a mu := by simpa only [a] using hWf
        have hb : Integrable b mu := by simpa only [b] using hxf
        have hd : Integrable d mu := by simpa only [d] using hyf
        have he : Integrable e mu := by simpa only [e] using hqf
        have hab : integral mu (a - b) = integral mu a - integral mu b := by
          calc
            integral mu (a - b) = ∫ y, a y - b y ∂mu := by
              refine integral_congr_ae (ae_of_all _ fun y => ?_)
              rfl
            _ = integral mu a - integral mu b := integral_sub ha hb
        have habd : integral mu ((a - b) - d) =
            integral mu (a - b) - integral mu d := by
          calc
            integral mu ((a - b) - d) = ∫ y, (a - b) y - d y ∂mu := by
              refine integral_congr_ae (ae_of_all _ fun y => ?_)
              rfl
            _ = integral mu (a - b) - integral mu d :=
              integral_sub (ha.sub hb) hd
        have habde : integral mu (((a - b) - d) + e) =
            integral mu ((a - b) - d) + integral mu e := by
          calc
            integral mu (((a - b) - d) + e) =
                ∫ y, ((a - b) - d) y + e y ∂mu := by
              refine integral_congr_ae (ae_of_all _ fun y => ?_)
              rfl
            _ = integral mu ((a - b) - d) + integral mu e :=
              integral_add ((ha.sub hb).sub hd) he
        rw [habde, habd, hab]
        dsimp [a, b, d, e]
        rw [integral_const_mul, integral_const_mul]
        rfl
  have hfc_point :
      forall z, fc z = (f + (-c) • (fun _ : Omega => (1 : Real))) z := by
    intro z
    simp only [fc, centeredInput, c, Pi.add_apply, Pi.smul_apply]
    ring
  have hkfc :
      kernelOp W mu fc x = kernelOp W mu f x - degree W mu x * c := by
    have hfun : fc = f + (-c) • (fun _ : Omega => (1 : Real)) :=
      funext hfc_point
    rw [hfun, kernelOp_add' hW hf (good_smul (-c) good_one) x,
      kernelOp_smul', kernelOp_one hW]
    ring
  have hmeanfc :
      mean mu (kernelOp W mu fc) =
        (∫ y, degree W mu y * f y ∂mu) - edgeDensity W mu * c := by
    rw [mean_kernelOp_eq hW hfc]
    have hpath : pathIter W mu 1 = degree W mu := pathIter_one hW
    rw [hpath]
    unfold pairing fc centeredInput c
    have hfun :
        (fun x => degree W mu x * (f x - mean mu f)) =
          (fun x => degree W mu x * f x - mean mu f * degree W mu x) := by
      funext z
      ring
    rw [hfun]
    rw [integral_sub ((good_degree hW).mul hf).integrable
      ((good_degree hW).integrable.const_mul _), integral_const_mul]
    have hdegint : (∫ a, degree W mu a ∂mu) = edgeDensity W mu := by
      simpa only [one_mul] using
        (integral_one_mul_degree_eq_edgeDensity
          (Omega := Omega) (mu := mu) (W := W))
    rw [hdegint]
    ring
  rw [compress, hkfc, hmeanfc, hleft]
  dsimp [c]
  ring

/--
@isnad1 id=eq.2h4v.s12.e04c2cf954d1 from=translated src=- shape=92949466 vocab=19c93030
-/
lemma centeredGraphonOp_apply_goodL2
    (hW : IsGraphon W mu) {f : Omega -> Real} (hf : Good f) :
    centeredGraphonOp hW (goodL2 (mu := mu) hf) =
      goodL2 (mu := mu)
        (good_compress hW (good_centeredInput (mu := mu) hf)) := by
  let fc : Omega -> Real := centeredInput mu f
  have hfc : Good fc := good_centeredInput (mu := mu) hf
  have hmean : mean mu fc = 0 := mean_centeredInput (mu := mu) hf
  have hP : centerProjection (Omega := Omega) (mu := mu)
      (goodL2 (mu := mu) hf) = goodL2 (mu := mu) hfc := by
    calc
      centerProjection (Omega := Omega) (mu := mu)
          (goodL2 (mu := mu) hf) =
          goodL2 (mu := mu)
            (good_sub hf
              (DenseRegion.good_const (Omega := Omega) (mean mu f))) :=
        centerProjection_apply_goodL2 (mu := mu) hf
      _ = goodL2 (mu := mu) hfc := by
        exact MemLp.toLp_congr
          (good_memLp_two
            (good_sub hf
              (DenseRegion.good_const (Omega := Omega) (mean mu f))))
          (good_memLp_two hfc)
          (ae_of_all _ fun x => by rfl)
  unfold centeredGraphonOp
  change centerProjection (Omega := Omega) (mu := mu)
      (kernelOpCLM (mu := mu) hW
        (centerProjection (Omega := Omega) (mu := mu)
          (goodL2 (mu := mu) hf))) = _
  rw [hP, kernelOpCLM_goodL2_eq_goodL2 hW hfc,
    centerProjection_apply_goodL2 (good_kernelOp hW hfc)]
  exact MemLp.toLp_congr
    (good_memLp_two
      (good_sub (good_kernelOp hW hfc)
        (DenseRegion.good_const (Omega := Omega)
          (mean mu (kernelOp W mu fc)))))
    (good_memLp_two (good_compress hW hfc))
    (ae_of_all _ fun _ => by rfl)

/--
@isnad1 id=eq.2h4v.s13.97a5884d2d13 from=translated src=- shape=2974c860 vocab=84b28a66
-/
lemma centeredKernelOp_apply_goodL2
    (hW : IsGraphon W mu) {f : Omega -> Real} (hf : Good f) :
    centeredKernelOp hW (goodL2 (mu := mu) hf) =
      centeredGraphonOp hW (goodL2 (mu := mu) hf) := by
  unfold centeredKernelOp
  rw [kernelOpGoodKCLM_goodL2 (mu := mu) (centeredKernel_goodK hW)
      (by norm_num : (0 : Real) <= 4) (abs_centeredKernel_le_four hW) hf,
    centeredGraphonOp_apply_goodL2 hW hf]
  exact MemLp.toLp_congr
    (kernelOpGoodK_memLp_two (mu := mu) (centeredKernel_goodK hW) hf)
    (good_memLp_two (good_compress hW (good_centeredInput (mu := mu) hf)))
    (ae_of_all _ fun x => kernelOp_centeredKernel_eq_compress_centeredInput hW hf x)

/--
@isnad1 id=eq.1h3v.s11.1af0ff99d329 from=translated src=- shape=95f00871 vocab=79be8fa5
-/
theorem centeredKernelOp_eq_centeredGraphonOp (hW : IsGraphon W mu) :
    centeredKernelOp hW = centeredGraphonOp hW := by
  apply ContinuousLinearMap.ext (R₁ := Real)
  intro v
  exact DenseRange.induction_on
    (denseRange_goodL2 (Omega := Omega) (mu := mu)) v
    (by exact isClosed_eq (by fun_prop) (by fun_prop))
    (by
      intro a
      rcases a with ⟨f, hf⟩
      exact centeredKernelOp_apply_goodL2 hW hf)

end OddCycleBound.IntermediateRegion
