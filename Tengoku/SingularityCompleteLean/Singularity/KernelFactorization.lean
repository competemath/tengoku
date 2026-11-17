import Tengoku.SingularityCompleteLean.Singularity.DensityVector
import Tengoku.SingularityCompleteLean.Singularity.LiouvilleOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From a scalar kernel identity to an operator factorization

On L¹∩L², density analysis is a Bochner integral. Pairing these integrals
identifies the kernel of H₋* M H₊. Schwartz density then extends the identity
to all of L². The scalar kernel identity is an explicit hypothesis; its
geometric and probabilistic derivation is not formalized here.
-/

noncomputable section
open MeasureTheory
open scoped ComplexConjugate

namespace Singularity

/-- Integration commutes with the conjugate-linear argument of the inner product.
@isnad1 id=eq.1h3v.s8.f770dd2ab27d from=translated src=- shape=0e6f1246 vocab=64aa7fc6
-/
theorem integral_inner_first {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E] {u : ℝ → E}
    (hu : Integrable u) (y : E) :
    (∫ s, inner ℂ (u s) y) = inner ℂ (∫ s, u s) y := by
  have h := congrArg (conj : ℂ → ℂ) (integral_inner (𝕜 := ℂ) hu y)
  rw [← integral_conj] at h
  simpa only [inner_conj_symm] using h

/-- Two Bochner integrals may be paired through a bounded operator.
@isnad1 id=eq.2h5v.s9.20230f4eea6d from=translated src=- shape=143ecb43 vocab=5b68a755
-/
theorem inner_integral_operator_integral {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (M : F →L[ℂ] E) {u : ℝ → E} {v : ℝ → F}
    (hu : Integrable u) (hv : Integrable v) :
    inner ℂ (∫ s, u s) (M (∫ t, v t)) =
      ∫ s, ∫ t, inner ℂ (u s) (M (v t)) := by
  rw [← integral_inner_first hu]
  congr 1
  funext s
  rw [← M.integral_comp_comm hv, integral_inner (M.integrable_comp hv)]

/-- The corresponding double integral is absolutely integrable.
@isnad1 id=integrab.2h5v.s9.3dd5490c1f03 from=translated src=- shape=8e14b103 vocab=064f6966
-/
theorem integrable_inner_operator_prod {E F : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [NormedSpace ℝ F] [IsScalarTower ℝ ℂ F] [CompleteSpace F]
    (M : F →L[ℂ] E) {u : ℝ → E} {v : ℝ → F}
    (hu : Integrable u) (hv : Integrable v) :
    Integrable (fun p : ℝ × ℝ => inner ℂ (u p.1) (M (v p.2))) (volume.prod volume) := by
  apply ((hu.norm.mul_prod hv.norm).const_mul ‖M‖).mono'
    (hu.aestronglyMeasurable.comp_fst.inner
      (M.continuous.comp_aestronglyMeasurable hv.aestronglyMeasurable.comp_snd))
  exact Filter.Eventually.of_forall (fun p => by
    calc
      ‖inner ℂ (u p.1) (M (v p.2))‖ ≤ ‖u p.1‖ * ‖M (v p.2)‖ := norm_inner_le_norm _ _
      _ ≤ ‖u p.1‖ * (‖M‖ * ‖v p.2‖) :=
        mul_le_mul_of_nonneg_left (M.le_opNorm _) (norm_nonneg _)
      _ = ‖M‖ * (‖u p.1‖ * ‖v p.2‖) := by ring)

variable {ι : Type*} [Countable ι]

/-- The scalar kernel obtained from the two actual density columns.-/
def densityPairingKernel (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι) (s t : ℝ) : ℂ :=
  inner ℂ (Kminus.column s) (M (Kplus.column t))

/-- The bounded operator represented by this kernel.-/
def densityFactorization (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι) : RealLineL2 →L[ℂ] RealLineL2 :=
  Kminus.analysis.adjoint.comp (M.comp Kplus.analysis)

/-- Exact weak kernel formula on L¹∩L².
@isnad1 id=eq.2h6v.s13.c2d3a16bae2a from=translated src=- shape=f41532fa vocab=6a3dc9ad
-/
theorem densityFactorization_inner (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι) (f h : RealLineL2)
    (hf : Integrable (f : ℝ → ℂ)) (hh : Integrable (h : ℝ → ℂ)) :
    inner ℂ h (densityFactorization Kminus Kplus M f) =
      ∫ s, ∫ t, densityPairingKernel Kminus Kplus M s t * inner ℂ (h s) (f t) := by
  change inner ℂ h (Kminus.analysis.adjoint (M (Kplus.analysis f))) = _
  rw [Kminus.analysis.adjoint_inner_right, Kminus.analysis_eq_integral h hh,
    Kplus.analysis_eq_integral f hf,
    inner_integral_operator_integral M (Kminus.column_integrable hh) (Kplus.column_integrable hf)]
  congr 1
  funext s
  congr 1
  funext t
  simp only [map_smul, inner_smul_left, inner_smul_right, densityPairingKernel,
    RCLike.inner_apply]
  ring

/-- Absolute integrability of the physical pairing kernel on L¹∩L².
@isnad1 id=integrab.2h6v.s10.b8aad3f8897a from=translated src=- shape=faa3676d vocab=4f2f8c1c
-/
theorem densityPairingKernel_integrable (Kminus Kplus : DensityFamily ℝ ι volume)
    (M : SequenceL2 ι →L[ℂ] SequenceL2 ι) {f h : ℝ → ℂ}
    (hf : Integrable f) (hh : Integrable h) :
    Integrable (fun p : ℝ × ℝ => densityPairingKernel Kminus Kplus M p.1 p.2 *
      inner ℂ (h p.1) (f p.2)) (volume.prod volume) := by
  apply (integrable_inner_operator_prod M (Kminus.column_integrable hh)
    (Kplus.column_integrable hf)).congr
  exact Filter.Eventually.of_forall (fun p => by
    simp only [map_smul, inner_smul_left, inner_smul_right, densityPairingKernel,
      RCLike.inner_apply]
    ring)

/-- Weak agreement on Schwartz tests determines a bounded L² operator.
@isnad1 id=eq.1h2v.s14.9999eccc7154 from=translated src=- shape=dbc7c75b vocab=fdd40ce8
-/
theorem operator_eq_of_schwartz_pairings (C D : RealLineL2 →L[ℂ] RealLineL2)
    (hpair : ∀ f h : SchwartzMap ℝ ℂ,
      inner ℂ (h.toLp 2) (C (f.toLp 2)) = inner ℂ (h.toLp 2) (D (f.toLp 2))) : C = D := by
  have hd := SchwartzMap.denseRange_toLpCLM (E := ℝ) (F := ℂ) (p := 2) (μ := volume) ENNReal.ofNat_ne_top
  have he (f : SchwartzMap ℝ ℂ) : C (f.toLp 2) = D (f.toLp 2) := by
    apply ext_inner_left ℂ
    have hall : (fun x : RealLineL2 => inner ℂ x (C (f.toLp 2))) =
        (fun x : RealLineL2 => inner ℂ x (D (f.toLp 2))) :=
      hd.equalizer (continuous_id.inner continuous_const)
        (continuous_id.inner continuous_const) (funext (fun h => hpair f h))
    exact congrFun hall
  have hall := hd.equalizer C.continuous D.continuous (funext he)
  exact DFunLike.coe_injective hall

end Singularity
