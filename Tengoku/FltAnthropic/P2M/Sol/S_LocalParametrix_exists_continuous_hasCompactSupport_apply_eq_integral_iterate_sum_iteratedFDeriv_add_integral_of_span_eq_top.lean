import Tengoku.FltAnthropic.Theorems.Thm_LocalParametrix_exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top
import Tengoku.FltAnthropic.Theorems.Thm_LocalParametrix_exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LocalParametrix_exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LocalParametrix_exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LocalParametrix_exists_continuous_hasCompactSupport_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top

set_option autoImplicit false

noncomputable section

open MeasureTheory Topology
open scoped NNReal

namespace R4LocParam

section Operator

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {ι : Type*} [Fintype ι]

def Lap (A : ι → E →L[ℝ] E) : (E → ℂ) → (E → ℂ) :=
  fun (G : E → ℂ) (y : E) => ∑ i, iteratedFDeriv ℝ 2 G y (fun _ => A i y)

def LapIt (A : ι → E →L[ℝ] E) (m : ℕ) : (E → ℂ) → (E → ℂ) := (Lap A)^[m]

variable (A : ι → E →L[ℝ] E)

/--
@isnad1 id=eq.0h4v.s11.83054754e9f4 from=translated src=- shape=75ae3c2a vocab=0dd3d607
-/
theorem Lap_eq_fderiv (G : E → ℂ) :
    Lap A G = fun y => ∑ i, fderiv ℝ (fderiv ℝ G) y (A i y) (A i y) := by
  funext y
  simp only [Lap, iteratedFDeriv_two_apply]

/--
@isnad1 id=contdiff.1h4v.s7.76be49b590fa from=translated src=- shape=20908529 vocab=146b261f
-/
theorem contDiff_Lap {G : E → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) : ContDiff ℝ (⊤ : ℕ∞) (Lap A G) := by
  rw [Lap_eq_fderiv]
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := (contDiff_infty_iff_fderiv.mp hG).2
  have h2 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ (fderiv ℝ G)) := (contDiff_infty_iff_fderiv.mp h1).2
  refine ContDiff.sum fun i _ => ?_
  exact (h2.clm_apply (A i).contDiff).clm_apply (A i).contDiff

/--
@isnad1 id=le.0h4v.s6.e20cd6290702 from=translated src=- shape=1470b37c vocab=caa68729
-/
theorem tsupport_Lap_subset (G : E → ℂ) : tsupport (Lap A G) ⊆ tsupport G := by
  refine closure_minimal ?_ (isClosed_tsupport G)
  intro y hy
  have hne : iteratedFDeriv ℝ 2 G y ≠ 0 := by
    intro h0
    apply hy
    change ∑ i, iteratedFDeriv ℝ 2 G y (fun _ => A i y) = 0
    simp only [h0, zero_apply, Finset.sum_const_zero]
  exact support_iteratedFDeriv_subset 2 hne

/--
@isnad1 id=hascompa.1h4v.s6.65bf2cd0202f from=translated src=- shape=5f2c7bdb vocab=a94ca363
-/
theorem hasCompactSupport_Lap {G : E → ℂ} (hG : HasCompactSupport G) : HasCompactSupport (Lap A G) :=
  hG.of_isClosed_subset (isClosed_tsupport _) (tsupport_Lap_subset A G)

/--
@isnad1 id=eq.2h5v.s7.b782cfea7ffa from=translated src=- shape=0912fbc6 vocab=1bf8a502
-/
theorem Lap_add {F G : E → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    Lap A (F + G) = Lap A F + Lap A G := by
  funext y
  simp only [Lap, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h2 : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  rw [iteratedFDeriv_add_apply (hF.of_le h2).contDiffAt (hG.of_le h2).contDiffAt]
  rfl

/--
@isnad1 id=eq.0h5v.s6.229bbd4587e3 from=translated src=- shape=1f728738 vocab=f513462a
-/
theorem LapIt_succ (m : ℕ) (G : E → ℂ) : LapIt A (m + 1) G = Lap A (LapIt A m G) := by
  rw [LapIt, LapIt, Function.iterate_succ_apply']

/--
@isnad1 id=eq.0h5v.s6.4d7958f8e15e from=translated src=- shape=2ad4159b vocab=f513462a
-/
theorem LapIt_succ' (m : ℕ) (G : E → ℂ) : LapIt A (m + 1) G = LapIt A m (Lap A G) := by
  rw [LapIt, LapIt, Function.iterate_succ_apply]

/--
@isnad1 id=contdiff.1h5v.s7.046a28a9a7d0 from=translated src=- shape=cb225b72 vocab=b06436d6
-/
theorem contDiff_LapIt (m : ℕ) {G : E → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    ContDiff ℝ (⊤ : ℕ∞) (LapIt A m G) := by
  induction m with
  | zero => exact hG
  | succ m ih => rw [LapIt_succ]; exact contDiff_Lap A ih

/--
@isnad1 id=le.0h5v.s6.e348e261ec68 from=translated src=- shape=476aa172 vocab=2b3c9ded
-/
theorem tsupport_LapIt_subset (m : ℕ) (G : E → ℂ) : tsupport (LapIt A m G) ⊆ tsupport G := by
  induction m with
  | zero => exact subset_rfl
  | succ m ih => rw [LapIt_succ]; exact (tsupport_Lap_subset A _).trans ih

/--
@isnad1 id=eq.2h6v.s7.f4a6367c3e53 from=translated src=- shape=5a58b4ef vocab=8f2d79d6
-/
theorem LapIt_add (m : ℕ) {F G : E → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (hG : ContDiff ℝ (⊤ : ℕ∞) G) :
    LapIt A m (F + G) = LapIt A m F + LapIt A m G := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [LapIt_succ, LapIt_succ, LapIt_succ, ih, Lap_add A (contDiff_LapIt A m hF) (contDiff_LapIt A m hG)]

variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]

def conjA (T : E ≃L[ℝ] W) : ι → W →L[ℝ] W :=
  fun i => (T : E →L[ℝ] W).comp ((A i).comp (T.symm : W →L[ℝ] E))

/--
@isnad1 id=eq.0h7v.s9.b0176c18469b from=translated src=- shape=e4311b4b vocab=60f877e1
-/
theorem conjA_apply (T : E ≃L[ℝ] W) (i : ι) (y : W) : conjA A T i y = T (A i (T.symm y)) := rfl

/--
@isnad1 id=eq.1h6v.s9.2889cd5f373b from=translated src=- shape=27555e60 vocab=d69746ae
-/
theorem Lap_comp_symm (T : E ≃L[ℝ] W) {F : E → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    Lap (conjA A T) (fun y => F (T.symm y)) = fun y => Lap A F (T.symm y) := by
  funext y
  change ∑ i, iteratedFDeriv ℝ 2 (F ∘ ⇑(T.symm : W →L[ℝ] E)) y (fun _ => conjA A T i y) =
    ∑ i, iteratedFDeriv ℝ 2 F (T.symm y) (fun _ => A i (T.symm y))
  have h2 : ((2 : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := WithTop.coe_le_coe.mpr le_top
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (T.symm : W →L[ℝ] E) hF y h2]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  congr 1
  funext j
  change T.symm (conjA A T i y) = A i (T.symm y)
  rw [conjA_apply, ContinuousLinearEquiv.symm_apply_apply]

/--
@isnad1 id=eq.1h7v.s9.3642a4f128ce from=translated src=- shape=e8964f93 vocab=beb6f50e
-/
theorem LapIt_comp_symm (T : E ≃L[ℝ] W) (m : ℕ) {F : E → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) :
    LapIt (conjA A T) m (fun y => F (T.symm y)) = fun y => LapIt A m F (T.symm y) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [LapIt_succ, LapIt_succ, ih]
    exact Lap_comp_symm A T (contDiff_LapIt A m hF)

end Operator

section Transpose

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]
variable (A : ι → E →L[ℝ] E) (μ : Measure E) [μ.IsAddHaarMeasure]

/--
@isnad1 id=contdiff.1h3v.s8.ed9b6a7c71ec from=translated src=- shape=6b18edc9 vocab=c05260ba
-/
theorem contDiff_fderiv_apply {φ : E → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (v : E) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => fderiv ℝ φ y v) :=
  ((contDiff_infty_iff_fderiv.mp hφ).2).clm_apply contDiff_const

/--
@isnad1 id=hascompa.1h3v.s8.a807aea9445a from=translated src=- shape=19a4cab0 vocab=efa30180
-/
theorem hasCompactSupport_fderiv_apply {φ : E → ℂ} (hφ : HasCompactSupport φ) (v : E) :
    HasCompactSupport (fun y => fderiv ℝ φ y v) :=
  hφ.fderiv_apply (𝕜 := ℝ) v

/--
@isnad1 id=le.0h3v.s8.ab96c83c42dd from=translated src=- shape=ed6ea660 vocab=cda64f26
-/
theorem tsupport_fderiv_apply_subset' (φ : E → ℂ) (v : E) :
    tsupport (fun y => fderiv ℝ φ y v) ⊆ tsupport φ :=
  tsupport_fderiv_apply_subset ℝ v

/--
@isnad1 id=eq.1h5v.s11.0b6e1082cffc from=translated src=- shape=e99d06f0 vocab=98386d2f
-/
theorem fderiv_fderiv_apply {G : E → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G) (y v w : E) :
    fderiv ℝ (fderiv ℝ G) y v w = fderiv ℝ (fun z => fderiv ℝ G z w) y v := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ G) := (contDiff_infty_iff_fderiv.mp hG).2
  have hd : DifferentiableAt ℝ (fderiv ℝ G) y :=
    (h1.differentiable (by simp)).differentiableAt
  have := (hd.hasFDerivAt.clm_apply (hasFDerivAt_const w y)).fderiv
  rw [this]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    zero_apply, map_zero, ContinuousLinearMap.flip_apply, zero_add]

/--
@isnad1 id=eq.3h5v.s9.937b51b0c0cc from=translated src=- shape=8dcbc5de vocab=ba3e87ca
-/
theorem ibp {φ ψ : E → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) (v : E) :
    ∫ y, fderiv ℝ φ y v * ψ y ∂μ = - ∫ y, φ y * fderiv ℝ ψ y v ∂μ := by
  have hφd : Differentiable ℝ φ := hφ.differentiable (by simp)
  have hψd : Differentiable ℝ ψ := hψ.differentiable (by simp)
  have hφ'c : Continuous (fun y => fderiv ℝ φ y v) := (contDiff_fderiv_apply hφ v).continuous
  have hψ'c : Continuous (fun y => fderiv ℝ ψ y v) := (contDiff_fderiv_apply hψ v).continuous
  have hψ'k : HasCompactSupport (fun y => fderiv ℝ ψ y v) := hasCompactSupport_fderiv_apply hψc v
  have e1 : (fun y => fderiv ℝ φ y v * ψ y) = fun y => ψ y * fderiv ℝ φ y v := by
    funext y; ring
  rw [e1, integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable]
  · congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    change fderiv ℝ ψ y v * φ y = φ y * fderiv ℝ ψ y v
    ring
  · exact (hψ'c.mul hφ.continuous).integrable_of_hasCompactSupport hψ'k.mul_right
  · exact (hψ.continuous.mul hφ'c).integrable_of_hasCompactSupport hψc.mul_right
  · exact (hψ.continuous.mul hφ.continuous).integrable_of_hasCompactSupport hψc.mul_right
  · exact fun x _ => hψd.differentiableAt
  · exact fun x _ => hφd.differentiableAt

variable {κ : Type*} [Fintype κ] (b : Module.Basis κ ℝ E)

def coef (i : ι) (k : κ) : E → ℂ := fun y => ((b.coord k (A i y) : ℝ) : ℂ)

/--
@isnad1 id=contdiff.0h7v.s7.73eab9fdd4a8 from=translated src=- shape=e74da09c vocab=d8ab7d78
-/
theorem contDiff_coef (i : ι) (k : κ) : ContDiff ℝ (⊤ : ℕ∞) (coef A b i k) := by
  have hlin : ContDiff ℝ (⊤ : ℕ∞) (fun y : E => b.coord k (A i y)) :=
    (LinearMap.toContinuousLinearMap (b.coord k ∘ₗ ((A i : E →L[ℝ] E) : E →ₗ[ℝ] E))).contDiff
  exact Complex.ofRealCLM.contDiff.comp hlin

def LapT (g : E → ℂ) : E → ℂ := fun y =>
  ∑ i, ∑ k, ∑ l, fderiv ℝ (fun z => fderiv ℝ (fun t => coef A b i k t * coef A b i l t * g t) z (b k)) y (b l)

/--
@isnad1 id=contdiff.1h9v.s7.2150e634518b from=translated src=- shape=2a50da9d vocab=3d64123f
-/
theorem contDiff_ccg {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) (i : ι) (k l : κ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => coef A b i k t * coef A b i l t * g t) :=
  ((contDiff_coef A b i k).mul (contDiff_coef A b i l)).mul hg

/--
@isnad1 id=hascompa.1h9v.s7.cbc90524aa45 from=translated src=- shape=afcf66bd vocab=664446f2
-/
theorem hasCompactSupport_ccg {g : E → ℂ} (hg : HasCompactSupport g) (i : ι) (k l : κ) :
    HasCompactSupport (fun t => coef A b i k t * coef A b i l t * g t) := by
  change HasCompactSupport ((fun t => coef A b i k t * coef A b i l t) * g)
  exact hg.mul_left

/--
@isnad1 id=contdiff.1h6v.s7.34b68e2f62a2 from=translated src=- shape=b5c5f597 vocab=70904733
-/
theorem contDiff_LapT {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g) : ContDiff ℝ (⊤ : ℕ∞) (LapT A b g) := by
  unfold LapT
  refine ContDiff.sum fun i _ => ContDiff.sum fun k _ => ContDiff.sum fun l _ => ?_
  exact contDiff_fderiv_apply (contDiff_fderiv_apply (contDiff_ccg A b hg i k l) (b k)) (b l)

/--
@isnad1 id=le.0h6v.s7.588c4fedf5a8 from=translated src=- shape=045426cd vocab=5f6f5274
-/
theorem tsupport_LapT_subset (g : E → ℂ) : tsupport (LapT A b g) ⊆ tsupport g := by
  refine closure_minimal ?_ (isClosed_tsupport g)
  intro y hy
  by_contra hyg
  apply hy
  change ∑ i, ∑ k, ∑ l, fderiv ℝ (fun z => fderiv ℝ (fun t => coef A b i k t * coef A b i l t * g t) z
    (b k)) y (b l) = 0
  refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
  have h1 : tsupport (fun z => fderiv ℝ (fun t => coef A b i k t * coef A b i l t * g t) z (b k)) ⊆
      tsupport g :=
    (tsupport_fderiv_apply_subset' _ (b k)).trans
      (tsupport_mul_subset_right (f := fun t => coef A b i k t * coef A b i l t) (g := g))
  have h2 : y ∉ tsupport (fun z => fderiv ℝ (fun t => coef A b i k t * coef A b i l t * g t) z (b k)) :=
    fun h => hyg (h1 h)
  rw [fderiv_of_notMem_tsupport ℝ h2, zero_apply]

/--
@isnad1 id=hascompa.1h6v.s7.b23f9e1818b3 from=translated src=- shape=ff60d304 vocab=c748795f
-/
theorem hasCompactSupport_LapT {g : E → ℂ} (hg : HasCompactSupport g) : HasCompactSupport (LapT A b g) :=
  hg.of_isClosed_subset (isClosed_tsupport _) (tsupport_LapT_subset A b g)

/--
@isnad1 id=eq.1h8v.s11.1409a6d99ce6 from=translated src=- shape=17f9171c vocab=95e89650
-/
theorem fderiv_fderiv_expand {F : E → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F) (i : ι) (y : E) :
    fderiv ℝ (fderiv ℝ F) y (A i y) (A i y) =
      ∑ k, ∑ l, coef A b i k y * coef A b i l y * fderiv ℝ (fun z => fderiv ℝ F z (b l)) y (b k) := by
  set L := fderiv ℝ (fderiv ℝ F) y with hL
  have hv : A i y = ∑ k, (b.coord k (A i y)) • b k := by
    conv_lhs => rw [← b.sum_repr (A i y)]
    rfl
  have step1 : L (A i y) = ∑ k, (b.coord k (A i y)) • L (b k) := by
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_smul]
  have step2 : ∀ k, L (b k) (A i y) = ∑ l, (b.coord l (A i y)) • L (b k) (b l) := by
    intro k
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul]
  rw [step1, sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_apply, step2 k, Finset.smul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [hL, fderiv_fderiv_apply hF y (b k) (b l)]
  simp only [coef]
  rw [Complex.real_smul, Complex.real_smul]
  ring

/--
@isnad1 id=eq.3h8v.s8.6b431b4598fb from=translated src=- shape=06cf8251 vocab=cf959140
-/
theorem integral_Lap_mul {F g : E → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (hg : ContDiff ℝ (⊤ : ℕ∞) g) (hgc : HasCompactSupport g) :
    ∫ y, Lap A F y * g y ∂μ = ∫ y, F y * LapT A b g y ∂μ := by

  have hF1 : ∀ w : E, ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ F z w) := fun w => contDiff_fderiv_apply hF w
  have lhs : (fun y => Lap A F y * g y) = fun y => ∑ i, ∑ k, ∑ l,
      fderiv ℝ (fun z => fderiv ℝ F z (b l)) y (b k) * (coef A b i k y * coef A b i l y * g y) := by
    funext y
    rw [Lap_eq_fderiv, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [fderiv_fderiv_expand A b hF i y, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  have rhs : (fun y => F y * LapT A b g y) = fun y => ∑ i, ∑ k, ∑ l,
      F y * fderiv ℝ (fun z => fderiv ℝ (fun t => coef A b i k t * coef A b i l t * g t) z (b k)) y
        (b l) := by
    funext y
    simp only [LapT, Finset.mul_sum]

  have hint_l : ∀ i k l, Integrable (fun y => fderiv ℝ (fun z => fderiv ℝ F z (b l)) y (b k) *
      (coef A b i k y * coef A b i l y * g y)) μ := fun i k l =>
    ((contDiff_fderiv_apply (hF1 (b l)) (b k)).continuous.mul
      (contDiff_ccg A b hg i k l).continuous).integrable_of_hasCompactSupport
      (hasCompactSupport_ccg A b hgc i k l).mul_left
  have hint_r : ∀ i k l, Integrable (fun y => F y * fderiv ℝ (fun z => fderiv ℝ
      (fun t => coef A b i k t * coef A b i l t * g t) z (b k)) y (b l)) μ := fun i k l =>
    (hF.continuous.mul (contDiff_fderiv_apply (contDiff_fderiv_apply (contDiff_ccg A b hg i k l)
      (b k)) (b l)).continuous).integrable_of_hasCompactSupport
      ((hasCompactSupport_fderiv_apply (hasCompactSupport_fderiv_apply
        (hasCompactSupport_ccg A b hgc i k l) (b k)) (b l)).mul_left)
  rw [lhs, rhs]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ => hint_l i k l]
  rw [integral_finsetSum _ fun i _ => integrable_finsetSum _ fun k _ =>
    integrable_finsetSum _ fun l _ => hint_r i k l]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint_l i k l,
    integral_finsetSum _ fun k _ => integrable_finsetSum _ fun l _ => hint_r i k l]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [integral_finsetSum _ fun l _ => hint_l i k l, integral_finsetSum _ fun l _ => hint_r i k l]
  refine Finset.sum_congr rfl fun l _ => ?_

  have hccg := contDiff_ccg A b hg i k l
  have hccgc := hasCompactSupport_ccg A b hgc i k l
  rw [ibp μ (hF1 (b l)) hccg hccgc (b k)]
  rw [ibp μ hF (contDiff_fderiv_apply hccg (b k)) (hasCompactSupport_fderiv_apply hccgc (b k)) (b l)]
  rw [neg_neg]

/--
@isnad1 id=ex.2h6v.s8.ccdd63689a00 from=translated src=- shape=29f1f04c vocab=eb713309
-/
theorem exists_transpose_LapIt (m : ℕ) {g : E → ℂ} (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hgc : HasCompactSupport g) :
    ∃ h : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) h ∧ HasCompactSupport h ∧ tsupport h ⊆ tsupport g ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        ∫ y, LapIt A m F y * g y ∂μ = ∫ y, F y * h y ∂μ := by
  induction m generalizing g with
  | zero => exact ⟨g, hg, hgc, subset_rfl, fun F _ _ => rfl⟩
  | succ m ih =>
    obtain ⟨h, hh, hhc, hhs, hid⟩ := ih hg hgc
    let b := Module.finBasis ℝ E
    refine ⟨LapT A b h, contDiff_LapT A b hh, hasCompactSupport_LapT A b hhc,
      (tsupport_LapT_subset A b h).trans hhs, fun F hF hFc => ?_⟩
    have e1 : (fun y => LapIt A (m + 1) F y * g y) = fun y => LapIt A m (Lap A F) y * g y := by
      funext y; rw [LapIt_succ']
    rw [e1, hid (Lap A F) (contDiff_Lap A hF) (hasCompactSupport_Lap A hFc)]
    exact integral_Lap_mul A μ b hF hh hhc

end Transpose

section Transport

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]
variable {ι : Type*} [Fintype ι]

/--
@isnad1 id=ex.1h11v.s10.02259fabb542 from=translated src=- shape=363dfd91 vocab=d0bee84d
-/
theorem transport (A : ι → E →L[ℝ] E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (ν : Measure W) [ν.IsAddHaarMeasure] (T : E ≃L[ℝ] W) (x₀ : E) (m : ℕ) (u w : W → ℂ)
    (hid : ∀ G : W → ℂ, ContDiff ℝ (⊤ : ℕ∞) G → HasCompactSupport G →
      G (T x₀) = (∫ y, LapIt (conjA A T) m G y * u y ∂ν) + ∫ y, G y * w y ∂ν) :
    ∃ c : ℝ≥0, ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
      F x₀ = (∫ x, LapIt A m F x * ((c : ℂ) * u (T x)) ∂μ) + ∫ x, F x * ((c : ℂ) * w (T x)) ∂μ := by

  set ν' : Measure W := Measure.map (T : E → W) μ with hν'
  haveI : ν'.IsAddHaarMeasure := by
    rw [hν']
    exact ContinuousLinearEquiv.isAddHaarMeasure_map T μ
  set c : ℝ≥0 := ν.addHaarScalarFactor ν' with hc
  have hνc : ν = c • ν' := Measure.isAddLeftInvariant_eq_smul ν ν'
  have hT : IsClosedEmbedding (T : E → W) := T.toHomeomorph.isClosedEmbedding
  have key : ∀ Φ : W → ℂ, ∫ y, Φ y ∂ν = (c : ℂ) * ∫ x, Φ (T x) ∂μ := by
    intro Φ
    rw [hνc, integral_smul_nnreal_measure, hν', hT.integral_map]
    rw [NNReal.smul_def, Complex.real_smul]
  refine ⟨c, fun F hF hFc => ?_⟩
  have hG : ContDiff ℝ (⊤ : ℕ∞) (fun y => F (T.symm y)) := hF.comp (T.symm : W →L[ℝ] E).contDiff
  have hGc : HasCompactSupport (fun y => F (T.symm y)) := by
    change HasCompactSupport (F ∘ T.symm.toHomeomorph)
    exact hFc.comp_homeomorph T.symm.toHomeomorph
  have h0 := hid (fun y => F (T.symm y)) hG hGc
  simp only [ContinuousLinearEquiv.symm_apply_apply] at h0
  rw [h0, LapIt_comp_symm A T m hF, key, key]
  simp only [ContinuousLinearEquiv.symm_apply_apply]
  rw [← integral_const_mul, ← integral_const_mul]
  congr 1
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change (c : ℂ) * (LapIt A m F x * u (T x)) = LapIt A m F x * ((c : ℂ) * u (T x))
    ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    change (c : ℂ) * (F x * w (T x)) = F x * ((c : ℂ) * w (T x))
    ring

end Transport

section Main

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
variable {ι : Type*} [Fintype ι]

/--
@isnad1 id=ex.3h7v.s9.376fdc4aaa45 from=translated src=- shape=58d80447 vocab=2cf04501
-/
theorem main (μ : Measure E) [μ.IsAddHaarMeasure]
    (A : ι → E →L[ℝ] E) (x₀ : E)
    (hA : Submodule.span ℝ (Set.range fun i => A i x₀) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ E < 2 * m) (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, LapIt A m F x * g₁ x ∂μ) + ∫ x, F x * g₂ x ∂μ := by

  set d : ℕ := Module.finrank ℝ E with hd
  let T : E ≃L[ℝ] EuclideanSpace ℝ (Fin d) := toEuclidean
  set A' : ι → EuclideanSpace ℝ (Fin d) →L[ℝ] EuclideanSpace ℝ (Fin d) := conjA A T with hA'def
  have hA' : Submodule.span ℝ (Set.range fun i => A' i (T x₀)) = ⊤ := by
    have hr : (Set.range fun i => A' i (T x₀)) =
        ((T : E →L[ℝ] EuclideanSpace ℝ (Fin d)) : E →ₗ[ℝ] EuclideanSpace ℝ (Fin d)) ''
          (Set.range fun i => A i x₀) := by
      ext v
      simp only [Set.mem_range, Set.mem_image, exists_exists_eq_and, hA'def, conjA_apply,
        ContinuousLinearEquiv.symm_apply_apply]
      constructor
      · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
      · rintro ⟨i, rfl⟩; exact ⟨i, rfl⟩
    rw [hr, Submodule.span_image, hA, Submodule.map_top]
    exact LinearMap.range_eq_top.mpr T.surjective
  have hm' : Module.finrank ℝ (EuclideanSpace ℝ (Fin d)) < 2 * m := by
    rw [finrank_euclideanSpace_fin]; exact hm

  obtain ⟨u, w, hu, hw, hu', hidW⟩ :=
    LocalParametrix.exists_continuous_contDiffOn_apply_eq_integral_iterate_sum_iteratedFDeriv_add_integral_of_span_eq_top
      A' (T x₀) hA' m hm'

  obtain ⟨c, hidE⟩ := transport A μ volume T x₀ m u w hidW
  set u₁ : E → ℂ := fun x => (c : ℂ) * u (T x) with hu₁
  set w₁ : E → ℂ := fun x => (c : ℂ) * w (T x) with hw₁
  have hu₁c : Continuous u₁ := continuous_const.mul (hu.comp T.continuous)
  have hw₁c : Continuous w₁ := continuous_const.mul (hw.comp T.continuous)
  have hu₁' : ContDiffOn ℝ (⊤ : ℕ∞) u₁ {x₀}ᶜ := by
    refine contDiffOn_const.mul ?_
    refine hu'.comp (T : E →L[ℝ] EuclideanSpace ℝ (Fin d)).contDiff.contDiffOn ?_
    intro x hx hTx
    exact hx (T.injective hTx)

  haveI : IsFiniteMeasureOnCompacts μ := inferInstance
  exact
    LocalParametrix.exists_hasCompactSupport_apply_eq_integral_add_integral_of_contDiffOn_compl_singleton
      μ (LapIt A m)
      (fun F G hF _ hG _ => LapIt_add A m hF hG)
      (fun F hF _ => (contDiff_LapIt A m hF).continuous)
      (fun F _ _ => tsupport_LapIt_subset A m F)
      (fun g hg hgc => by
        obtain ⟨h, hh, hhc, hhs, hid⟩ := exists_transpose_LapIt A μ m hg hgc
        exact ⟨h, hh.continuous, hhs, hid⟩)
      x₀ u₁ w₁ hu₁c hw₁c hu₁' hidE V hV

end Main

end R4LocParam

end

open MeasureTheory Topology in
/--
@isnad1 id=ex.3h7v.s10.30592e3fe979 from=translated src=- shape=78214066 vocab=51af9231
-/
theorem solution
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
    {ι : Type*} [Fintype ι] (A : ι → E →L[ℝ] E) (x₀ : E)
    (hA : Submodule.span ℝ (Set.range fun i => A i x₀) = ⊤)
    (m : ℕ) (hm : Module.finrank ℝ E < 2 * m) (V : Set E) (hV : V ∈ 𝓝 x₀) :
    ∃ g₁ g₂ : E → ℂ, Continuous g₁ ∧ Continuous g₂ ∧
      HasCompactSupport g₁ ∧ HasCompactSupport g₂ ∧ tsupport g₁ ⊆ V ∧ tsupport g₂ ⊆ V ∧
      ∀ F : E → ℂ, ContDiff ℝ (⊤ : ℕ∞) F → HasCompactSupport F →
        F x₀ = (∫ x, ((fun (G : E → ℂ) (y : E) =>
                  ∑ i, iteratedFDeriv ℝ 2 G y (fun _ => A i y))^[m] F) x * g₁ x ∂μ) +
          ∫ x, F x * g₂ x ∂μ :=
  R4LocParam.main μ A x₀ hA m hm V hV
