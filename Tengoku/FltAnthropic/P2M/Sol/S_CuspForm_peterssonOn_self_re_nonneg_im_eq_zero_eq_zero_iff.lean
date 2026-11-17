import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CuspForm_PeterssonOn
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FundamentalDomainVolume

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter
open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace PetOnIP2

variable {Γ : Subgroup SL(2, ℤ)} [Γ.FiniteIndex] {k : ℤ}

local notation "Γᴳᴸ" => ((Γ : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

/--
@isnad1 id=continuo.0h0v.s7.9213c1ba3a46 from=translated src=- shape=6cb9e56d vocab=434fe350
-/
scoped instance sl2zContinuousConstSMul : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul γ := by
    have h : (fun z : ℍ => γ • z) =
        fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ : GL (Fin 2) ℝ) • z := by
      funext z
      exact MulAction.compHom_smul_def (Matrix.SpecialLinearGroup.mapGL ℝ) γ z
    rw [h]
    exact continuous_const_smul _

scoped instance fintypeQuot : Fintype (SL(2, ℤ) ⧸ Γ) :=
  haveI : Finite (SL(2, ℤ) ⧸ Γ) := Subgroup.finite_quotient_of_finiteIndex
  Fintype.ofFinite _

def cosum (Φ : ℍ → ℂ) (x : ℍ) : ℂ := ∑ q : SL(2, ℤ) ⧸ Γ, Φ ((q.out⁻¹ : SL(2, ℤ)) • x)

/--
@isnad1 id=eq.0h4v.s6.d812b939f2c1 from=translated src=- shape=cf9b44ef vocab=4637b5c1
-/
theorem integrand_eq (F G : ℍ → ℂ) :
    CuspForm.peterssonOnIntegrand Γ k F G = cosum (Γ := Γ) (UpperHalfPlane.petersson k F G) := by
  funext x
  unfold CuspForm.peterssonOnIntegrand cosum
  rw [finsum_eq_sum_of_fintype]
  exact Finset.sum_congr rfl fun q _ => UpperHalfPlane.petersson_slash_SL k F G _ x

/--
@isnad1 id=ex.0h4v.s9.2f65463a0061 from=translated src=- shape=e3bfd1fd vocab=10b6c998
-/
theorem petersson_bounded (f g : CuspForm Γᴳᴸ k) :
    ∃ C, ∀ x, ‖UpperHalfPlane.petersson k ⇑f ⇑g x‖ ≤ C :=
  CuspFormClass.petersson_bounded_left k Γᴳᴸ f g

def dens (f : CuspForm Γᴳᴸ k) (x : ℍ) : ℝ := ‖f x‖ ^ 2 * x.im ^ k

omit [Γ.FiniteIndex] in
/--
@isnad1 id=le.0h4v.s7.f9aac5fbf147 from=translated src=- shape=7960cd4f vocab=2e103bd1
-/
theorem dens_nonneg (f : CuspForm Γᴳᴸ k) (x : ℍ) : 0 ≤ dens f x :=
  mul_nonneg (sq_nonneg _) (zpow_nonneg x.im_pos.le _)

omit [Γ.FiniteIndex] in
/--
@isnad1 id=eq.0h4v.s9.d39d8079c57a from=translated src=- shape=c54a7422 vocab=3339017c
-/
theorem petersson_self_eq_dens (f : CuspForm Γᴳᴸ k) (x : ℍ) :
    UpperHalfPlane.petersson k ⇑f ⇑f x = ((dens f x : ℝ) : ℂ) := by
  unfold UpperHalfPlane.petersson dens
  rw [Complex.conj_mul' (f x)]
  push_cast
  ring

omit [Γ.FiniteIndex] in
/--
@isnad1 id=continuo.0h3v.s7.0cd2ce11055f from=translated src=- shape=eb657e45 vocab=098d1116
-/
theorem continuous_dens (f : CuspForm Γᴳᴸ k) : Continuous (dens f) := by
  unfold dens
  refine ((continuous_norm.comp (CuspFormClass.holo f).continuous).pow 2).mul ?_
  exact (UpperHalfPlane.continuous_im.zpow₀ k fun x => Or.inl (x.im_pos.ne'))

def rdens (f : CuspForm Γᴳᴸ k) (x : ℍ) : ℝ := ∑ q : SL(2, ℤ) ⧸ Γ, dens f ((q.out⁻¹ : SL(2, ℤ)) • x)

/--
@isnad1 id=le.0h4v.s7.4ee96c48c813 from=translated src=- shape=dea551f3 vocab=82d8a9d4
-/
theorem rdens_nonneg (f : CuspForm Γᴳᴸ k) (x : ℍ) : 0 ≤ rdens f x :=
  Finset.sum_nonneg fun _ _ => dens_nonneg f _

/--
@isnad1 id=continuo.0h3v.s7.0c9161125ab8 from=translated src=- shape=601b35ab vocab=cd6b8172
-/
theorem continuous_rdens (f : CuspForm Γᴳᴸ k) : Continuous (rdens f) :=
  continuous_finsetSum _ fun _ _ => (continuous_dens f).comp (continuous_const_smul _)

/--
@isnad1 id=eq.0h3v.s9.0f06d223d09b from=translated src=- shape=97033c91 vocab=a7aad045
-/
theorem integrand_self_eq (f : CuspForm Γᴳᴸ k) :
    CuspForm.peterssonOnIntegrand Γ k ⇑f ⇑f = fun x => ((rdens f x : ℝ) : ℂ) := by
  rw [integrand_eq]
  funext x
  simp only [cosum, rdens, petersson_self_eq_dens, Complex.ofReal_sum]

/--
@isnad1 id=integrab.0h3v.s8.579b8d6c035b from=translated src=- shape=07aa7802 vocab=23cc4f13
-/
theorem integrable_rdens (f : CuspForm Γᴳᴸ k) : Integrable (rdens f) (volume.restrict (𝒟 : Set ℍ)) := by
  obtain ⟨C, hC⟩ := petersson_bounded f f
  refine Measure.integrableOn_of_bounded (M := ∑ _q : SL(2, ℤ) ⧸ Γ, C)
    FLT.FundamentalDomainVolume.volume_fd_lt_top.ne (continuous_rdens f).aestronglyMeasurable ?_
  refine Filter.Eventually.of_forall fun x => ?_
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  have := hC ((q.out⁻¹ : SL(2, ℤ)) • x)
  rwa [petersson_self_eq_dens, Complex.norm_real] at this

/--
@isnad1 id=eq.0h3v.s9.4b4cecf6c581 from=translated src=- shape=7345818e vocab=5cfe2706
-/
theorem peterssonOn_self_eq (f : CuspForm Γᴳᴸ k) :
    CuspForm.peterssonOn Γ k f f = ((∫ x in (𝒟 : Set ℍ), rdens f x : ℝ) : ℂ) := by
  rw [CuspForm.peterssonOn_def, integrand_self_eq, integral_complex_ofReal]

/--
@isnad1 id=le.0h3v.s9.a7ba545558c3 from=translated src=- shape=7c1a2029 vocab=53cab797
-/
theorem peterssonOn_self_re_nonneg (f : CuspForm Γᴳᴸ k) : 0 ≤ (CuspForm.peterssonOn Γ k f f).re := by
  rw [peterssonOn_self_eq, Complex.ofReal_re]
  exact setIntegral_nonneg ModularGroup.isClosed_fd.measurableSet fun x _ => rdens_nonneg f x

/--
@isnad1 id=eq.0h3v.s9.d660a3206605 from=translated src=- shape=376da5f8 vocab=5317bc9c
-/
theorem peterssonOn_self_im (f : CuspForm Γᴳᴸ k) : (CuspForm.peterssonOn Γ k f f).im = 0 := by
  rw [peterssonOn_self_eq, Complex.ofReal_im]

def w₀ : ℍ := ⟨2 * Complex.I, by simp⟩

/--
@isnad1 id=mem.0h0v.s3.0c4d2d55cea0 from=translated src=- shape=d1530203 vocab=7d314ad3
-/
theorem w₀_mem_fdo : w₀ ∈ 𝒟ᵒ := by
  refine ⟨?_, ?_⟩
  · show 1 < Complex.normSq (2 * Complex.I)
    simp [Complex.normSq_apply]; norm_num
  · show |(2 * Complex.I).re| < 1 / 2
    simp

/--
@isnad1 id=eq.2h4v.s8.b508e89d434a from=translated src=- shape=7b472e92 vocab=e827e403
-/
theorem rdens_eq_zero_of_integral_eq_zero (f : CuspForm Γᴳᴸ k)
    (h : ∫ x in (𝒟 : Set ℍ), rdens f x = 0) {x : ℍ} (hx : x ∈ 𝒟ᵒ) : rdens f x = 0 := by

  have hae : ∀ᵐ y ∂(volume.restrict (𝒟 : Set ℍ)), rdens f y = 0 := by
    have := (integral_eq_zero_iff_of_nonneg_ae (Filter.Eventually.of_forall (rdens_nonneg f))
      (integrable_rdens f)).mp h
    filter_upwards [this] with y hy using hy
  by_contra hne
  have hpos : 0 < rdens f x := lt_of_le_of_ne (rdens_nonneg f x) (Ne.symm hne)

  set U : Set ℍ := 𝒟ᵒ ∩ {y | rdens f x / 2 < rdens f y} with hU
  have hUopen : IsOpen U :=
    ModularGroup.isOpen_fdo.inter (isOpen_lt continuous_const (continuous_rdens f))
  have hxU : x ∈ U := ⟨hx, by show rdens f x / 2 < rdens f x; linarith⟩
  have hUpos : 0 < volume U := FLT.HyperbolicMeasure.volume_pos_of_isOpen hUopen ⟨x, hxU⟩
  have hUfd : U ⊆ 𝒟 := fun y hy => ModularGroup.fdo_subset_fd hy.1

  have hzero : volume.restrict (𝒟 : Set ℍ) U = 0 := by
    refine measure_eq_zero_iff_ae_notMem.mpr ?_
    filter_upwards [hae] with y hy hyU
    have : rdens f x / 2 < rdens f y := hyU.2
    rw [hy] at this
    linarith
  rw [Measure.restrict_apply hUopen.measurableSet, Set.inter_eq_self_of_subset_left hUfd] at hzero
  exact hUpos.ne' hzero

theorem eq_zero_of_peterssonOn_self_eq_zero (f : CuspForm Γᴳᴸ k) (h : CuspForm.peterssonOn Γ k f f = 0) :
    f = 0 := by
  have hint : ∫ x in (𝒟 : Set ℍ), rdens f x = 0 := by
    have := congrArg Complex.re h
    rwa [peterssonOn_self_eq, Complex.ofReal_re, Complex.zero_re] at this

  set q₀ : SL(2, ℤ) ⧸ Γ := QuotientGroup.mk 1 with hq₀
  set σ : SL(2, ℤ) := q₀.out⁻¹ with hσ
  have hvan : ∀ x ∈ 𝒟ᵒ, f (σ • x) = 0 := by
    intro x hx
    have h0 := rdens_eq_zero_of_integral_eq_zero f hint hx
    have hterm : dens f (σ • x) = 0 := by
      have hle : dens f (σ • x) ≤ rdens f x := by
        rw [rdens]
        exact Finset.single_le_sum (f := fun q : SL(2, ℤ) ⧸ Γ => dens f ((q.out⁻¹ : SL(2, ℤ)) • x))
          (fun q _ => dens_nonneg f _) (Finset.mem_univ q₀)
      exact le_antisymm (h0 ▸ hle) (dens_nonneg f _)
    have : ‖f (σ • x)‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp hterm with h1 | h1
      · exact h1
      · exact absurd h1 (zpow_ne_zero _ (σ • x).im_pos.ne')
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)

  set V : Set ℍ := (fun x : ℍ => σ • x) '' 𝒟ᵒ with hV
  have hVopen : IsOpen V := (Homeomorph.smul σ (α := ℍ)).isOpenMap _ ModularGroup.isOpen_fdo
  have hVne : (σ • w₀) ∈ V := ⟨w₀, w₀_mem_fdo, rfl⟩
  have hfV : ∀ y ∈ V, f y = 0 := by
    rintro _ ⟨x, hx, rfl⟩; exact hvan x hx

  set F : ℂ → ℂ := ⇑f ∘ ofComplex with hF
  have hFdiff : DifferentiableOn ℂ F {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp (CuspFormClass.holo f)
  have hopen : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hFan : AnalyticOnNhd ℂ F {z : ℂ | 0 < z.im} := hFdiff.analyticOnNhd hopen
  have hconn : IsPreconnected {z : ℂ | 0 < z.im} :=
    (convex_halfSpace_im_gt 0).isPreconnected
  set z₀ : ℂ := ((σ • w₀ : ℍ) : ℂ) with hz₀
  have hz₀mem : z₀ ∈ {z : ℂ | 0 < z.im} := (σ • w₀).im_pos
  have hev : F =ᶠ[nhds z₀] 0 := by

    have hWopen : IsOpen (((↑) : ℍ → ℂ) '' V) := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ hVopen
    have hz₀W : z₀ ∈ ((↑) : ℍ → ℂ) '' V := ⟨σ • w₀, hVne, rfl⟩
    filter_upwards [hWopen.mem_nhds hz₀W] with z hz
    obtain ⟨y, hy, rfl⟩ := hz
    simp only [hF, Function.comp_apply, ofComplex_apply, Pi.zero_apply]
    exact hfV y hy
  have hzero := hFan.eqOn_zero_of_preconnected_of_eventuallyEq_zero hconn hz₀mem hev
  apply DFunLike.ext f 0
  intro y
  have := hzero y.im_pos
  simp only [hF, Function.comp_apply, ofComplex_apply, Pi.zero_apply] at this
  simpa using this

/--
@isnad1 id=iff.0h3v.s10.5c14e0476901 from=translated src=- shape=2d726a8e vocab=07a53f05
-/
theorem peterssonOn_self_eq_zero_iff (f : CuspForm Γᴳᴸ k) : CuspForm.peterssonOn Γ k f f = 0 ↔ f = 0 := by
  constructor
  · exact eq_zero_of_peterssonOn_self_eq_zero f
  · rintro rfl
    rw [peterssonOn_self_eq]
    have : rdens (0 : CuspForm Γᴳᴸ k) = fun _ => 0 := by
      funext x; simp [rdens, dens]
    rw [this]
    simp

end PetOnIP2
open scoped _root_.P2MW.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff.PetOnIP2

end
open scoped _root_.P2MW.S_CuspForm_peterssonOn_self_re_nonneg_im_eq_zero_eq_zero_iff.PetOnIP2

open scoped MatrixGroups in
/--
@isnad1 id=and.0h3v.s11.bfa79f901738 from=translated src=- shape=2c5ef99b vocab=b74c6acf
-/
theorem solution (Γ : Subgroup SL(2, ℤ))
    [Γ.FiniteIndex] (k : ℤ) (f : CuspForm (Γ : Subgroup (GL (Fin 2) ℝ)) k) :
    0 ≤ (CuspForm.peterssonOn Γ k f f).re ∧ (CuspForm.peterssonOn Γ k f f).im = 0 ∧
    (CuspForm.peterssonOn Γ k f f = 0 ↔ f = 0) :=
  ⟨PetOnIP2.peterssonOn_self_re_nonneg f, PetOnIP2.peterssonOn_self_im f,
    PetOnIP2.peterssonOn_self_eq_zero_iff f⟩
