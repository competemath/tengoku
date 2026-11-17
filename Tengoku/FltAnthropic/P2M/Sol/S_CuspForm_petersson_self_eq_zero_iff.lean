import Tengoku.FltAnthropic.Definitions.Def_CuspForm_Petersson
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FundamentalDomainVolume

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_petersson_self_eq_zero_iff.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_petersson_self_eq_zero_iff

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm ComplexConjugate Modular

namespace AlliAux1Pet

variable {N : ℕ} {k : ℤ}

def tr (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) : ℍ → ℂ :=
  ⇑f ∣[k] (σ⁻¹ : SL(2, ℤ))

/--
@isnad1 id=eq.0h3v.s9.7df42996f278 from=translated src=- shape=d49bf04e vocab=1c3f4462
-/
theorem tr_one (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : tr f 1 = ⇑f := by
  simp [tr]

/--
@isnad1 id=eq.1h5v.s8.dc0f1aaa3442 from=translated src=- shape=e5f9adfd vocab=26506d81
-/
theorem tr_mul_of_mem (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ γ : SL(2, ℤ))
    (hγ : γ ∈ CongruenceSubgroup.Gamma0 N) : tr f (σ * γ) = tr f σ := by
  unfold tr
  rw [mul_inv_rev, SlashAction.slash_mul]
  congr 1
  exact SlashInvariantFormClass.slash_action_eq f _
    (Subgroup.mem_map_of_mem (Matrix.SpecialLinearGroup.mapGL ℝ) (inv_mem hγ))

/--
@isnad1 id=eq.0h4v.s13.a8c0c657a96c from=translated src=- shape=f9eb3a95 vocab=5f6e27e6
-/
theorem tr_eq_coe_translate (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) :
    tr f σ = ⇑(CuspForm.translate f (σ⁻¹ : SL(2, ℤ))) := by
  rw [CuspForm.coe_translate]; rfl

/--
@isnad1 id=continuo.0h4v.s7.4c07d6163997 from=translated src=- shape=ae879e3f vocab=64a55be4
-/
theorem continuous_tr (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) :
    Continuous (tr f σ) := by
  rw [tr_eq_coe_translate]
  exact (CuspForm.translate f (σ⁻¹ : SL(2, ℤ))).holo'.continuous

/--
@isnad1 id=eq.0h6v.s10.bb8846cf4a0f from=translated src=- shape=394a9385 vocab=af0ab096
-/
theorem petersson_tr (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.petersson k (tr f σ) (tr g σ) τ =
      UpperHalfPlane.petersson k ⇑f ⇑g ((σ⁻¹ : SL(2, ℤ)) • τ) :=
  UpperHalfPlane.petersson_slash_SL k ⇑f ⇑g σ⁻¹ τ

def summand (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (τ : ℍ) : ℂ :=
  UpperHalfPlane.petersson k (tr f q.out) (tr g q.out) τ

/--
@isnad1 id=eq.0h5v.s9.eb4764836946 from=translated src=- shape=0eebad85 vocab=fb00ee7a
-/
theorem integrand_eq_finsum (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f g τ = ∑ᶠ q, summand f g q τ := rfl

/--
@isnad1 id=eq.0h5v.s9.05e6c81699d5 from=translated src=- shape=8850e7dc vocab=dd06a75a
-/
theorem integrand_eq_sum [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f g τ = ∑ q, summand f g q τ := by
  rw [integrand_eq_finsum, finsum_eq_sum_of_fintype]

def selfDensity [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) : ℝ :=
  ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ‖tr f q.out τ‖ ^ 2 * τ.im ^ k

/--
@isnad1 id=eq.0h3v.s5.29a8a5ba3bd0 from=translated src=- shape=b2a5f648 vocab=49ae1aab
-/
theorem petersson_self_pt (h : ℍ → ℂ) (τ : ℍ) :
    UpperHalfPlane.petersson k h h τ = ((‖h τ‖ ^ 2 * τ.im ^ k : ℝ) : ℂ) := by
  unfold UpperHalfPlane.petersson
  rw [Complex.conj_mul']
  push_cast
  ring

/--
@isnad1 id=eq.0h4v.s8.6db885e3655f from=translated src=- shape=f391d3f7 vocab=682f70c7
-/
theorem integrand_self_eq [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f f τ = (selfDensity f τ : ℂ) := by
  rw [integrand_eq_sum, selfDensity, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact petersson_self_pt _ _

/--
@isnad1 id=le.0h4v.s8.ed9258cb3679 from=translated src=- shape=10dfa17e vocab=c90264ab
-/
theorem selfDensity_nonneg [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) : 0 ≤ selfDensity f τ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le _)

/--
@isnad1 id=continuo.0h3v.s8.cb37ccebe7b9 from=translated src=- shape=e92ad753 vocab=a21ab1d6
-/
theorem continuous_selfDensity [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : Continuous (selfDensity f) := by
  unfold selfDensity
  refine continuous_finsetSum _ fun q _ => ?_
  refine ((continuous_tr f _).norm.pow 2).mul ?_
  exact (UpperHalfPlane.continuous_im.zpow₀ k fun τ => Or.inl (UpperHalfPlane.im_ne_zero τ))

def twoI : ℍ := ⟨2 * Complex.I, by simp⟩

/--
@isnad1 id=mem.0h0v.s3.fa014f87052d from=translated src=- shape=d1530203 vocab=29365442
-/
theorem twoI_mem_fdo : twoI ∈ ModularGroup.fdo := by
  refine ⟨?_, ?_⟩
  · show 1 < Complex.normSq (2 * Complex.I)
    simp [Complex.normSq_apply]
    norm_num
  · show |(2 * Complex.I).re| < 1 / 2
    simp

theorem eq_zero_of_eqOn_fdo (f : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (hf : ∀ τ ∈ ModularGroup.fdo, f τ = 0) : f = 0 := by

  set G : ℂ → ℂ := ⇑f ∘ UpperHalfPlane.ofComplex with hG
  have hU : IsOpen {z : ℂ | 0 < z.im} := isOpen_lt continuous_const Complex.continuous_im
  have hdiff : DifferentiableOn ℂ G {z : ℂ | 0 < z.im} :=
    UpperHalfPlane.mdifferentiable_iff.mp f.holo'
  have han : AnalyticOnNhd ℂ G {z : ℂ | 0 < z.im} := hdiff.analyticOnNhd hU
  have hpre : IsPreconnected {z : ℂ | 0 < z.im} := (convex_halfSpace_im_gt 0).isPreconnected
  have hz₀ : ((twoI : ℍ) : ℂ) ∈ {z : ℂ | 0 < z.im} := twoI.im_pos

  have hev : G =ᶠ[𝓝 ((twoI : ℍ) : ℂ)] 0 := by
    have hopen : IsOpen (UpperHalfPlane.coe '' ModularGroup.fdo) :=
      UpperHalfPlane.isOpenEmbedding_coe.isOpenMap _ ModularGroup.isOpen_fdo
    have hmem : ((twoI : ℍ) : ℂ) ∈ UpperHalfPlane.coe '' ModularGroup.fdo := ⟨twoI, twoI_mem_fdo, rfl⟩
    filter_upwards [hopen.mem_nhds hmem] with z hz
    obtain ⟨τ, hτ, rfl⟩ := hz
    simp only [hG, Function.comp_apply, Pi.zero_apply, UpperHalfPlane.ofComplex_apply]
    exact hf τ hτ
  have hzero := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero hpre hz₀ hev
  ext τ
  have := hzero τ.im_pos
  simpa [hG] using this

/--
@isnad1 id=eq.0h3v.s8.3a2c00e120ec from=translated src=- shape=25930019 vocab=8e0a61f8
-/
theorem petersson_self_eq_integral [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f f = ((∫ τ in 𝒟, selfDensity f τ : ℝ) : ℂ) := by
  rw [CuspForm.petersson_def, ← integral_complex_ofReal]
  exact integral_congr_ae (Eventually.of_forall fun τ => integrand_self_eq f τ)

section fin
variable [NeZero N]

scoped instance : Finite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
  Subgroup.finite_quotient_of_finiteIndex

/--
@isnad1 id=continuo.0h4v.s8.e5c63b78f98c from=translated src=- shape=0ced7056 vocab=67088e24
-/
theorem continuous_integrand (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    Continuous (CuspForm.peterssonIntegrand f g) := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  have : CuspForm.peterssonIntegrand f g = fun τ => ∑ q, summand f g q τ :=
    funext (integrand_eq_sum f g)
  rw [this]
  refine continuous_finsetSum _ fun q _ => ?_
  exact UpperHalfPlane.petersson_continuous k (continuous_tr f _) (continuous_tr g _)

/--
@isnad1 id=ex.0h4v.s8.72c708d3f074 from=translated src=- shape=0a49eb34 vocab=ff8aad7e
-/
theorem integrand_bounded (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ∃ C, ∀ τ, ‖CuspForm.peterssonIntegrand f g τ‖ ≤ C := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) f g
  refine ⟨∑ _q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, C, fun τ => ?_⟩
  rw [integrand_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  unfold summand
  rw [petersson_tr]
  exact hC _

/--
@isnad1 id=integrab.0h4v.s8.e67a332d238d from=translated src=- shape=0836fcd4 vocab=efeb5c72
-/
theorem integrableOn_integrand (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    IntegrableOn (CuspForm.peterssonIntegrand f g) 𝒟 volume := by
  obtain ⟨C, hC⟩ := integrand_bounded f g
  refine Measure.integrableOn_of_bounded (M := C)
    FLT.FundamentalDomainVolume.volume_fd_lt_top.ne
    (continuous_integrand f g).aestronglyMeasurable ?_
  exact Eventually.of_forall hC

/--
@isnad1 id=integrab.0h3v.s8.901c01fd2d84 from=translated src=- shape=50df7ef1 vocab=5cfb2180
-/
theorem integrableOn_selfDensity [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) : IntegrableOn (selfDensity f) 𝒟 volume := by
  refine IntegrableOn.congr_fun (integrableOn_integrand f f).re (fun τ _ => ?_)
    ModularGroup.isClosed_fd.measurableSet
  show RCLike.re (CuspForm.peterssonIntegrand f f τ) = selfDensity f τ
  rw [integrand_self_eq]
  simp

/--
@isnad1 id=iff.0h3v.s9.809ae341b6ad from=translated src=- shape=542ba854 vocab=e6121d7b
-/
theorem petersson_self_eq_zero_iff' (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f f = 0 ↔ f = 0 := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  constructor
  · intro h
    rw [petersson_self_eq_integral, Complex.ofReal_eq_zero] at h
    have hint := integrableOn_selfDensity f
    rw [integral_eq_zero_iff_of_nonneg_ae] at h
    rotate_left
    · exact (ae_restrict_iff' ModularGroup.isClosed_fd.measurableSet).mpr
        (Eventually.of_forall fun τ _ => selfDensity_nonneg f τ)
    · exact hint

    have hfdo : ∀ τ ∈ ModularGroup.fdo, selfDensity f τ = 0 := by
      by_contra hcon
      push Not at hcon
      obtain ⟨τ₀, hτ₀, hne⟩ := hcon
      set U := ModularGroup.fdo ∩ (selfDensity f) ⁻¹' {x | x ≠ 0} with hUdef
      have hUopen : IsOpen U := ModularGroup.isOpen_fdo.inter
        ((continuous_selfDensity f).isOpen_preimage _ isOpen_ne)
      have hUpos : 0 < volume U := hUopen.measure_pos volume ⟨τ₀, hτ₀, hne⟩
      have hae : ∀ᵐ τ ∂(volume : Measure ℍ), τ ∈ 𝒟 → selfDensity f τ = 0 :=
        (ae_restrict_iff' ModularGroup.isClosed_fd.measurableSet).mp h
      have hUnull : volume U = 0 := by
        refine measure_eq_zero_iff_ae_notMem.mpr ?_
        filter_upwards [hae] with τ hτ hτU
        exact hτU.2 (hτ (ModularGroup.fdo_subset_fd hτU.1))
      exact hUpos.ne' hUnull

    have hf0 : ∀ τ ∈ ModularGroup.fdo, f τ = 0 := by
      intro τ hτ
      have hsum := hfdo τ hτ
      unfold selfDensity at hsum
      have hterm := (Finset.sum_eq_zero_iff_of_nonneg fun q _ =>
        mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le _)).mp hsum
        (QuotientGroup.mk 1) (Finset.mem_univ _)
      have hpos : 0 < τ.im ^ k := zpow_pos τ.im_pos k
      have h1 : ‖tr f (QuotientGroup.mk (1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out τ‖ ^ 2 = 0 := by
        rcases mul_eq_zero.mp hterm with h | h
        · exact h
        · exact absurd h hpos.ne'
      have h2 : tr f (QuotientGroup.mk (1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N).out τ = 0 := by
        simpa using h1

      obtain ⟨γ, hγ⟩ := QuotientGroup.mk_out_eq_mul (CongruenceSubgroup.Gamma0 N) (1 : SL(2, ℤ))
      rw [hγ, tr_mul_of_mem f 1 γ γ.2, tr_one] at h2
      exact h2
    exact eq_zero_of_eqOn_fdo f hf0
  · rintro rfl
    rw [petersson_self_eq_integral]
    have : selfDensity (0 : CuspForm (CongruenceSubgroup.Gamma0 N) k) = fun _ => 0 := by
      funext τ; simp [selfDensity, tr, SlashAction.zero_slash]
    simp [this]

end fin

end AlliAux1Pet
open scoped _root_.P2MW.S_CuspForm_petersson_self_eq_zero_iff.AlliAux1Pet
/--
@isnad1 id=iff.0h3v.s9.809ae341b6ad from=translated src=- shape=542ba854 vocab=e6121d7b
-/
theorem solution {N : ℕ} {k : ℤ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f f = 0 ↔ f = 0 :=
  AlliAux1Pet.petersson_self_eq_zero_iff' f

end
open scoped _root_.P2MW.S_CuspForm_petersson_self_eq_zero_iff.AlliAux1Pet
