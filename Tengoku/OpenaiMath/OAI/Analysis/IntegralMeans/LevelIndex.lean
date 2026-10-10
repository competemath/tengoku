import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.Turning

namespace OAI

noncomputable section
open Set MeasureTheory Filter Function InnerProductSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open MeasureTheory Function
open Set Filter
open Set MeasureTheory Filter Function
open Set MeasureTheory Filter Function InnerProductSpace
open TopologicalSpace
open scoped CompactlySupported
open scoped ENNReal
open scoped Manifold
open scoped Topology CompactlySupported ComplexConjugate
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical
open scoped Topology ENNReal NNReal
namespace Brennan

lemma windingNumber_normal_field {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hd : ∀ t, deriv γ t ≠ 0)
    (hm : ∀ t, (γ 0).re ≤ (γ t).re)
    (hr : (deriv γ 0).re = 0) (hi : (deriv γ 0).im < 0)
    (X : C(ℂ,ℂ)) (hX : ∀ t, X (γ t) ≠ 0)
    (horth : ∀ t, (X (γ t)*(conj (deriv γ t))).re = 0) :
    windingNumber (X.comp (periodicLoop hγ.continuous 0)) = 1 := by
  let T : C(unitInterval,ℂ) := ⟨fun t => deriv γ t,
    (hγ.continuous_deriv (by simp)).comp continuous_subtype_val⟩
  let R : C(unitInterval,ℂ) := ⟨fun t => X (γ t)/deriv γ t, by
    apply Continuous.div
    · exact X.continuous.comp (hγ.continuous.comp continuous_subtype_val)
    · exact T.continuous
    · exact fun t => hd t⟩
  have hTloop : T 1 = T 0 := (periodic_deriv hp).eq
  have hRloop : R 1 = R 0 := by
    change X (γ 1)/deriv γ 1 = X (γ 0)/deriv γ 0
    rw [hp.eq,(periodic_deriv hp).eq]
  have hRn (t) : R t ≠ 0 := div_ne_zero (hX t) (hd t)
  have hRslit (t) : R t ∈ Complex.slitPlane := by
    apply Or.inr
    have hre : (R t).re = 0 := by
      change (X (γ t)/deriv γ t).re = 0
      rw [Complex.div_re,← add_div]
      have hh := horth t
      simp only [Complex.mul_re,Complex.conj_re,Complex.conj_im,mul_neg,sub_neg_eq_add] at hh
      rw [hh,zero_div]
    intro him
    exact hRn t (Complex.ext hre him)
  have hwindR : windingNumber R = 0 := by
    apply windingNumber_eq_of_logIncrement hRloop
    simpa only [hRloop,sub_self,Int.cast_zero,zero_mul] using HasLogIncrement.of_slit R hRslit
  have hwindT : windingNumber T = 1 := by
    apply windingNumber_eq_of_logIncrement hTloop
    obtain ⟨A,hA,hinc⟩ := tangent_turning_log hγ hp hinj (fun t _ => hd t)
      (fun t _ => hm t) hr hi
    refine ⟨A,hA,?_⟩
    rw [hinc,add_sub_cancel_left]
    simp only [Int.cast_one,one_mul]
    push_cast
    ring
  have he : X.comp (periodicLoop hγ.continuous 0) = T*R := by
    ext t
    change X (γ ((t:ℝ)+0)) = deriv γ t*(X (γ t)/deriv γ t)
    rw [add_zero,mul_div_cancel₀ _ (hd t)]
  rw [he,windingNumber_mul T R hTloop hRloop (fun t => hd t) hRn,hwindT,hwindR,add_zero]

lemma periodic_simple_eq_of_near {γ : ℝ → ℂ} (hp : Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {a b : ℝ}
    (he : γ a = γ b) (hab : |a-b| < 1) : a = b := by
  have hh (t : ℝ) : γ (Int.fract t) = γ t := by
    simpa only [Int.fract,mul_one] using hp.sub_int_mul_eq (x := t) ⌊t⌋
  have hfr : Int.fract a = Int.fract b := hinj
    ⟨Int.fract_nonneg a,Int.fract_lt_one a⟩ ⟨Int.fract_nonneg b,Int.fract_lt_one b⟩
    ((hh a).trans (he.trans (hh b).symm))
  obtain ⟨n,hn⟩ := Int.fract_eq_fract.mp hfr
  rw [hn] at hab
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast (abs_lt.mp hab).1
  have hnhi : n < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hab).2
  have hn0 : n = 0 := by omega
  rw [hn0,Int.cast_zero] at hn
  exact sub_eq_zero.mp hn

lemma periodic_simple_shift {γ : ℝ → ℂ} (hp : Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (s : ℝ) :
    InjOn (fun t => γ (t+s)) (Ico (0 : ℝ) 1) := by
  intro a ha b hb he
  have hh : |(a+s)-(b+s)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  have heq := periodic_simple_eq_of_near hp hinj he hh
  linarith

lemma periodic_simple_reverse {γ : ℝ → ℂ} (hp : Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) :
    InjOn (fun t => γ (-t)) (Ico (0 : ℝ) 1) := by
  intro a ha b hb he
  have hh : |(-a)-(-b)| < 1 := by
    rw [abs_lt]
    constructor <;> linarith [ha.1,ha.2,hb.1,hb.2]
  have heq := periodic_simple_eq_of_near hp hinj he hh
  linarith

lemma orient_unit_curve {γ : ℝ → ℂ} (hc : ContDiff ℝ 1 γ)
    (hp : Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hd : ∀ t, deriv γ t ≠ 0) :
    ∃ η : ℝ → ℂ, range η = range γ ∧ ContDiff ℝ 1 η ∧
      Periodic η 1 ∧ InjOn η (Ico (0 : ℝ) 1) ∧ (∀ t, deriv η t ≠ 0) ∧
      (∀ t, (η 0).re ≤ (η t).re) ∧ (deriv η 0).re = 0 ∧ (deriv η 0).im < 0 := by
  have hk : IsCompact (range γ) := by
    rw [← periodicLoop_range hc.continuous hp 0]
    exact isCompact_range (periodicLoop hc.continuous 0).continuous
  obtain ⟨z,⟨s,hs⟩,hmin⟩ := hk.exists_isMinOn ⟨γ 0,⟨0,rfl⟩⟩
    Complex.continuous_re.continuousOn
  subst z
  let η : ℝ → ℂ := fun t => γ (t+s)
  have hηr : range η = range γ := by
    apply Subset.antisymm
    · rintro _ ⟨t,rfl⟩; exact ⟨t+s,rfl⟩
    · rintro _ ⟨t,rfl⟩; exact ⟨t-s,by simp only [η,sub_add_cancel]⟩
  have hηc : ContDiff ℝ 1 η := hc.comp (contDiff_id.add contDiff_const)
  have hηp : Periodic η 1 := hp.add_const s
  have hηinj : InjOn η (Ico (0 : ℝ) 1) := periodic_simple_shift hp hinj s
  have hηd (t) : deriv η t ≠ 0 := by
    dsimp only [η]
    rw [deriv_comp_add_const]
    exact hd (t+s)
  have hηmin (t) : (η 0).re ≤ (η t).re := by
    simpa only [η,zero_add] using
      (show (γ s).re ≤ (γ (t+s)).re from hmin ⟨t+s,rfl⟩)
  have hlocal : IsLocalMin (fun t => (η t).re) 0 :=
    Filter.Eventually.of_forall hηmin
  have hηre : (deriv η 0).re = 0 := hlocal.hasDerivAt_eq_zero
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0
      ((hηc.differentiable (by simp)) 0).hasDerivAt)
  by_cases hi : (deriv η 0).im < 0
  · exact ⟨η,hηr,hηc,hηp,hηinj,hηd,hηmin,hηre,hi⟩
  · have him : 0 < (deriv η 0).im := lt_of_le_of_ne (not_lt.mp hi) (by
      intro he
      exact hηd 0 (Complex.ext hηre he.symm))
    let κ : ℝ → ℂ := fun t => η (-t)
    have hκr : range κ = range η := by
      apply Subset.antisymm
      · rintro _ ⟨t,rfl⟩; exact ⟨-t,rfl⟩
      · rintro _ ⟨t,rfl⟩; exact ⟨-t,by simp [κ]⟩
    refine ⟨κ,hκr.trans hηr,hηc.comp contDiff_id.neg,?_,
      periodic_simple_reverse hηp hηinj,?_,?_,?_,?_⟩
    · intro t
      change η (-(t+1)) = η (-t)
      rw [show -(t+1) = -t-1 by ring,hηp.sub_eq]
    · intro t
      dsimp only [κ]
      rw [deriv_comp_neg]
      exact neg_ne_zero.mpr (hηd (-t))
    · intro t
      simpa only [κ,neg_zero] using hηmin (-t)
    · dsimp only [κ]
      rw [deriv_comp_neg,neg_zero,Complex.neg_re,hηre,neg_zero]
    · dsimp only [κ]
      rw [deriv_comp_neg,neg_zero,Complex.neg_im]
      exact neg_neg_of_pos him

lemma orient_periodic_curve {γ : ℝ → ℂ} {P : ℝ} (hP : 0 < P)
    (hc : ContDiff ℝ 1 γ) (hp : Periodic γ P) (hinj : InjOn γ (Ico (0 : ℝ) P))
    (hd : ∀ t, deriv γ t ≠ 0) :
    ∃ η : ℝ → ℂ, range η = range γ ∧ ContDiff ℝ 1 η ∧
      Periodic η 1 ∧ InjOn η (Ico (0 : ℝ) 1) ∧ (∀ t, deriv η t ≠ 0) ∧
      (∀ t, (η 0).re ≤ (η t).re) ∧ (deriv η 0).re = 0 ∧ (deriv η 0).im < 0 := by
  let κ : ℝ → ℂ := fun t => γ (P*t)
  have hκr : range κ = range γ := by
    apply Subset.antisymm
    · rintro _ ⟨t,rfl⟩; exact ⟨P*t,rfl⟩
    · rintro _ ⟨t,rfl⟩; exact ⟨t/P,by simp [κ,mul_div_cancel₀ _ hP.ne']⟩
  have hκc : ContDiff ℝ 1 κ := hc.comp (contDiff_const.mul contDiff_id)
  have hκp : Periodic κ 1 := by
    intro t
    change γ (P*(t+1)) = γ (P*t)
    rw [mul_add,mul_one,hp]
  have hκinj : InjOn κ (Ico (0 : ℝ) 1) := by
    intro a ha b hb he
    have heq := hinj ⟨mul_nonneg hP.le ha.1,by nlinarith [ha.2]⟩
      ⟨mul_nonneg hP.le hb.1,by nlinarith [hb.2]⟩ he
    exact (mul_left_cancel₀ hP.ne') heq
  have hκd (t) : deriv κ t ≠ 0 := by
    dsimp only [κ]
    rw [deriv_comp_mul_left]
    exact smul_ne_zero hP.ne' (hd (P*t))
  obtain ⟨η,hηr,hh⟩ := orient_unit_curve hκc hκp hκinj hκd
  exact ⟨η,hηr.trans hκr,hh⟩

def tangentGradient (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  (-(fderiv ℝ f z Complex.I) : ℂ) + Complex.I*(fderiv ℝ f z 1 : ℂ)

lemma tangentGradient_orthogonal (f : ℂ → ℝ) (z : ℂ) :
    fderiv ℝ f z (tangentGradient f z) = 0 := by
  rw [realFunctional_decomposition]
  simp only [tangentGradient,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im]
  ring

lemma tangentGradient_ne_zero {f : ℂ → ℝ} {z : ℂ} (h : fderiv ℝ f z ≠ 0) :
    tangentGradient f z ≠ 0 := by
  intro he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [tangentGradient,Complex.add_re,Complex.add_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.neg_re,Complex.neg_im,Complex.mul_re,Complex.mul_im,
    Complex.I_re,Complex.I_im,Complex.zero_re,Complex.zero_im] at hre him
  apply h
  ext w
  rw [realFunctional_decomposition]
  simp only [zero_mul,one_mul,sub_zero,neg_zero,zero_add,add_zero,neg_eq_zero] at hre him
  simp only [him,hre,mul_zero,add_zero,zero_apply]

lemma tangentGradient_contDiff {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (tangentGradient f) := by
  have hd := hf.fderiv_right (show (1 : WithTop ℕ∞)+1 ≤ 2 by norm_num)
  exact ((Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)).neg).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)))

lemma tangentGradient_hasCompactSupport {f : ℂ → ℝ} {d : ℝ}
    (hs : HasCompactSupport (fun z => f z-d)) : HasCompactSupport (tangentGradient f) := by
  have hD := hs.fderiv ℝ
  apply hD.mono'
  intro z hz
  by_contra hn
  have hzer : fderiv ℝ (fun z => f z-d) z = 0 := notMem_support.mp
    (fun h => hn (subset_tsupport _ h))
  have hfzero : fderiv ℝ f z = 0 := by simpa only [fderiv_sub_const] using hzer
  exact hz (by simp only [tangentGradient,hfzero,zero_apply,
    Complex.ofReal_zero,neg_zero,mul_zero,add_zero])

lemma compact_regular_level_oriented_curves {f : ℂ → ℝ} {c d : ℝ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport (fun z => f z-d))
    (hreg : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hK : IsCompact {z | f z = c}) :
    ∃ C : Finset (Set ℂ), (⋃ S ∈ C, S) = {z | f z = c} ∧
      (∀ S ∈ C, ∀ T ∈ C, S ≠ T → Disjoint S T) ∧
      ∀ S ∈ C, ∃ γ : ℝ → ℂ, range γ = S ∧ ContDiff ℝ 1 γ ∧
        Periodic γ 1 ∧ InjOn γ (Ico (0 : ℝ) 1) ∧ (∀ t, deriv γ t ≠ 0) ∧
        (∀ t, (γ 0).re ≤ (γ t).re) ∧ (deriv γ 0).re = 0 ∧ (deriv γ 0).im < 0 := by
  obtain ⟨C,hC,hdis,hcurves⟩ := compact_regular_level_finite_curves
    (hf.of_le (by norm_num)) (tangentGradient_contDiff hf) (tangentGradient_hasCompactSupport hs)
    (tangentGradient_orthogonal f) hreg (fun z hz => tangentGradient_ne_zero (hreg z hz)) hK
  refine ⟨C,hC,hdis,?_⟩
  intro S hS
  obtain ⟨γ,P,hP,hrange,hD,hper,hinj⟩ := hcurves S hS
  have hlevel (t) : f (γ t) = c := by
    have hm : γ t ∈ ⋃ S ∈ C, S := mem_iUnion₂.mpr ⟨S,hS,hrange ▸ mem_range_self t⟩
    rwa [hC] at hm
  obtain ⟨η,hηrange,hη⟩ := orient_periodic_curve hP
    (integral_curve_contDiff_one (tangentGradient_contDiff hf).continuous hD)
    hper hinj (fun t => by rw [(hD t).deriv]; exact tangentGradient_ne_zero (hreg _ (hlevel t)))
  exact ⟨η,hηrange.trans hrange,hη⟩

lemma loopIndex_zero_of_im_lt (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : ∀ t, a.im < (γ t).im) : loopIndex γ a = 0 := by
  have hslit (t) : γ t-a ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    exact ne_of_gt (sub_pos.mpr (ha t))
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  refine ⟨⟨fun t => Complex.log (γ t-a), ?_⟩, ?_, ?_⟩
  · exact Continuous.clog (by fun_prop) hslit
  · intro t
    exact Complex.exp_log (Complex.slitPlane_ne_zero (hslit t))
  · simp [hloop]

lemma closure_windingInterior_subset_halfPlane (γ : C(unitInterval, ℂ))
    (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ halfPlane) :
    closure (windingInterior γ) ⊆ halfPlane := by
  obtain ⟨d,hd,hdist⟩ := isCompact_univ.exists_forall_le'
    (show ContinuousOn (fun t : unitInterval => (γ t).im) univ by fun_prop)
    (a := 0) (fun t _ => hγ t)
  have hsub : windingInterior γ ⊆ {a : ℂ | d ≤ a.im} := by
    intro a ha
    by_contra hn
    exact ha.2 (loopIndex_zero_of_im_lt γ hloop
      (fun t => (lt_of_not_ge hn).trans_le (hdist t (mem_univ t))))
  have hc := closure_minimal hsub (isClosed_le continuous_const Complex.continuous_im)
  intro a ha
  exact hd.trans_le (hc ha)

lemma reciprocalPotential_lt_on_windingInterior {f : ℂ → ℂ}
    (hf : UnivalentOn f halfPlane) {k b : ℝ} (hk : 0 < k) (hb : 0 < b) (ξ : ℂ)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ halfPlane)
    (hlevel : ∀ t, reciprocalPotential f k ξ (γ t) = b)
    {z : ℂ} (hz : z ∈ windingInterior γ) : reciprocalPotential f k ξ z < b := by
  apply reciprocalPotential_lt_boundary hf hk hb ξ (isOpen_windingInterior γ hloop)
    ((isBounded_windingInterior γ hloop).isCompact_closure)
    (closure_windingInterior_subset_halfPlane γ hloop hγ) _ hz
  intro w hw
  obtain ⟨t,rfl⟩ := frontier_windingInterior_subset γ hloop hw
  exact (hlevel t).le

lemma extend_compact_sublevel {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : ∀ z ∈ U, ContDiffAt ℝ 2 f z) {d : ℝ}
    (hK : IsCompact {z | z ∈ U ∧ f z ≤ d}) :
    ∃ F : ℂ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport (fun z => F z-d) ∧
      (∀ z, z ∈ U → f z ≤ d → F =ᶠ[𝓝 z] f) ∧
      (∀ z ∉ U, F z = d) ∧
      (∀ z c, c < d → (F z ≤ c ↔ z ∈ U ∧ f z ≤ c)) ∧
      (∀ z c, c < d → (F z < c ↔ z ∈ U ∧ f z < c)) := by
  obtain ⟨χ,hχc,hχK,hχU,hχ1,hχrange⟩ := exists_smooth_cutoff hK hU
    (fun _ h => h.1)
  let F := fun z => χ z*(f z-d)+d
  have heq (z) (hz : z ∈ U) (hzd : f z ≤ d) : F =ᶠ[𝓝 z] f := by
    filter_upwards [hχ1 z ⟨hz,hzd⟩] with w hw
    simp only [F,hw,one_mul,sub_add_cancel]
  have hzero (z) (hz : z ∉ tsupport χ) : F =ᶠ[𝓝 z] fun _ => d := by
    filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
    have hh : χ w = 0 := notMem_support.mp (fun h => hw (subset_tsupport χ h))
    simp only [F,hh,zero_mul,zero_add]
  have hFc : ContDiff ℝ 2 F := by
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact ((hχc.contDiffAt.mul ((hf z (hχU hz)).sub contDiffAt_const)).add
        contDiffAt_const)
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero z hz)
  have hFK : HasCompactSupport (fun z => F z-d) := by
    apply hχK.mono'
    intro z hz
    by_contra hn
    have hh := (hzero z hn).self_of_nhds
    exact hz (sub_eq_zero.mpr hh)
  have hFd (z) (hz : z ∉ U) : F z = d :=
    (hzero z (fun h => hz (hχU h))).self_of_nhds
  have hlarge (z) (hz : z ∈ U) (hdz : d ≤ f z) : d ≤ F z := by
    dsimp only [F]
    exact le_add_of_nonneg_left (mul_nonneg (hχrange z).1 (sub_nonneg.mpr hdz))
  refine ⟨F,hFc,hFK,heq,hFd,?_,?_⟩
  · intro z c hc
    constructor
    · intro hz
      have hzU : z ∈ U := by
        by_contra hn
        rw [hFd z hn] at hz
        exact hc.not_ge hz
      have hzd : f z ≤ d := by
        by_contra hn
        exact hc.not_ge ((hlarge z hzU (not_le.mp hn).le).trans hz)
      exact ⟨hzU,(heq z hzU hzd).self_of_nhds ▸ hz⟩
    · rintro ⟨hzU,hz⟩
      rwa [(heq z hzU (hz.trans hc.le)).self_of_nhds]
  · intro z c hc
    constructor
    · intro hz
      have hzU : z ∈ U := by
        by_contra hn
        rw [hFd z hn] at hz
        exact hc.not_gt hz
      have hzd : f z ≤ d := by
        by_contra hn
        exact hc.not_gt ((hlarge z hzU (not_le.mp hn).le).trans_lt hz)
      exact ⟨hzU,(heq z hzU hzd).self_of_nhds ▸ hz⟩
    · rintro ⟨hzU,hz⟩
      rwa [(heq z hzU (hz.le.trans hc.le)).self_of_nhds]

end Brennan

end

end OAI
