import Tengoku.OpenaiMath.OAI.Analysis.IntegralMeans.CriticalPoint

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

lemma HasLogIncrement.path_trans {a b c : ℂ} {γ : Path a b} {η : Path b c}
    {p q : ℂ} (hγ : HasLogIncrement γ.toContinuousMap p)
    (hη : HasLogIncrement η.toContinuousMap q) :
    HasLogIncrement (γ.trans η).toContinuousMap (p+q) := by
  obtain ⟨A,hA,hp⟩ := hγ
  obtain ⟨B,hB,hq⟩ := hη
  let α : Path (A 0) (A 1) := ⟨A,rfl,rfl⟩
  let β : Path (A 1) (B 1+A 1-B 0) :=
    ⟨⟨fun t => B t+A 1-B 0, by fun_prop⟩, by simp, rfl⟩
  refine ⟨(α.trans β).toContinuousMap, ?_, ?_⟩
  · intro t
    change Complex.exp ((α.trans β) t) = (γ.trans η) t
    rw [Path.trans_apply,Path.trans_apply]
    split_ifs with h
    · exact hA _
    · dsimp only [β,ContinuousMap.coe_mk,Path.coe_mk_mk]
      have heA : Complex.exp (A 1) = b := (hA 1).trans γ.target
      have heB : Complex.exp (B 0) = b := (hB 0).trans η.source
      have hb : b ≠ 0 := heB ▸ Complex.exp_ne_zero (B 0)
      rw [Complex.exp_sub,Complex.exp_add,heA,heB,hB]
      exact mul_div_cancel_right₀ _ hb
  · change (α.trans β) 1-(α.trans β) 0=p+q
    simp only [Path.target,Path.source]
    linear_combination hp+hq

lemma HasLogIncrement.path_symm {a b : ℂ} {γ : Path a b} {q : ℂ}
    (hγ : HasLogIncrement γ.toContinuousMap q) :
    HasLogIncrement γ.symm.toContinuousMap (-q) := by
  obtain ⟨A,hA,hq⟩ := hγ
  refine ⟨⟨fun t => A (unitInterval.symm t), by fun_prop⟩, ?_, ?_⟩
  · exact fun t => hA (unitInterval.symm t)
  · simp only [ContinuousMap.coe_mk,unitInterval.symm_one,unitInterval.symm_zero]
    linear_combination -hq

lemma exists_path_logIncrement {a b : ℂ} (γ : Path a b) (hn : ∀ t, γ t ≠ 0) :
    ∃ q, HasLogIncrement γ.toContinuousMap q := by
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0,by simp⟩)
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locallyPathConnectedSpace
  obtain ⟨A,hA⟩ := exists_log_lift_of_simplyConnected (0 : unitInterval) γ.toContinuousMap hn
  exact ⟨A 1-A 0,A,hA,rfl⟩

lemma HasLogIncrement.of_slit (γ : C(unitInterval,ℂ))
    (hγ : ∀ t, γ t ∈ Complex.slitPlane) :
    HasLogIncrement γ (Complex.log (γ 1)-Complex.log (γ 0)) := by
  exact ⟨⟨fun t => Complex.log (γ t),γ.continuous.clog hγ⟩,
    fun t => Complex.exp_log (Complex.slitPlane_ne_zero (hγ t)),rfl⟩

lemma HasLogIncrement.of_neg_slit (γ : C(unitInterval,ℂ))
    (hγ : ∀ t, -γ t ∈ Complex.slitPlane) :
    HasLogIncrement γ (Complex.log (-γ 1)-Complex.log (-γ 0)) := by
  refine ⟨⟨fun t => Complex.log (-γ t)+(Real.pi : ℂ)*Complex.I,
    ((γ.continuous.neg).clog hγ).add continuous_const⟩,?_,?_⟩
  · intro t
    simp only [ContinuousMap.coe_mk,Complex.exp_add,Complex.exp_pi_mul_I]
    rw [Complex.exp_log (Complex.slitPlane_ne_zero (hγ t))]
    ring
  · dsimp only [ContinuousMap.coe_mk]
    ring

lemma log_neg_of_im_neg {z : ℂ} (hi : z.im < 0) :
    Complex.log (-z) = Complex.log z+(Real.pi : ℂ)*Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re,norm_neg]
  · simpa [Complex.log_im] using Complex.arg_neg_eq_arg_add_pi_of_im_neg hi

lemma log_neg_of_im_pos {z : ℂ} (hi : 0 < z.im) :
    Complex.log (-z) = Complex.log z-(Real.pi : ℂ)*Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re,norm_neg]
  · simpa [Complex.log_im] using Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi

def rectPath (r h : ℝ) : Path ((-r : ℂ)-(h : ℂ)*Complex.I)
    ((-r : ℂ)-(h : ℂ)*Complex.I) :=
  (((Path.segment ((-r : ℂ)-(h : ℂ)*Complex.I) ((r : ℂ)-(h : ℂ)*Complex.I)).trans
    (Path.segment ((r : ℂ)-(h : ℂ)*Complex.I) ((r : ℂ)+(h : ℂ)*Complex.I))).trans
    (Path.segment ((r : ℂ)+(h : ℂ)*Complex.I) ((-r : ℂ)+(h : ℂ)*Complex.I))).trans
    (Path.segment ((-r : ℂ)+(h : ℂ)*Complex.I) ((-r : ℂ)-(h : ℂ)*Complex.I))

lemma rectPath_logIncrement {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    HasLogIncrement (rectPath r h).toContinuousMap (2*Real.pi*Complex.I) := by
  let a : ℂ := (-r : ℂ)-(h : ℂ)*Complex.I
  let b : ℂ := (r : ℂ)-(h : ℂ)*Complex.I
  let c : ℂ := (r : ℂ)+(h : ℂ)*Complex.I
  let d : ℂ := (-r : ℂ)+(h : ℂ)*Complex.I
  have hab (t : unitInterval) : (Path.segment a b) t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,a,b,Complex.add_im,
      Complex.sub_im,Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.neg_im]
    nlinarith
  have hbc (t : unitInterval) : (Path.segment b c) t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,b,c,Complex.add_re,
      Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im]
    nlinarith
  have hcd (t : unitInterval) : (Path.segment c d) t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    right
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,c,d,Complex.add_im,
      Complex.real_smul,Complex.mul_im,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.neg_im]
    nlinarith
  have hda (t : unitInterval) : -(Path.segment d a) t ∈ Complex.slitPlane := by
    apply Complex.mem_slitPlane_iff.mpr
    left
    simp only [Path.segment_apply,AffineMap.lineMap_apply_module,d,a,Complex.add_re,
      Complex.sub_re,Complex.real_smul,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,Complex.I_re,Complex.I_im,Complex.neg_re]
    nlinarith
  have h₁ := HasLogIncrement.of_slit (Path.segment a b).toContinuousMap hab
  have h₂ := HasLogIncrement.of_slit (Path.segment b c).toContinuousMap hbc
  have h₃ := HasLogIncrement.of_slit (Path.segment c d).toContinuousMap hcd
  have h₄ := HasLogIncrement.of_neg_slit (Path.segment d a).toContinuousMap hda
  have he := ((h₁.path_trans h₂).path_trans h₃).path_trans h₄
  have ha : a.im < 0 := by simpa [a] using hh
  have hd : 0 < d.im := by simpa [d] using hh
  have hla := log_neg_of_im_neg ha
  have hld := log_neg_of_im_pos hd
  convert he using 1
  · rfl
  · simp only [Path.coe_toContinuousMap,Path.target,Path.source]
    rw [hla,hld]
    ring

lemma rectPath_winding {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    windingNumber (rectPath r h).toContinuousMap = 1 := by
  apply windingNumber_eq_of_logIncrement ((rectPath r h).target.trans (rectPath r h).source.symm)
  simpa only [Int.cast_one,one_mul] using rectPath_logIncrement hr hh

lemma windingNumber_path_symm {a b : ℂ} (γ : Path a b)
    (hc : γ 1 = γ 0) (hn : ∀ t, γ t ≠ 0) :
    windingNumber γ.symm.toContinuousMap = -windingNumber γ.toContinuousMap := by
  apply windingNumber_eq_of_logIncrement (by simpa using hc.symm)
  convert (windingNumber_spec γ.toContinuousMap hc hn).path_symm using 1
  push_cast
  ring

lemma windingNumber_four_paths {a b c d : ℂ}
    (α : Path a b) (β : Path b c) (χ : Path c d) (δ : Path d a)
    (hβc : β 1 = β 0) (hδc : δ 1 = δ 0)
    (hχ : χ.toContinuousMap = α.symm.toContinuousMap)
    (hα : ∀ t, α t ≠ 0) (hβ : ∀ t, β t ≠ 0) (hδ : ∀ t, δ t ≠ 0) :
    windingNumber (((α.trans β).trans χ).trans δ).toContinuousMap =
      windingNumber β.toContinuousMap + windingNumber δ.toContinuousMap := by
  obtain ⟨p,hp⟩ := exists_path_logIncrement α hα
  have hq := windingNumber_spec β.toContinuousMap hβc hβ
  have hr := windingNumber_spec δ.toContinuousMap hδc hδ
  have hs : HasLogIncrement χ.toContinuousMap (-p) := hχ ▸ hp.path_symm
  apply windingNumber_eq_of_logIncrement
    ((((α.trans β).trans χ).trans δ).target.trans
      (((α.trans β).trans χ).trans δ).source.symm)
  convert ((hp.path_trans hq).path_trans hs).path_trans hr using 1
  push_cast
  ring

lemma transverse_hasFDerivAt {γ : ℝ → ℂ} {d : ℂ} (hd : HasDerivAt γ d 0) :
    HasFDerivAt (fun w : ℂ => γ w.im-γ 0-w.re • (Complex.I*d))
      ((-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ) 0 := by
  have h := ((hd.hasFDerivAt.comp (0 : ℂ) (Complex.imCLM.hasFDerivAt)).sub_const
    (γ 0)).sub (Complex.reCLM.hasFDerivAt.smul_const (Complex.I*d))
  have he : ContinuousLinearMap.toSpanSingleton ℝ d ∘L Complex.imCLM -
      Complex.reCLM.smulRight (Complex.I*d) =
      (-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ := by
    ext z
    apply Complex.ext <;> simp [Complex.real_smul] <;> ring
  rw [he] at h
  exact h

lemma det_transverse_pos {d : ℂ} (hd : d ≠ 0) :
    0 < LinearMap.det (((-Complex.I*d) • ContinuousLinearMap.id ℝ ℂ).toLinearMap) := by
  rw [det_complex_smul]
  simp only [ContinuousLinearMap.coe_id,LinearMap.det_id,mul_one]
  exact sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hd))

lemma periodic_simple_zero {γ : ℝ → ℂ} (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {t : ℝ} (ht : t ∈ Icc (-(1/2 : ℝ)) (1/2))
    (he : γ t = γ 0) : t = 0 := by
  by_cases hn : 0 ≤ t
  · exact hinj ⟨hn,by linarith [ht.2]⟩ ⟨le_rfl,by norm_num⟩ he
  · have hne : t+1 = 0 := hinj ⟨by linarith [ht.1],by linarith⟩
      ⟨le_rfl,by norm_num⟩ ((hp t).trans he)
    linarith [ht.1]

lemma transverse_unique_zero_strip {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdn : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, |w.re| ≤ δ → |w.im| ≤ 1/2 →
      (γ w.im-γ 0-w.re • (Complex.I*d) = 0 ↔ w = 0) := by
  let H : ℂ → ℂ := fun w => γ w.im-γ 0-w.re • (Complex.I*d)
  have hH0 : H 0 = 0 := by simp [H]
  obtain ⟨_,r,hr,hlocal⟩ := exists_slit_radius_pos hH0 (transverse_hasFDerivAt hd)
    (det_transverse_pos hdn)
  let η := min (r/2) (1/4 : ℝ)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  let K : Set ℝ := Icc (-(1/2 : ℝ)) (1/2) ∩ {t | η ≤ |t|}
  have hK : IsCompact K := isCompact_Icc.inter_right
    (isClosed_le continuous_const continuous_abs)
  obtain ⟨m,hm,hbound⟩ := hK.exists_forall_le' ((hc.sub continuous_const).norm.continuousOn)
    (a := (0 : ℝ)) (fun t ht => norm_pos_iff.mpr (sub_ne_zero.mpr (by
      intro he
      have he0 := periodic_simple_zero hp hinj ht.1 he
      have hb : η ≤ |t| := ht.2
      simp only [he0,abs_zero] at hb
      exact (not_le.mpr hη) hb)))
  let δ := min (r/2) (m/(2*‖d‖))
  have hδ : 0 < δ := lt_min (by linarith) (div_pos hm (by positivity))
  refine ⟨δ,hδ,?_⟩
  intro w hre him
  constructor
  · intro hz
    by_contra hwn
    by_cases hi : |w.im| < η
    · have hn : ‖w-0‖ < 2*r := by
        simpa only [sub_zero] using calc
          ‖w‖ ≤ |w.re|+|w.im| := Complex.norm_le_abs_re_add_abs_im w
          _ < r/2+r/2 := by
            have hδr := min_le_left (r/2) (m/(2*‖d‖))
            have hηr := min_le_left (r/2) (1/4 : ℝ)
            dsimp only [δ] at hre
            dsimp only [η] at hi
            linarith
          _ < 2*r := by linarith
      have hnon := Complex.slitPlane_ne_zero (hlocal w hn hwn)
      apply hnon
      simp only [H,hz,zero_div]
    · have hb := hbound w.im ⟨abs_le.mp him,not_lt.mp hi⟩
      change m ≤ ‖γ w.im-γ 0‖ at hb
      have he : γ w.im-γ 0 = w.re • (Complex.I*d) := sub_eq_zero.mp hz
      have hnorm : ‖γ w.im-γ 0‖ = |w.re| *‖d‖ := by
        rw [he,norm_smul,Real.norm_eq_abs,norm_mul,Complex.norm_I,one_mul]
      have hδm : δ*‖d‖ ≤ m/2 := by
        have h := min_le_right (r/2) (m/(2*‖d‖))
        have hn := norm_pos_iff.mpr hdn
        dsimp only [δ]
        apply (le_div_iff₀ hn).mp
        convert h using 1; field_simp
      have : |w.re| *‖d‖ ≤ m/2 := (mul_le_mul_of_nonneg_right hre (norm_nonneg d)).trans hδm
      linarith
  · rintro rfl
    simp

def rectRegion (r h : ℝ) : Set ℂ := {z | |z.re| ≤ r ∧ |z.im| ≤ h}

lemma convex_rectRegion (r h : ℝ) : Convex ℝ (rectRegion r h) := by
  have he : rectRegion r h = (Complex.reCLM ⁻¹' Icc (-r) r) ∩
      (Complex.imCLM ⁻¹' Icc (-h) h) := by
    ext z
    simp [rectRegion,abs_le]
  rw [he]
  exact ((convex_Icc (-r) r).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Icc (-h) h).linear_preimage Complex.imCLM.toLinearMap)

lemma rectPath_mem {r h : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h) (t : unitInterval) :
    rectPath r h t ∈ rectRegion r h := by
  have hs (a b : ℂ) (ha : a ∈ rectRegion r h) (hb : b ∈ rectRegion r h) :
      range (Path.segment a b) ⊆ rectRegion r h := by
    rintro _ ⟨s,rfl⟩
    simpa only [Path.segment_apply,AffineMap.lineMap_apply_module] using
      (convex_rectRegion r h) ha hb (sub_nonneg.mpr s.2.2) s.2.1 (by ring)
  have h₁ : ((-r : ℂ)-(h : ℂ)*Complex.I) ∈ rectRegion r h := by
    simp [rectRegion,abs_of_nonneg hr,abs_of_nonneg hh]
  have h₂ : ((r : ℂ)-(h : ℂ)*Complex.I) ∈ rectRegion r h := by
    simp [rectRegion,abs_of_nonneg hr,abs_of_nonneg hh]
  have h₃ : ((r : ℂ)+(h : ℂ)*Complex.I) ∈ rectRegion r h := by
    simp [rectRegion,abs_of_nonneg hr,abs_of_nonneg hh]
  have h₄ : ((-r : ℂ)+(h : ℂ)*Complex.I) ∈ rectRegion r h := by
    simp [rectRegion,abs_of_nonneg hr,abs_of_nonneg hh]
  have hb : range (rectPath r h) ⊆ rectRegion r h := by
    simp only [rectPath,Path.trans_range]
    exact union_subset (union_subset (union_subset (hs _ _ h₁ h₂) (hs _ _ h₂ h₃))
      (hs _ _ h₃ h₄)) (hs _ _ h₄ h₁)
  exact hb ⟨t,rfl⟩

lemma rectPath_ne_zero {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (t : unitInterval) :
    rectPath r h t ≠ 0 := by
  obtain ⟨T,hT,_⟩ := rectPath_logIncrement hr hh
  exact (hT t ▸ Complex.exp_ne_zero (T t))

end Brennan

end

end OAI
