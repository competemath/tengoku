import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.PoissonBoundary

namespace OAI

noncomputable section

namespace CompleteCrouzeix

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
section

lemma circleAverage_pos_at_I {g : ℂ → ℝ} (hg : ContinuousOn g (sphere 0 1))
    (hpos : ∀ z ∈ sphere (0 : ℂ) 1, 0 ≤ g z) (hI : 0 < g I) :
    0 < Real.circleAverage g 0 1 := by
  unfold Real.circleAverage
  apply smul_pos (by positivity)
  apply intervalIntegral.integral_pos Real.two_pi_pos
  · apply hg.comp (continuous_circleMap 0 1).continuousOn
    intro θ _
    simp
  · intro θ _
    apply hpos
    simp
  · refine ⟨Real.pi / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, ?_⟩
    simpa [circleMap_pi_div_two] using hI

def herglotzExtension (f : ℂ → ℝ) (w : ℂ) : ℂ :=
  Real.circleAverage (fun t => herglotzRieszKernel 0 w t • (f t : ℂ)) 0 1

open Set Filter Metric Complex
open scoped Topology

def upperLogNorm (g : ℂ → ℂ) (z : ℂ) : ℝ :=
  if z.im = 0 then 0 else Real.log ‖g z‖

lemma upperLogNorm_eventuallyEq (g : ℂ → ℂ) {z : ℂ} (hz : z.im ≠ 0) :
    upperLogNorm g =ᶠ[𝓝 z] (fun w => Real.log ‖g w‖) := by
  filter_upwards [Complex.continuous_im.continuousAt.eventually_ne hz] with w hw
  exact ite_eq_right hw

lemma upperLogNorm_continuousOn {g : ℂ → ℂ}
    (hg : ∀ z ∈ upperClosedDisk, 0 < z.im → AnalyticAt ℂ g z)
    (hn : ∀ z ∈ upperClosedDisk, 0 < z.im → g z ≠ 0)
    (hb : ∀ p ∈ upperClosedDisk, p.im = 0 →
      Tendsto (fun z => ‖g z‖) (𝓝[{z : ℂ | 0 < z.im}] p) (𝓝 1)) :
    ContinuousOn (upperLogNorm g) upperClosedDisk := by
  intro p hp
  by_cases hz : p.im = 0
  · have hpos : ContinuousWithinAt (upperLogNorm g) {z : ℂ | 0 < z.im} p := by
      change Tendsto (upperLogNorm g) _ (𝓝 (upperLogNorm g p))
      rw [upperLogNorm, ite_eq_left hz]
      have ht := (hb p hp hz).log (by norm_num : (1 : ℝ) ≠ 0)
      rw [Real.log_one] at ht
      apply ht.congr'
      filter_upwards [self_mem_nhdsWithin] with z hz
      exact (ite_eq_right (ne_of_gt hz)).symm
    have hreal : ContinuousWithinAt (upperLogNorm g) {z : ℂ | z.im = 0} p := by
      apply (continuousWithinAt_const (b := (0 : ℝ))).congr
      · intro z hz
        exact ite_eq_left hz
      · exact ite_eq_left hz
    apply (hreal.union hpos).mono
    intro z hz
    by_cases he : z.im = 0
    · exact Or.inl he
    · exact Or.inr (lt_of_le_of_ne hz.2 (Ne.symm he))
  · have hp' : 0 < p.im := lt_of_le_of_ne hp.2 (Ne.symm hz)
    have hc := ((hg p hp hp').continuousAt.norm.log (norm_ne_zero_iff.mpr (hn p hp hp')))
    exact (hc.congr (upperLogNorm_eventuallyEq g hz).symm).continuousWithinAt

end

open Set Filter Metric
open scoped Topology

theorem compact_local_injective_collar {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℂ} (hcont : ∀ z ∈ K, ContinuousAt f z) (hinj : InjOn f K)
    (hloc : ∀ z ∈ K, ∃ U ∈ 𝓝 z, InjOn f U) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ InjOn f U := by
  let R : Set (ℂ × ℂ) := {p | f p.1 = f p.2 → p.1 = p.2}
  have hR : R ∈ 𝓝ˢ (K ×ˢ K) := by
    rw [mem_nhdsSet_iff_forall]
    rintro ⟨x,y⟩ ⟨hx,hy⟩
    by_cases hxy : x = y
    · subst y
      obtain ⟨U,hU,hUi⟩ := hloc x hx
      apply mem_of_superset (show U ×ˢ U ∈ 𝓝 (x,x) by
        rw [nhds_prod_eq]; exact prod_mem_prod hU hU)
      rintro ⟨a,b⟩ ⟨ha,hb⟩
      exact hUi ha hb
    · have hne : f x - f y ≠ 0 := sub_ne_zero.mpr (fun he => hxy (hinj hx hy he))
      have hc : ContinuousAt (fun p : ℂ × ℂ => f p.1 - f p.2) (x,y) :=
        ((hcont x hx).comp continuousAt_fst).sub ((hcont y hy).comp continuousAt_snd)
      filter_upwards [hc.eventually_ne hne] with p hp
      exact fun he => False.elim (hp (sub_eq_zero.mpr he))
  rw [hK.nhdsSet_prod_eq hK, mem_prod_self_iff] at hR
  obtain ⟨V,hV,hVR⟩ := hR
  obtain ⟨U,hU,hKU,hUV⟩ := mem_nhdsSet_iff_exists.mp hV
  refine ⟨U,hU,hKU,?_⟩
  intro x hx y hy he
  have hr := hVR (show (x,y) ∈ V ×ˢ V from ⟨hUV hx,hUV hy⟩)
  exact hr he

theorem analytic_compact_injective_collar {K : Set ℂ} (hK : IsCompact K)
    {f : ℂ → ℂ} (ha : AnalyticOnNhd ℂ f K) (hd : ∀ z ∈ K, deriv f z ≠ 0)
    (hi : InjOn f K) :
    ∃ U : Set ℂ, IsOpen U ∧ K ⊆ U ∧ InjOn f U ∧ AnalyticOnNhd ℂ f U := by
  obtain ⟨U,hU,hKU,hUi⟩ := compact_local_injective_collar hK
    (fun z hz => (ha z hz).continuousAt) hi (by
      intro z hz
      have he := (ha z hz).hasStrictDerivAt.eventually_left_inverse (hd z hz)
      refine ⟨_,he,?_⟩
      intro x hx y hy hxy
      rw [← hx, ← hy, hxy])
  let W := {z | AnalyticAt ℂ f z}
  have hW : IsOpen W := isOpen_analyticAt ℂ f
  refine ⟨U ∩ W,hU.inter hW,fun z hz => ⟨hKU hz,ha z hz⟩,
    hUi.mono inter_subset_left,fun z hz => hz.2⟩

theorem conformal_modulus_boundary {U : Set ℂ} (hU : IsOpen U) {f g : ℂ → ℂ}
    (hf : MapsTo f U (ball 0 1)) (hg : ContinuousOn g (ball 0 1))
    (hgU : MapsTo g (ball 0 1) U) (hgf : ∀ z ∈ U, g (f z) = z)
    {p : ℂ} (hp : p ∈ frontier U) :
    Tendsto (fun z => ‖f z‖) (𝓝[U] p) (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    obtain ⟨r,hr,hra⟩ := exists_between (max_lt ha (by norm_num : (0:ℝ) < 1))
    have har : a < r := lt_of_le_of_lt (le_max_left a 0) hr
    have hsub : closedBall (0:ℂ) r ⊆ ball 0 1 := closedBall_subset_ball hra
    have hK : IsCompact (g '' closedBall (0:ℂ) r) :=
      (isCompact_closedBall 0 r).image_of_continuousOn (hg.mono hsub)
    have hpU : p ∉ U := by
      rw [hU.frontier_eq] at hp
      exact hp.2
    have hpK : p ∉ g '' closedBall (0:ℂ) r := fun ⟨z,hz,he⟩ => hpU (he ▸ hgU (hsub hz))
    have hn : (g '' closedBall (0:ℂ) r)ᶜ ∈ 𝓝 p := hK.isClosed.isOpen_compl.mem_nhds hpK
    filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds hn] with z hz hzK
    have hnz : r < ‖f z‖ := by
      by_contra h
      have hfz : f z ∈ closedBall (0:ℂ) r := by simpa using le_of_not_gt h
      exact hzK ⟨f z,hfz,hgf z hz⟩
    exact har.trans hnz
  · intro b hb
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (mem_ball_zero_iff.mp (hf hz)).trans hb

end CompleteCrouzeix

end

end OAI
