import Tengoku.OpenaiMath.OAI.Analysis.NumericalRange.Model

namespace OAI

noncomputable section

namespace CompleteCrouzeix

open Complex Metric Set Filter Real
open scoped Topology ComplexConjugate
section

def poissonExtension (f : ℂ → ℝ) (w : ℂ) : ℝ :=
  Real.circleAverage (fun t => poissonKernel 0 w t * f t) 0 1

lemma unit_poisson_nonneg {w t : ℂ} (hw : ‖w‖ < 1) (ht : t ∈ sphere 0 1) :
    0 ≤ poissonKernel 0 w t := by
  have ht' : ‖t‖ = 1 := by simpa using ht
  simp only [poissonKernel_def, sub_zero, ht']
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg w]

def diskDirichlet (f : ℂ → ℝ) (w : ℂ) : ℝ :=
  if ‖w‖ < 1 then poissonExtension f w else f w

lemma diskDirichlet_eq_boundary {f : ℂ → ℝ} {p : ℂ} (hp : p ∈ sphere 0 1) :
    diskDirichlet f p = f p := by
  have h : ‖p‖ = 1 := by simpa using hp
  simp [diskDirichlet,h]

end

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate
section

lemma harmonic_eventually_eq_of_isLocalMax {u : ℂ → ℝ} {p : ℂ}
    (hu : HarmonicAt u p) (hm : IsLocalMax u p) :
    ∀ᶠ z in 𝓝 p, u z = u p := by
  obtain ⟨r,hr,hrs⟩ := Metric.eventually_nhds_iff.mp hu.eventually
  have hur : HarmonicOnNhd u (ball p r) := fun z hz => hrs (by simpa [dist_comm] using hz)
  obtain ⟨H,hHa,hHu⟩ := hur.exists_analyticOnNhd_ball_re_eq
  have hp : p ∈ ball p r := mem_ball_self hr
  have hdiff : ∀ᶠ z in 𝓝 p, DifferentiableAt ℂ (fun z => Complex.exp (H z)) z := by
    filter_upwards [isOpen_ball.mem_nhds hp] with z hz
    exact Complex.differentiable_exp.differentiableAt.comp z (hHa z hz).differentiableAt
  have hmax : IsLocalMax (norm ∘ fun z => Complex.exp (H z)) p := by
    filter_upwards [hm, isOpen_ball.mem_nhds hp] with z hz hzr
    simp only [Function.comp_def, Complex.norm_exp, hHu hzr, hHu hp]
    exact Real.exp_le_exp.mpr hz
  filter_upwards [Complex.norm_eventually_eq_of_isLocalMax hdiff hmax,
    isOpen_ball.mem_nhds hp] with z hz hzr
  simp only [Complex.norm_exp] at hz
  exact (hHu hzr).symm.trans ((Real.exp_injective hz).trans (hHu hp))

lemma harmonic_eqOn_of_isPreconnected_of_isMaxOn {u : ℂ → ℝ} {U : Set ℂ} {p : ℂ}
    (hUc : IsPreconnected U) (hUo : IsOpen U) (hu : HarmonicOnNhd u U)
    (hp : p ∈ U) (hm : IsMaxOn u U p) : EqOn u (fun _ => u p) U := by
  let V := U ∩ {z | IsMaxOn u U z}
  have hV : ∀ z ∈ V, u z = u p := fun z hz => le_antisymm (hm hz.1) (hz.2 hp)
  have hVo : IsOpen V := by
    apply isOpen_iff_mem_nhds.mpr
    intro z hz
    have hh := harmonic_eventually_eq_of_isLocalMax (hu z hz.1)
      (hz.2.isLocalMax (hUo.mem_nhds hz.1))
    filter_upwards [hUo.mem_nhds hz.1, hh] with w hw huw
    exact ⟨hw, fun t ht => (hz.2 ht).trans_eq huw.symm⟩
  let W := U ∩ {z | u z ≠ u p}
  have hWo : IsOpen W := hu.continuousOn.isOpen_inter_preimage hUo isOpen_ne
  have hdis : Disjoint V W := disjoint_left.mpr fun z hv hw => hw.2 (hV z hv)
  have hcover : U ⊆ V ∪ W := by
    intro z hz
    by_cases he : u z = u p
    · exact Or.inl ⟨hz, fun t ht => (hm ht).trans_eq he.symm⟩
    · exact Or.inr ⟨hz,he⟩
  have hsub : U ⊆ V := hUc.subset_left_of_subset_union hVo hWo hdis hcover ⟨p,hp,hp,hm⟩
  exact fun z hz => hV z (hsub hz)

theorem harmonic_exists_mem_frontier_isMaxOn {u : ℂ → ℝ} {U : Set ℂ}
    (hUb : Bornology.IsBounded U) (hUne : U.Nonempty)
    (hu : HarmonicOnNhd u U) (huc : ContinuousOn u (closure U)) :
    ∃ p ∈ frontier U, IsMaxOn u (closure U) p := by
  have hc : IsCompact (closure U) := hUb.isCompact_closure
  obtain ⟨w,hw,hm⟩ := hc.exists_isMaxOn hUne.closure huc
  rw [closure_eq_interior_union_frontier, mem_union] at hw
  rcases hw with hw | hw
  · have hne : interior U ≠ univ := ne_top_of_le_ne_top hc.ne_univ interior_subset_closure
    obtain ⟨z,hz,hzw⟩ := exists_mem_frontier_infDist_compl_eq_dist hw hne
    have hd : 0 < dist w z := by
      apply dist_pos.mpr
      intro he
      subst z
      exact Set.disjoint_left.mp (disjoint_interior_frontier (s := U)) hw (frontier_interior_subset hz)
    have hball : ball w (dist w z) ⊆ U := by
      rw [← hzw]
      exact ball_infDist_compl_subset.trans interior_subset
    have hconst := harmonic_eqOn_of_isPreconnected_of_isMaxOn
      (convex_ball w (dist w z)).isPreconnected isOpen_ball (hu.mono hball)
      (mem_ball_self hd) (hm.on_subset (hball.trans subset_closure))
    have hcl : EqOn u (fun _ => u w) (closure (ball w (dist w z))) :=
      hconst.of_subset_closure (huc.mono (closure_mono hball)) continuousOn_const subset_closure Subset.rfl
    have hze : u z = u w := hcl (by rw [closure_ball _ hd.ne']; simp [dist_comm])
    exact ⟨z,frontier_interior_subset hz, fun t ht => (hm ht).trans_eq hze.symm⟩
  · exact ⟨w,hw,hm⟩

theorem harmonic_le_of_frontier_le {u : ℂ → ℝ} {U : Set ℂ} {C : ℝ}
    (hUb : Bornology.IsBounded U) (hu : HarmonicOnNhd u U)
    (huc : ContinuousOn u (closure U)) (hbd : ∀ z ∈ frontier U, u z ≤ C)
    {z : ℂ} (hz : z ∈ closure U) : u z ≤ C := by
  have hUne : U.Nonempty := by
    by_contra hn
    have he : U = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [he] at hz
  obtain ⟨p,hp,hm⟩ := harmonic_exists_mem_frontier_isMaxOn hUb hUne hu huc
  exact (hm hz).trans (hbd p hp)

theorem harmonic_eqOn_closure_of_eqOn_frontier {u v : ℂ → ℝ} {U : Set ℂ}
    (hUb : Bornology.IsBounded U) (hu : HarmonicOnNhd u U) (hv : HarmonicOnNhd v U)
    (huc : ContinuousOn u (closure U)) (hvc : ContinuousOn v (closure U))
    (hbd : EqOn u v (frontier U)) : EqOn u v (closure U) := by
  intro z hz
  apply le_antisymm
  · have hh := harmonic_le_of_frontier_le hUb (hu.sub hv) (huc.sub hvc)
      (C := 0) (fun t ht => by simp [hbd ht]) hz
    exact sub_nonpos.mp hh
  · have hh := harmonic_le_of_frontier_le hUb (hv.sub hu) (hvc.sub huc)
      (C := 0) (fun t ht => by simp [hbd ht]) hz
    exact sub_nonpos.mp hh

end

open Complex InnerProductSpace Metric Set Filter
open scoped Topology ComplexConjugate

lemma circleAverage_conj {g : ℂ → ℝ} :
    Real.circleAverage (fun z => g (conj z)) 0 1 = Real.circleAverage g 0 1 := by
  rw [← Real.circleAverage_zero_one_congr_inv (f := g)]
  apply Real.circleAverage_congr_sphere
  intro z hz
  have hn : ‖z‖ = 1 := by simpa using hz
  simp only [Complex.inv_eq_conj hn]

lemma unit_poisson_conj (w t : ℂ) :
    poissonKernel 0 (conj w) (conj t) = poissonKernel 0 w t := by
  simp only [poissonKernel_def, sub_zero, ← map_sub, Complex.norm_conj]

lemma poissonExtension_odd {f : ℂ → ℝ}
    (hodd : ∀ z ∈ sphere (0 : ℂ) 1, f (conj z) = -f z) (w : ℂ) :
    poissonExtension f (conj w) = -poissonExtension f w := by
  unfold poissonExtension
  rw [← circleAverage_conj (g := fun t => poissonKernel 0 (conj w) t * f t)]
  calc
    _ = Real.circleAverage (fun t => -(poissonKernel 0 w t * f t)) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro t ht
      change poissonKernel 0 (conj w) (conj t) * f (conj t) = -(poissonKernel 0 w t * f t)
      rw [unit_poisson_conj, hodd t (by simpa using ht)]
      ring
    _ = _ := by simp [Real.circleAverage, intervalIntegral.integral_neg]

lemma diskDirichlet_zero_real {f : ℂ → ℝ}
    (hodd : ∀ z ∈ sphere (0 : ℂ) 1, f (conj z) = -f z)
    {z : ℂ} (hz : ‖z‖ < 1) (hzi : z.im = 0) : diskDirichlet f z = 0 := by
  have hc : conj z = z := Complex.conj_eq_iff_im.mpr hzi
  have hh := poissonExtension_odd hodd z
  rw [hc] at hh
  simp only [diskDirichlet, ite_eq_left hz]
  linarith

def upperDisk : Set ℂ := ball 0 1 ∩ {z | 0 < z.im}
def upperClosedDisk : Set ℂ := closedBall 0 1 ∩ {z | 0 ≤ z.im}

lemma upperDisk_isOpen : IsOpen upperDisk :=
  isOpen_ball.inter (isOpen_lt continuous_const Complex.continuous_im)

lemma closure_upperDisk_subset : closure upperDisk ⊆ upperClosedDisk := by
  apply closure_minimal
  · intro z hz
    exact ⟨ball_subset_closedBall hz.1, le_of_lt (show 0 < z.im from hz.2)⟩
  · exact isClosed_closedBall.inter (isClosed_le continuous_const Complex.continuous_im)

lemma upper_frontier_or {z : ℂ} (hz : z ∈ frontier upperDisk) : ‖z‖ = 1 ∨ z.im = 0 := by
  have hc := closure_upperDisk_subset hz.1
  have hn : ‖z‖ ≤ 1 := by simpa using hc.1
  by_cases he : ‖z‖ = 1
  · exact Or.inl he
  · right
    by_contra hi
    have hi' : 0 < z.im := lt_of_le_of_ne hc.2 (Ne.symm hi)
    apply hz.2
    rw [upperDisk_isOpen.interior_eq]
    exact ⟨by simpa using lt_of_le_of_ne hn he, hi'⟩

def oddBoundary (u : ℂ → ℝ) (z : ℂ) : ℝ :=
  if 0 ≤ z.im then u z else -u (conj z)

lemma oddBoundary_odd {u : ℂ → ℝ}
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0)
    {z : ℂ} (hz : z ∈ sphere (0 : ℂ) 1) : oddBoundary u (conj z) = -oddBoundary u z := by
  have hn : ‖z‖ = 1 := by simpa using hz
  by_cases hzi : z.im = 0
  · have hc : conj z = z := Complex.conj_eq_iff_im.mpr hzi
    have hu := hzero z ⟨by simp [hn], by simp [hzi]⟩ hzi
    simp [oddBoundary,hc,hzi,hu]
  · by_cases hpos : 0 ≤ z.im
    · have hpos' : 0 < z.im := lt_of_le_of_ne hpos (Ne.symm hzi)
      have hh : ¬0 ≤ (conj z).im := by simp only [Complex.conj_im]; linarith
      simp only [oddBoundary, ite_eq_left hpos, ite_eq_right hh, Complex.conj_conj]
    · have hh : 0 ≤ (conj z).im := by simp only [Complex.conj_im]; linarith
      simp only [oddBoundary, ite_eq_right hpos, ite_eq_left hh, neg_neg]

lemma continuousOn_oddBoundary {u : ℂ → ℝ}
    (hu : ContinuousOn u upperClosedDisk)
    (hzero : ∀ z ∈ upperClosedDisk, z.im = 0 → u z = 0) :
    ContinuousOn (oddBoundary u) (sphere 0 1) := by
  have hup : IsClosed {z : ℂ | 0 ≤ z.im} := isClosed_le continuous_const Complex.continuous_im
  have hdown : closure {z : ℂ | ¬0 ≤ z.im} ⊆ {z | z.im ≤ 0} := by
    apply closure_minimal
    · intro z hz
      exact (lt_of_not_ge hz).le
    · exact isClosed_le Complex.continuous_im continuous_const
  have hfront : ∀ z ∈ frontier {z : ℂ | 0 ≤ z.im}, z.im = 0 := by
    intro z hz
    have hp : 0 ≤ z.im := by simpa [hup.closure_eq] using hz.1
    have hm : z.im ≤ 0 := by
      have hh : z ∈ closure {z : ℂ | ¬0 ≤ z.im} := by
        change z ∈ closure ({z : ℂ | 0 ≤ z.im}ᶜ)
        rw [closure_compl]
        exact hz.2
      exact hdown hh
    exact le_antisymm hm hp
  apply ContinuousOn.if
  · intro z hz
    have hzi := hfront z hz.2
    have hn : ‖z‖ = 1 := by simpa using hz.1
    have hc : conj z = z := Complex.conj_eq_iff_im.mpr hzi
    rw [hc, hzero z ⟨by simp [hn], by simp [hzi]⟩ hzi, neg_zero]
  · apply hu.mono
    intro z hz
    exact ⟨sphere_subset_closedBall hz.1, by simpa [hup.closure_eq] using hz.2⟩
  · apply ContinuousOn.neg
    apply hu.comp Complex.continuous_conj.continuousOn
    intro z hz
    exact ⟨by simpa using (sphere_subset_closedBall hz.1), by
      simp only [mem_ofPred_eq, Complex.conj_im, neg_nonneg]; exact hdown hz.2⟩

end CompleteCrouzeix

end

end OAI
