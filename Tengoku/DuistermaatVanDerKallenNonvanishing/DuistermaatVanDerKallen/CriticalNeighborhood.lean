import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.UniformGradient
import Tengoku.Seed.Topology.MetricSpace.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A local form of the proper-radius compactness argument. It proves openness
of the good-value set without asserting finiteness of either critical-value set. -/

open Filter Set
open scoped Topology

namespace DuistermaatVanDerKallen

/-- At each noncritical, non-asymptotic value, the weighted gradient is bounded
below on the inverse image of a whole base neighborhood.
@isnad1 id=ex.6h6v.s7.637af4c2c037 from=translated src=- shape=63c1319d vocab=9b9b6fbc
-/
theorem exists_local_gradient_bound {X Y : Type*}
    [TopologicalSpace X] [FirstCountableTopology X] [MetricSpace Y]
    (F : X → Y) (r lam : X → ℝ)
    (hF : Continuous F) (hlam : Continuous lam)
    (hr : ∀ x, 0 ≤ r x) (hlam0 : ∀ x, 0 ≤ lam x)
    (hproper : ∀ R, IsCompact {x | r x ≤ R})
    {c : Y} (hc : c ∉ ordinaryCriticalValues F lam ∪ asymptoticCriticalValues F r lam) :
    ∃ ε > (0 : ℝ), ∃ a > (0 : ℝ),
      ∀ x, dist (F x) c < ε → a ≤ (1 + r x) * lam x := by
  classical
  by_contra h
  push Not at h
  have hex : ∀ n : ℕ, ∃ x, dist (F x) c < 1 / ((n : ℝ) + 1) ∧
      (1 + r x) * lam x < 1 / ((n : ℝ) + 1) :=
    fun n => h _ (by positivity) _ (by positivity)
  choose x hx hb using hex
  have hFc : Tendsto (fun n => F (x n)) atTop (𝓝 c) := by
    apply tendsto_iff_dist_tendsto_zero.mpr
    exact squeeze_zero (fun _ => dist_nonneg) (fun n => (hx n).le)
      tendsto_one_div_add_atTop_nhds_zero_nat
  have hs : Tendsto (fun n => (1 + r (x n)) * lam (x n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => mul_nonneg (by linarith [hr (x n)]) (hlam0 _))
      (fun n => (hb n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  have hrl : Tendsto (fun n => r (x n) * lam (x n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => mul_nonneg (hr _) (hlam0 _)) _ hs
    intro n
    nlinarith [hlam0 (x n)]
  have hl : Tendsto (fun n => lam (x n)) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => hlam0 _) _ hs
    intro n
    nlinarith [mul_nonneg (hr (x n)) (hlam0 (x n))]
  by_cases hescape : Tendsto (fun n => r (x n)) atTop atTop
  · exact hc (Or.inr ⟨x, hescape, hFc, hrl⟩)
  · simp only [tendsto_atTop, not_forall] at hescape
    obtain ⟨R, hR⟩ := hescape
    have hfreq : ∃ᶠ n in atTop, x n ∈ {x | r x ≤ R} :=
      (Filter.not_eventually.mp hR).mono fun n hn => (not_le.mp hn).le
    obtain ⟨a, _, ψ, hψ, ha⟩ := (hproper R).isSeqCompact.subseq_of_frequently_in hfreq
    have hFa : F a = c := tendsto_nhds_unique (hF.tendsto a |>.comp ha)
      (hFc.comp hψ.tendsto_atTop)
    have hla : lam a = 0 := tendsto_nhds_unique (hlam.tendsto a |>.comp ha)
      (hl.comp hψ.tendsto_atTop)
    exact hc (Or.inl ⟨a, hla, hFa⟩)

/-- A positive weighted-gradient lower bound over an open base set excludes
both ordinary and asymptotic critical values from that set.
@isnad1 id=not.4h8v.s6.d354c09261b3 from=translated src=- shape=13f396e3 vocab=a939d903
-/
theorem gradient_bound_excludes_critical {X Y : Type*} [TopologicalSpace Y]
    (F : X → Y) (r lam : X → ℝ)
    {U : Set Y} (hU : IsOpen U) {a : ℝ} (ha : 0 < a)
    (hbound : ∀ x, F x ∈ U → a ≤ (1 + r x) * lam x) :
    ∀ c ∈ U, c ∉ ordinaryCriticalValues F lam ∪ asymptoticCriticalValues F r lam := by
  intro c hc hcrit
  rcases hcrit with ⟨x, hx, rfl⟩ | ⟨x, hr, hF, hl⟩
  · have hb := hbound x hc
    rw [hx, mul_zero] at hb
    exact (not_le_of_gt ha) hb
  · have hsmall : ∀ᶠ n in atTop, r (x n) * lam (x n) < a / 2 :=
      hl.eventually (gt_mem_nhds (by linarith))
    have hlarge : ∀ᶠ n in atTop, 1 ≤ r (x n) := hr.eventually_ge_atTop 1
    have hbase : ∀ᶠ n in atTop, F (x n) ∈ U := hF.eventually (hU.mem_nhds hc)
    obtain ⟨n, hn, hnr, hnU⟩ := (hsmall.and (hlarge.and hbase)).exists
    have hb := hbound (x n) hnU
    nlinarith

/-- The union of ordinary and asymptotic critical values is closed for a
continuous scalar norm over a space with compact radius sublevels.
@isnad1 id=isclosed.5h5v.s7.88ad1f3690bf from=translated src=- shape=39205efc vocab=5181cde7
-/
theorem criticalValues_union_isClosed {X Y : Type*}
    [TopologicalSpace X] [FirstCountableTopology X] [MetricSpace Y]
    (F : X → Y) (r lam : X → ℝ)
    (hF : Continuous F) (hlam : Continuous lam)
    (hr : ∀ x, 0 ≤ r x) (hlam0 : ∀ x, 0 ≤ lam x)
    (hproper : ∀ R, IsCompact {x | r x ≤ R}) :
    IsClosed (ordinaryCriticalValues F lam ∪ asymptoticCriticalValues F r lam) := by
  rw [← isOpen_compl_iff]
  apply Metric.isOpen_iff.mpr
  intro c hc
  obtain ⟨ε, hε, a, ha, hb⟩ := exists_local_gradient_bound F r lam hF hlam hr hlam0 hproper hc
  exact ⟨ε, hε, gradient_bound_excludes_critical F r lam Metric.isOpen_ball ha hb⟩

end DuistermaatVanDerKallen
