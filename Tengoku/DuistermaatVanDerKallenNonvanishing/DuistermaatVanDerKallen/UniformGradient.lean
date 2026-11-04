import Tengoku.Seed.Topology.Sequences
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Tactic.Push
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A topological proof of manuscript Lemma `lem:uniform-gradient`.
The radius is abstract but must have compact sublevels. This applies to the
proper affine-torus radius, not to the ordinary norm on the open torus. -/

open Filter
open scoped Topology

namespace DuistermaatVanDerKallen

/-- Ordinary scalar critical values, expressed through the differential norm.-/
def ordinaryCriticalValues {X Y : Type*} (F : X → Y) (lam : X → ℝ) : Set Y :=
  F '' {x | lam x = 0}

/-- Asymptotic critical values for a specified proper radius.-/
def asymptoticCriticalValues {X Y : Type*} [TopologicalSpace Y]
    (F : X → Y) (r lam : X → ℝ) : Set Y :=
  {c | ∃ x : ℕ → X, Tendsto (fun n => r (x n)) atTop atTop ∧
    Tendsto (fun n => F (x n)) atTop (𝓝 c) ∧
    Tendsto (fun n => r (x n) * lam (x n)) atTop (𝓝 0)}

/-- Compact-base lower bound, proved without a finiteness hypothesis on the
critical-value sets. Only exclusion of those sets and properness are needed.
@isnad1 id=ex.7h6v.s7.ac64315aa378 from=translated src=- shape=5a2f0008 vocab=140565fb
-/
theorem uniform_gradient_lower_bound {X Y : Type*}
    [TopologicalSpace X] [FirstCountableTopology X]
    [TopologicalSpace Y] [FirstCountableTopology Y] [T2Space Y]
    (F : X → Y) (r lam : X → ℝ)
    (hF : Continuous F) (hlam : Continuous lam)
    (hr : ∀ x, 0 ≤ r x) (hlam0 : ∀ x, 0 ≤ lam x)
    (hproper : ∀ R, IsCompact {x | r x ≤ R})
    (Q : Set Y) (hQ : IsCompact Q)
    (hgood : ∀ c ∈ Q, c ∉ ordinaryCriticalValues F lam ∪ asymptoticCriticalValues F r lam) :
    ∃ c > (0 : ℝ), ∀ x, F x ∈ Q → c ≤ (1 + r x) * lam x := by
  classical
  by_contra h
  push Not at h
  have hex : ∀ n : ℕ, ∃ x, F x ∈ Q ∧
      (1 + r x) * lam x < 1 / ((n : ℝ) + 1) :=
    fun n => h _ (by positivity)
  choose x hx hb using hex
  have hsmall : Tendsto (fun n => (1 + r (x n)) * lam (x n)) atTop (𝓝 0) :=
    squeeze_zero (fun n => mul_nonneg (by linarith [hr (x n)]) (hlam0 _))
      (fun n => (hb n).le) tendsto_one_div_add_atTop_nhds_zero_nat
  obtain ⟨c, hc, φ, hφ, hFc⟩ := hQ.isSeqCompact (x := fun n => F (x n)) hx
  have hs := hsmall.comp hφ.tendsto_atTop
  have hrl : Tendsto (fun n => r (x (φ n)) * lam (x (φ n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => mul_nonneg (hr _) (hlam0 _)) _ hs
    intro n
    dsimp only [Function.comp_apply]
    nlinarith [hlam0 (x (φ n))]
  have hl : Tendsto (fun n => lam (x (φ n))) atTop (𝓝 0) := by
    apply squeeze_zero (fun n => hlam0 _) _ hs
    intro n
    dsimp only [Function.comp_apply]
    nlinarith [mul_nonneg (hr (x (φ n))) (hlam0 (x (φ n)))]
  by_cases hescape : Tendsto (fun n => r (x (φ n))) atTop atTop
  · exact hgood c hc (Or.inr ⟨fun n => x (φ n), hescape, hFc, hrl⟩)
  · simp only [tendsto_atTop, not_forall] at hescape
    obtain ⟨R, hR⟩ := hescape
    have hfreq : ∃ᶠ n in atTop, x (φ n) ∈ {x | r x ≤ R} := by
      exact (Filter.not_eventually.mp hR).mono fun n hn => (not_le.mp hn).le
    obtain ⟨a, _, ψ, hψ, ha⟩ := (hproper R).isSeqCompact.subseq_of_frequently_in hfreq
    have hFa : F a = c := tendsto_nhds_unique (hF.tendsto a |>.comp ha)
      (hFc.comp hψ.tendsto_atTop)
    have hla : lam a = 0 := tendsto_nhds_unique (hlam.tendsto a |>.comp ha)
      (hl.comp hψ.tendsto_atTop)
    exact hgood c hc (Or.inl ⟨a, hla, hFa⟩)

/-- A radius bound alone is insufficient for continuation. Combined with the
uniform gradient bound it gives an explicit distance from the critical locus.
@isnad1 id=and.5h4v.s7.e73db868f601 from=translated src=- shape=2a2a5573 vocab=b1824736
-/
theorem regular_lower_bound_on_radius_sublevel {c r R lam : ℝ}
    (hc : 0 < c) (hr : 0 ≤ r) (hrR : r ≤ R) (hlam : 0 ≤ lam)
    (hbound : c ≤ (1 + r) * lam) :
    0 < c / (1 + R) ∧ c / (1 + R) ≤ lam := by
  have hR : 0 < 1 + R := by linarith
  refine ⟨div_pos hc hR, (div_le_iff₀ hR).2 ?_⟩
  nlinarith

end DuistermaatVanDerKallen
