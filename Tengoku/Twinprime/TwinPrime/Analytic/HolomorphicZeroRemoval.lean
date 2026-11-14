import Tengoku.Seed.Analysis.Meromorphic.FactorizedRational
import Tengoku.Seed.Analysis.Meromorphic.RCLike

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Removing the actual zeros on a compact subset

The divisor of a holomorphic function supplies the multiplicities. The
quotient is extended at its removable singularities and the resulting
factorization holds at every point, including the original zeros.
-/

noncomputable section

open Filter Function MeromorphicOn Set
open scoped Topology

namespace TwinPrime.Analytic

def zeroFactorPolynomial (f : ℂ → ℂ) (K : Set ℂ) : ℂ → ℂ :=
  ∏ᶠ u, (· - u) ^ divisor f K u

theorem exists_holomorphic_zero_removal {f : ℂ → ℂ} {U K : Set ℂ} {c : ℂ}
    (hf : AnalyticOnNhd ℂ f U) (hU : IsPreconnected U) (hc : c ∈ U)
    (hfc : f c ≠ 0) (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g U ∧ (∀ z ∈ K, g z ≠ 0) ∧
      ∀ z ∈ U, f z = zeroFactorPolynomial f K z * g z := by
  let D := divisor f K
  let P := zeroFactorPolynomial f K
  have hfin : D.support.Finite := D.finiteSupport hK
  have hD : ∀ z, 0 ≤ D z := (hf.mono hKU).divisor_nonneg
  have hP (z : ℂ) : AnalyticAt ℂ P z := Function.FactorizedRational.analyticAt (hD z)
  have hPn (z : ℂ) : meromorphicOrderAt P z ≠ ⊤ :=
    Function.FactorizedRational.meromorphicOrderAt_ne_top D
  have hPo (z : ℂ) : meromorphicOrderAt P z = (D z : WithTop ℤ) :=
    Function.FactorizedRational.meromorphicOrderAt_eq D hfin
  have hfn : ∀ z ∈ U, meromorphicOrderAt f z ≠ ⊤ := by
    intro z hz
    apply hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected hU hc hz
    rw [(hf c hc).meromorphicNFAt.meromorphicOrderAt_eq_zero_iff.mpr hfc]
    simp
  have hquot : MeromorphicOn (f / P) U :=
    hf.meromorphicOn.div (fun z _ => (hP z).meromorphicAt)
  let g := toMeromorphicNFOn (f / P) U
  have hgnf : MeromorphicNFOn g U := meromorphicNFOn_toMeromorphicNFOn _ _
  have hgo (z : ℂ) (hz : z ∈ U) :
      meromorphicOrderAt g z = meromorphicOrderAt f z - (D z : WithTop ℤ) := by
    dsimp [g]
    rw [meromorphicOrderAt_toMeromorphicNFOn hquot hz,
      meromorphicOrderAt_div (hf z hz).meromorphicAt (hP z).meromorphicAt, hPo]
  have hgoK (z : ℂ) (hz : z ∈ K) : meromorphicOrderAt g z = 0 := by
    rw [hgo z (hKU hz)]
    dsimp [D]
    rw [divisor_apply (hf.mono hKU).meromorphicOn hz]
    lift meromorphicOrderAt f z to ℤ using hfn z (hKU hz) with n hn
    simp
  have hg : AnalyticOnNhd ℂ g U := by
    intro z hz
    apply (hgnf hz).meromorphicOrderAt_nonneg_iff_analyticAt.mp
    by_cases hzK : z ∈ K
    · rw [hgoK z hzK]
    · rw [hgo z hz]
      have hDz : D z = 0 := by simp [D, hzK]
      rw [hDz, WithTop.coe_zero, sub_zero]
      exact (hf z hz).meromorphicOrderAt_nonneg
  refine ⟨g, hg, fun z hz => (hgnf (hKU hz)).meromorphicOrderAt_eq_zero_iff.mp (hgoK z hz), ?_⟩
  intro z hz
  have hPe : ∀ᶠ w in 𝓝[≠] z, P w ≠ 0 :=
    (meromorphicOrderAt_ne_top_iff_eventually_ne_zero (hP z).meromorphicAt).mp (hPn z)
  have he : f =ᶠ[𝓝[≠] z] P * g := by
    filter_upwards [hquot.toMeromorphicNFOn_eq_self_on_nhdsNE hz, hPe] with w hw hn
    change g w = f w / P w at hw
    change f w = P w * g w
    rw [hw]
    field_simp
  have he' : f =ᶠ[𝓝 z] P * g :=
    ((hf z hz).continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE
      ((hP z).continuousAt.mul (hg z hz).continuousAt)).mp he
  exact he'.eq_of_nhds

end TwinPrime.Analytic
