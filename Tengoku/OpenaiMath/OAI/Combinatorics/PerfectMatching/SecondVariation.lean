import Tengoku.OpenaiMath.OAI.Combinatorics.PerfectMatching.Calculus

namespace OAI

/-!
The second-variation inequality at a maximum of the actual entropy defect.
-/

noncomputable section

open scoped BigOperators Topology
open Filter

namespace MatchingEntropy

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V] [DecidableEq E]

def entropyDefect (G : LooplessGraph V E) (m : ℝ) (y : E → ℝ) : ℝ :=
  entropyBarrier m (entropy y)-maxMatchingEntropy G y

theorem score_law_eventually_simplex {ι : Type*} [Fintype ι] {p : ι → ℝ}
    (hp : p ∈ probabilitySimplex ι) (a : ι → ℝ) (hcenter : ∑ i, p i*a i = 0) :
    ∀ᶠ t : ℝ in 𝓝 0, (fun i => p i+t*(p i*a i)) ∈ probabilitySimplex ι := by
  have hh : ∀ᶠ t : ℝ in 𝓝 0, ∀ i, 0 < 1+t*a i := by
    apply Filter.eventually_all.mpr
    intro i
    have hc : Continuous (fun t : ℝ => 1+t*a i) := by fun_prop
    exact (isOpen_lt continuous_const hc).mem_nhds (by norm_num)
  filter_upwards [hh] with t ht
  constructor
  · intro i
    have h := mul_nonneg (hp.1 i) (ht i).le
    nlinarith
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, hp.2, hcenter]
    ring

omit [Fintype V] [DecidableEq V] in
theorem mean_score_support (G : LooplessGraph V E) {p : G.Matching → ℝ}
    (hp : p ∈ probabilitySimplex G.Matching) (a : G.Matching → ℝ) :
    ∀ e, G.mean p e = 0 → G.mean (fun M => p M*a M) e = 0 := by
  intro e he
  have hterms : ∀ M, p M*G.indicator M e = 0 := by
    have hh := (Finset.sum_eq_zero_iff_of_nonneg
      (fun M (_ : M ∈ Finset.univ) => mul_nonneg (hp.1 M) (G.indicator_nonneg M e))).mp he
    exact fun M => hh M (Finset.mem_univ M)
  apply Finset.sum_eq_zero
  intro M _
  calc
    _ = a M*(p M*G.indicator M e) := by ring
    _ = 0 := by rw [hterms, mul_zero]

end MatchingEntropy

end

end OAI
