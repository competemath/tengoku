import Tengoku.Seed.MeasureTheory.Function.ConditionalExpectation.PullOut
import Tengoku.Seed.Probability.Process.Filtration
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Positivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Iterating the coefficient Laplace bound across shapes

For nonnegative factors bounded by one, a conditional expectation bound at each
layer implies a product expectation bound. The factors may share all previously
exposed randomness; they are not assumed independent across layers.
-/

namespace Riesz
open MeasureTheory Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]

noncomputable def prefixProduct (Y : ℕ → Ω → ℝ) (n : ℕ) (ω : Ω) : ℝ :=
  ∏ i ∈ range n, Y i ω

/--
@isnad1 id=eq.0h3v.s5.ce6bfb051ba7 from=translated src=- shape=eed32ddf vocab=bbeb9901
-/
lemma prefixProduct_succ (Y : ℕ → Ω → ℝ) (n : ℕ) :
    prefixProduct Y (n + 1) = prefixProduct Y n * Y n := by
  funext ω
  simp [prefixProduct, Finset.prod_range_succ, Pi.mul_apply]

/--
@isnad1 id=strongly.1h5v.s6.91d7b448b237 from=translated src=- shape=4b0c1c4d vocab=a290580f
-/
lemma stronglyMeasurable_prefixProduct (ℱ : Filtration ℕ mΩ) (Y : ℕ → Ω → ℝ)
    (hY : ∀ i, StronglyMeasurable[ℱ (i + 1)] (Y i)) (n : ℕ) :
    StronglyMeasurable[ℱ n] (prefixProduct Y n) := by
  unfold prefixProduct
  apply Finset.stronglyMeasurable_fun_prod
  intro i hi
  exact (hY i).mono (ℱ.mono (by simpa [Finset.mem_range] using hi))

end Riesz

namespace Riesz
open MeasureTheory Finset

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsFiniteMeasure μ]

end Riesz
