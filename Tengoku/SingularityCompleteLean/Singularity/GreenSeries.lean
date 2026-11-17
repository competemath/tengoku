import Tengoku.SingularityCompleteLean.Singularity.Green
import Tengoku.Seed.Analysis.Normed.Algebra.GelfandFormula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The Green resolvent is the norm-convergent Green series

Gelfand's formula supplies an eventual geometric bound on the operator powers
from spectral radius < 1. This does not assume the stronger condition ‖P‖ < 1.
Identification with the random-walk path probabilities is proved in `WalkKernel.lean`
and `FiniteWalkLaw.lean`.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace Singularity

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- An operator spectral gap implies an eventual geometric bound on the powers.
@isnad1 id=ex.1h2v.s9.ce386c70920a from=translated src=- shape=661ebe0b vocab=1044c910
-/
theorem green_powers_geometric_bound (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    ∃ q : ℝ, 0 ≤ q ∧ q < 1 ∧ ∀ᶠ n : ℕ in atTop, ‖P ^ n‖ ≤ q ^ n := by
  obtain ⟨r, hr, hr1⟩ := exists_between hgap
  have hrfin : r ≠ ⊤ := ne_top_of_lt hr1
  have hq0 : 0 ≤ r.toReal := ENNReal.toReal_nonneg
  have hq1 : r.toReal < 1 := by
    simpa using (ENNReal.toReal_lt_toReal hrfin ENNReal.one_ne_top).mpr hr1
  refine ⟨r.toReal, hq0, hq1, ?_⟩
  have he : ∀ᶠ n : ℕ in atTop, ENNReal.ofReal (‖P ^ n‖ ^ (1 / (n : ℝ))) < r :=
    (spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius P).eventually (gt_mem_nhds hr)
  filter_upwards [he, eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast hn0
  have hroot : ‖P ^ n‖ ^ (1 / (n : ℝ)) ≤ r.toReal :=
    ((ENNReal.ofReal_lt_iff_lt_toReal (Real.rpow_nonneg (norm_nonneg _) _) hrfin).mp hn).le
  calc
    ‖P ^ n‖ = (‖P ^ n‖ ^ (1 / (n : ℝ))) ^ (n : ℝ) := by
      rw [← Real.rpow_mul (norm_nonneg _), one_div_mul_cancel hnpos.ne', Real.rpow_one]
    _ ≤ r.toReal ^ (n : ℝ) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (norm_nonneg _) _) hroot hnpos.le
    _ = r.toReal ^ n := Real.rpow_natCast _ _

/-- The norms of the Green-series terms are summable.
@isnad1 id=summable.1h2v.s9.e4ce7387d175 from=translated src=- shape=1a973f43 vocab=d3ef21b9
-/
theorem green_powers_norm_summable (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    Summable (fun n : ℕ => ‖P ^ n‖) := by
  obtain ⟨q, hq0, hq1, hbound⟩ := green_powers_geometric_bound P hgap
  apply (summable_geometric_of_lt_one hq0 hq1).of_norm_bounded_eventually_nat
  simpa only [norm_norm] using hbound

/-- Absolute norm convergence gives convergence in the operator Banach space.
@isnad1 id=summable.1h2v.s9.de48514aad58 from=translated src=- shape=8139d056 vocab=9461809d
-/
theorem green_powers_summable (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    Summable (fun n : ℕ => P ^ n) :=
  (green_powers_norm_summable P hgap).of_norm

/-- The sum of the operator powers is exactly the previously constructed resolvent.
@isnad1 id=eq.1h2v.s10.bc6239fd5635 from=translated src=- shape=cc6d81de vocab=fcd29aba
-/
theorem green_eq_tsum (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    green P = ∑' n : ℕ, P ^ n := by
  have hs := green_powers_summable P hgap
  calc
    green P = green P * ((1 - P) * ∑' n : ℕ, P ^ n) := by
      rw [hs.one_sub_mul_tsum_pow, mul_one]
    _ = ∑' n : ℕ, P ^ n := by
      rw [← mul_assoc]
      change Ring.inverse (1 - P) * (1 - P) * _ = _
      rw [Ring.inverse_mul_cancel (1 - P) (one_sub_isUnit P hgap), one_mul]

/-- The Green series converges in operator norm to the resolvent.
@isnad1 id=hassum.1h2v.s9.cb14176bdcf1 from=translated src=- shape=a6fc4fba vocab=a851a348
-/
theorem green_hasSum (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) :
    HasSum (fun n : ℕ => P ^ n) (green P) := by
  rw [green_eq_tsum P hgap]
  exact (green_powers_summable P hgap).hasSum

/-- Evaluation at a vector commutes with the norm-convergent Green series.
@isnad1 id=hassum.1h3v.s10.990cdc4329b9 from=translated src=- shape=3fb2ad52 vocab=e99a6925
-/
theorem green_apply_hasSum (P : E →L[ℂ] E) (hgap : spectralRadius ℂ P < 1) (v : E) :
    HasSum (fun n : ℕ => (P ^ n) v) (green P v) :=
  (ContinuousLinearMap.apply ℂ E v).hasSum (green_hasSum P hgap)

end Singularity
