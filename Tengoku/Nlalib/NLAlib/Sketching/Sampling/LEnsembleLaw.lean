import Tengoku.Nlalib.NLAlib.Matrix.Inequalities.PrincipalMinorProducts
import Tengoku.Seed.Probability.ProbabilityMassFunction.Integrals
import Tengoku.Seed.Probability.HasLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Variable-size determinantal L-ensembles

PSD principal-minor weights define an actual finite PMF and probability
measure, without a rank or nonsingularity condition on the kernel. Their
multivariate generating function is the normalized determinant.
Source: Dereziński–Mahoney 2020, §3, Definitions 2–4.
Atlas: `l-ensemble-law`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace NLAlib

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The L-ensemble normalizer is the sum of every principal minor, including
the empty minor one. Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-law (partial)
@isnad1 id=eq.0h2v.s6.7ba22bb6b064 from=translated src=- shape=08f38f3e vocab=bc19dd77
-/
theorem sum_principalMinor_eq_det_one_add (L : Matrix n n ℝ) :
    ∑ S : Finset n, principalMinor L S = (1 + L).det := by
  exact (Matrix.det_one_add_eq_sum_principal_minors L).symm

/-- The normalized principal-minor mass. For kernels outside the PSD domain
this is merely a total scalar formula; `lEnsemblePMF` requires PSD.-/
def lEnsembleProbability (L : Matrix n n ℝ) (S : Finset n) : ℝ :=
  principalMinor L S / (1 + L).det

/-- Each L-ensemble mass is nonnegative for a PSD kernel.
@isnad1 id=le.1h3v.s5.a1cac338e2e0 from=translated src=- shape=1d92e1fc vocab=a8ae4b0f
-/
theorem lEnsembleProbability_nonneg {L : Matrix n n ℝ} (hL : L.PosSemidef)
    (S : Finset n) : 0 ≤ lEnsembleProbability L S :=
  div_nonneg (principalMinor_nonneg hL S) ((by norm_num : (0 : ℝ) ≤ 1).trans
    (hL.one_le_det_one_add))

/-- All L-ensemble masses sum to one. No prescribed cardinality is imposed.
@isnad1 id=eq.1h2v.s5.fef5753c80a0 from=translated src=- shape=b656fda9 vocab=6887de5c
-/
theorem sum_lEnsembleProbability {L : Matrix n n ℝ} (hL : L.PosSemidef) :
    ∑ S : Finset n, lEnsembleProbability L S = 1 := by
  simp only [lEnsembleProbability, ← Finset.sum_div, sum_principalMinor_eq_det_one_add]
  exact div_self (ne_of_gt (lt_of_lt_of_le zero_lt_one
    (hL.one_le_det_one_add)))

/-- The variable-size determinantal PMF on every finite subset of the index
set. The empty determinant has mass `1 / det (I + L)`.
Dereziński–Mahoney 2020, §3, Definition 3.
atlas: l-ensemble-law (partial)-/
def lEnsemblePMF (L : Matrix n n ℝ) (hL : L.PosSemidef) : PMF (Finset n) := by
  classical
  refine PMF.ofFintype (fun S => ENNReal.ofReal (lEnsembleProbability L S)) ?_
  rw [← ENNReal.ofReal_sum_of_nonneg (fun S _ => lEnsembleProbability_nonneg hL S),
    sum_lEnsembleProbability hL]
  simp

/-- The variable-size L-ensemble probability measure associated with a real
PSD kernel. Dereziński–Mahoney 2020, §3, Definition 3.
atlas: l-ensemble-law (partial)-/
def lEnsembleLaw (L : Matrix n n ℝ) (hL : L.PosSemidef) : Measure (Finset n) :=
  (lEnsemblePMF L hL).toMeasure

/-- The normalized principal-minor measure is a probability measure.
@isnad1 id=isprobab.1h2v.s5.cbf6c3a43125 from=translated src=- shape=58239542 vocab=b5c4986e
-/
instance lEnsembleLaw_isProbabilityMeasure (L : Matrix n n ℝ) (hL : L.PosSemidef) :
    IsProbabilityMeasure (lEnsembleLaw L hL) := by
  unfold lEnsembleLaw
  infer_instance

/-- The L-ensemble assigns total mass one to all finite subsets.
Dereziński–Mahoney 2020, §3, Definition 3.
atlas: l-ensemble-law (partial)
@isnad1 id=eq.1h2v.s5.baccf4ce3a11 from=translated src=- shape=c0f71d7c vocab=304efbb3
-/
theorem lEnsembleLaw_univ (L : Matrix n n ℝ) (hL : L.PosSemidef) :
    lEnsembleLaw L hL Set.univ = 1 := measure_univ

/-- Expectations under an L-ensemble are finite sums of its principal-minor
probabilities. Every function on this finite sample space is integrable.
@isnad1 id=eq.1h3v.s6.657bbbdbb377 from=translated src=- shape=3a9499b8 vocab=ab6eac14
-/
theorem integral_lEnsembleLaw (L : Matrix n n ℝ) (hL : L.PosSemidef)
    (f : Finset n → ℝ) :
    ∫ S, f S ∂lEnsembleLaw L hL = ∑ S, lEnsembleProbability L S * f S := by
  classical
  rw [lEnsembleLaw, PMF.integral_eq_sum]
  simp only [lEnsemblePMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (lEnsembleProbability_nonneg hL _), smul_eq_mul]

/-- The mass of each finite subset is exactly its normalized principal minor.
Dereziński–Mahoney 2020, §3, Definition 3.
atlas: l-ensemble-law (partial)
@isnad1 id=eq.1h3v.s5.a4cc54e31b16 from=translated src=- shape=05f7fada vocab=d1899cf6
-/
theorem lEnsembleLaw_singleton (L : Matrix n n ℝ) (hL : L.PosSemidef) (S : Finset n) :
    (lEnsembleLaw L hL).real {S} = lEnsembleProbability L S := by
  classical
  rw [Measure.real, lEnsembleLaw,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton S)]
  simp only [lEnsemblePMF, PMF.ofFintype_apply,
    ENNReal.toReal_ofReal (lEnsembleProbability_nonneg hL S)]

/-- The L-ensemble generating function is the normalized multivariate
principal-minor determinant, for arbitrary real row weights including negative
and zero weights. Dereziński–Mahoney 2020, §3.
atlas: l-ensemble-law (partial)
@isnad1 id=eq.1h3v.s7.83f889fb93fe from=translated src=- shape=831cd222 vocab=f0c44377
-/
theorem integral_prod_lEnsembleLaw (L : Matrix n n ℝ) (hL : L.PosSemidef) (z : n → ℝ) :
    ∫ S, (∏ i ∈ S, z i) ∂lEnsembleLaw L hL =
      (1 + Matrix.diagonal z * L).det / (1 + L).det := by
  rw [integral_lEnsembleLaw, Matrix.det_one_add_diagonal_mul]
  simp only [lEnsembleProbability, principalMinor, Matrix.toBlock, div_mul_eq_mul_div,
    Finset.sum_div]

/-- The same generating-function identity holds for any random finite subset
with the L-ensemble law.
@isnad1 id=eq.2h6v.s7.2b17da52f6c2 from=translated src=- shape=dcf78efd vocab=17f99ea9
-/
theorem integral_prod_lEnsembleLaw_of_hasLaw {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (L : Matrix n n ℝ) (hL : L.PosSemidef)
    {S : Ω → Finset n} (hS : HasLaw S (lEnsembleLaw L hL) μ) (z : n → ℝ) :
    ∫ ω, (∏ i ∈ S ω, z i) ∂μ =
      (1 + Matrix.diagonal z * L).det / (1 + L).det := by
  have hm : AEStronglyMeasurable (fun T : Finset n => ∏ i ∈ T, z i)
      (lEnsembleLaw L hL) := (measurable_of_finite _).aestronglyMeasurable
  exact (hS.integral_comp hm).trans (integral_prod_lEnsembleLaw L hL z)

end NLAlib
