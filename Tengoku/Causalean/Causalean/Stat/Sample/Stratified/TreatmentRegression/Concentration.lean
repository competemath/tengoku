module
public import Tengoku.Causalean.Causalean.Stat.Concentration.TailBounds.McDiarmid
public import Tengoku.Causalean.Causalean.Stat.Sample.Stratified.TreatmentRegression.CategoricalLaw
public import Tengoku.Causalean.Causalean.Stat.Sample.Stratified.TreatmentRegression.DesignAlgebra
public import Tengoku.Causalean.Causalean.Stat.Sample.Stratified.TreatmentRegression.Occupancy

/-! # Uniform lower tail for within-cell treatment variation

The conditional Gram identity and uniform occupancy bound imply mean Gram at
least epsilon(1-epsilon)n/4 for n≥2 and at most n available cells. Replacing a
coordinate changes the Gram by at most one. McDiarmid gives an exponential
lower tail, weakened to an explicit 1/n bound valid for every positive n.
The n=1 case uses probability≤1 and the explicit constant, since its Gram is zero.

Primary formal reference: [FoML McDiarmid](https://github.com/auto-res/lean-rademacher/blob/main/FoML/Probability/McDiarmid.lean),
re-exported by Causalean.Stat.Concentration.TailBounds.McDiarmid. Its lower-tail
theorem uses a nonnegative deviation and t times the sum of squared oscillations
at most one; here the oscillations are one and t=1/n.
-/

@[expose] public section

noncomputable section

namespace Causalean.Stat.Sample.Stratified.TreatmentRegression

open MeasureTheory Set
open scoped BigOperators

/-- [The good-design Gram threshold per observation](goal) at [overlap margin ε](hyp:epsilon) is
ε(1 − ε)/8. -/
def gramThreshold (epsilon : ℝ) : ℝ := epsilon * (1 - epsilon) / 8

/-- [The uniform Gram lower-tail constant](goal) at [overlap margin ε](hyp:epsilon) is the
reciprocal of twice the squared good-design threshold, 1/(2·(ε(1 − ε)/8)²). -/
def gramTailConstant (epsilon : ℝ) : ℝ := 1 / (2 * gramThreshold epsilon ^ 2)

variable {κ : Type*} [Fintype κ] [DecidableEq κ]
  [MeasurableSpace κ] [MeasurableSingletonClass κ]

/-- Let the design be [n iid draws from a joint probability law ν of a cell and a Boolean
treatment](hyp:n,ν). If [there are at least two observations](hyp:hn),
[the number of cells is at most n](hyp:hcard), [the overlap margin ε is
positive](hyp:epsilon,hepsilon) and [at most one half](hyp:hhalf), and [every cell of positive
probability has propensity between ε and 1 − ε](hyp:hoverlap), then [the expected Gram
denominator is at least twice the good-design threshold times n, that is
ε(1 − ε)n/4](goal).

Sum integral_gram_labelFiber over label vectors, discarding zero-weight
fibers before applying overlap; transport repeatCount to the cell marginal
and apply integral_repeatCount_lower.
@isnad1 id=le.5h4v.s7.8325d202a45f from=translated src=- shape=5c1d65b4 vocab=6be8858e
-/
theorem integral_gram_lower (n : ℕ) (ν : Measure (κ × Bool)) [IsProbabilityMeasure ν]
    (hn : 2 ≤ n) (hcard : Fintype.card κ ≤ n)
    (epsilon : ℝ) (hepsilon : 0 < epsilon) (hhalf : epsilon ≤ 1 / 2)
    (hoverlap : ∀ k, 0 < cellProbability ν k →
      epsilon ≤ propensity ν k ∧ propensity ν k ≤ 1 - epsilon) :
    2 * gramThreshold epsilon * n ≤ ∫ d : Fin n → κ × Bool, gram d
      ∂Measure.pi (fun _ : Fin n => ν) := by
  classical
  let P := Measure.pi (fun _ : Fin n => ν)
  let Q := ν.map Prod.fst
  have hQ : IsProbabilityMeasure Q := Measure.isProbabilityMeasure_map measurable_fst.aemeasurable
  have hfiber (F : (Fin n → κ × Bool) → ℝ) :
      (∫ d, F d ∂P) = ∑ x : Fin n → κ, ∫ d in labelFiber x, F d ∂P := by
    simp_rw [← integral_indicator (Set.to_countable _ |>.measurableSet)]
    rw [← integral_finsetSum _ (fun _ _ => Integrable.of_finite)]
    apply integral_congr_ae
    filter_upwards with d
    have hx (x : Fin n → κ) : d ∈ labelFiber x ↔ x = fun i => (d i).1 := by
      simp only [labelFiber, mem_ofPred_eq]
      exact ⟨fun h => funext (fun i => (h i).symm), fun h i => congrFun h.symm i⟩
    simp [Set.indicator, hx]
  have hmass (k : κ) : (Q {k}).toReal = cellProbability ν k := by
    dsimp only [Q]
    rw [Measure.map_apply measurable_fst (measurableSet_singleton k)]
    rfl
  have hrepeat :
      (∫ x : Fin n → κ, (repeatCount x : ℝ) ∂Measure.pi (fun _ : Fin n => Q)) =
        ∑ x : Fin n → κ, labelWeight ν x * (repeatCount x : ℝ) := by
    rw [integral_fintype Integrable.of_finite]
    simp [Measure.real, Measure.pi_singleton, ENNReal.toReal_prod, hmass, labelWeight]
  have hlower (x : Fin n → κ) :
      epsilon * (1 - epsilon) * (labelWeight ν x * (repeatCount x : ℝ)) ≤
        ∫ d in labelFiber x, gram d ∂P := by
    have hw : 0 ≤ labelWeight ν x := Finset.prod_nonneg (fun _ _ => ENNReal.toReal_nonneg)
    by_cases hx : 0 < labelWeight ν x
    · have h := conditional_gram_mean_lower n ν x hx epsilon hepsilon hhalf hoverlap
      have h' := (le_div_iff₀ hx).mp h
      simpa [P, mul_assoc, mul_left_comm, mul_comm] using h'
    · have hz : labelWeight ν x = 0 := le_antisymm (le_of_not_gt hx) hw
      simp [P, integral_gram_labelFiber, hz]
  have hoc := integral_repeatCount_lower n Q hn hcard
  have hp : 0 ≤ epsilon * (1 - epsilon) := mul_nonneg hepsilon.le (by linarith)
  calc
    2 * gramThreshold epsilon * n = epsilon * (1 - epsilon) * ((n : ℝ) / 4) := by
      unfold gramThreshold
      ring
    _ ≤ epsilon * (1 - epsilon) *
        (∫ x : Fin n → κ, (repeatCount x : ℝ) ∂Measure.pi (fun _ : Fin n => Q)) :=
      mul_le_mul_of_nonneg_left hoc hp
    _ = ∑ x : Fin n → κ, epsilon * (1 - epsilon) *
        (labelWeight ν x * (repeatCount x : ℝ)) := by rw [hrepeat, Finset.mul_sum]
    _ ≤ ∑ x : Fin n → κ, ∫ d in labelFiber x, gram d ∂P :=
      Finset.sum_le_sum (fun x _ => hlower x)
    _ = ∫ d, gram d ∂P := (hfiber gram).symm

variable {Ω : Type*} [MeasurableSpace Ω]

end Causalean.Stat.Sample.Stratified.TreatmentRegression
