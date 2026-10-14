import Tengoku

open Filter MeasureTheory ProbabilityTheory
open scoped ENNReal Topology

namespace FormalSLT.Probability.BorelCantelli

/--
Borel-Cantelli lemma, limsup-measure-zero form.

This is a claim-facing thin wrapper around mathlib's
`MeasureTheory.measure_limsup_atTop_eq_zero`. The statement matches the
TheoremPath claim's "$A_n$ infinitely often has probability zero" formulation
by representing "infinitely often" as `Filter.limsup A Filter.atTop`.
Claim-facing wrapper for theorempath.com evidence entry `claim:measure-theoretic-probability::borel-cantelli-first`.
@isnad1 id=eq.1h3v.s6.fbd74f0ac00e from=translated src=- shape=201fbe7d vocab=8c65daa3
-/
theorem borelCantelliFirstLimsupMeasureZero
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : ℕ → Set Ω}
    (hSummable : (∑' n, μ (A n)) ≠ ∞) :
    μ (Filter.limsup A Filter.atTop) = 0 :=
  MeasureTheory.measure_limsup_atTop_eq_zero hSummable

/--
Borel-Cantelli lemma, eventually-not-in form.

This companion wrapper captures the prose consequence: almost every outcome
belongs to finitely many of the events.
@isnad1 id=eventual.1h3v.s6.9c27a3dc65f4 from=translated src=- shape=0ed2f771 vocab=73d31bac
-/
theorem borelCantelliFirstEventuallyNotMem
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {A : ℕ → Set Ω}
    (hSummable : (∑' n, μ (A n)) ≠ ∞) :
    ∀ᵐ ω ∂μ, ∀ᶠ n in Filter.atTop, ω ∉ A n :=
  MeasureTheory.ae_eventually_notMem hSummable

/--
Second Borel-Cantelli lemma, independent-events limsup-measure-one form.

Scope note: mathlib states this wrapper with `iIndepSet`, which is stronger
than the governed claim's pairwise-independence wording. The manifest marks
this as scoped support until the pairwise version is formalized.
Claim-facing wrapper for theorempath.com evidence entry `claim:measure-theoretic-probability::borel-cantelli-second`.
@isnad1 id=eq.3h3v.s6.16f037871c47 from=translated src=- shape=2f1864ad vocab=1428162a
-/
theorem borelCantelliSecondIndependentLimsupMeasureOne
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {A : ℕ → Set Ω}
    (hMeasurable : ∀ n, MeasurableSet (A n))
    (hIndependent : iIndepSet A μ)
    (hDivergent : (∑' n, μ (A n)) = ∞) :
    μ (Filter.limsup A Filter.atTop) = 1 :=
  ProbabilityTheory.measure_limsup_eq_one hMeasurable hIndependent hDivergent

end FormalSLT.Probability.BorelCantelli
