module
public import Tengoku.Causalean.Causalean.Mathlib.MeasureTheory.WithDensityTransport
public import Tengoku.Causalean.Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection.ThreeBlockFactorization

/-!
# Conditional independence as density factorization

This module gives the three product-density factorization characterizations needed by the
intersection proof.  They deliberately use the same canonical four-block product measure, so
the subsequent splicing argument does not have to transport almost-everywhere statements across
ad hoc reorderings.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

noncomputable section

namespace Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection

universe uX uY uV uZ

private def permXV [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace V] [MeasurableSpace Z] :
    (X × (V × (Y × Z))) ≃ᵐ (X × (Y × (V × Z))) where
  toFun q := (q.1, (q.2.2.1, (q.2.1, q.2.2.2)))
  invFun q := (q.1, (q.2.2.1, (q.2.1, q.2.2.2)))
  left_inv q := by cases q with | mk x r => cases r with | mk v r => cases r <;> rfl
  right_inv q := by cases q with | mk x r => cases r with | mk y r => cases r <;> rfl
  measurable_toFun := by
    change Measurable (fun q : X × (V × (Y × Z)) ↦ (q.1, (q.2.2.1, (q.2.1, q.2.2.2))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun q : X × (Y × (V × Z)) ↦ (q.1, (q.2.2.1, (q.2.1, q.2.2.2))))
    fun_prop

private def assocYV [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSpace V] [MeasurableSpace Z] :
    (X × ((Y × V) × Z)) ≃ᵐ (X × (Y × (V × Z))) where
  toFun q := (q.1, (q.2.1.1, (q.2.1.2, q.2.2)))
  invFun q := (q.1, ((q.2.1, q.2.2.1), q.2.2.2))
  left_inv q := by cases q with | mk x r => cases r with | mk yv z => cases yv <;> rfl
  right_inv q := by cases q with | mk x r => cases r with | mk y vz => cases vz <;> rfl
  measurable_toFun := by
    change Measurable (fun q : X × ((Y × V) × Z) ↦ (q.1, (q.2.1.1, (q.2.1.2, q.2.2))))
    fun_prop
  measurable_invFun := by
    change Measurable (fun q : X × (Y × (V × Z)) ↦ (q.1, ((q.2.1, q.2.2.1), q.2.2.2)))
    fun_prop

variable {X : Type uX} {Y : Type uY} {V : Type uV} {Z : Type uZ}
variable [MeasurableSpace X] [MeasurableSpace Y] [MeasurableSpace V] [MeasurableSpace Z]
variable [StandardBorelSpace X] [StandardBorelSpace Y]
  [StandardBorelSpace V] [StandardBorelSpace Z]
variable (μX : Measure X) (μY : Measure Y) (μV : Measure V) (μZ : Measure Z)
variable [SigmaFinite μX] [SigmaFinite μY] [SigmaFinite μV] [SigmaFinite μZ]
variable {d : FourBlock X Y V Z → ℝ≥0∞}
variable [IsFiniteMeasure ((fourBlockReference μX μY μV μZ).withDensity d)]

end Causalean.Mathlib.Probability.Independence.Conditional.DensityIntersection
