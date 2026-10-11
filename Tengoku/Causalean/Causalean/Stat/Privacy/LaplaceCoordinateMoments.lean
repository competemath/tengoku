module
public import Tengoku.Causalean.Causalean.Stat.Privacy.LaplaceMean
public import Tengoku.Causalean.Causalean.Stat.Privacy.LaplaceSecondMoment

/-!
# Finite-coordinate Laplace release moments

Every centered coordinate of the existing finite-product mechanism has the
scalar Laplace law, zero mean, and exact squared error. An arbitrary real
center yields query displacement squared plus twice the squared noise scale.
The index type is any finite type, including `Fin 2`.
-/

public section

namespace Causalean.Stat.Privacy

open MeasureTheory Causalean.Stat.Privacy
open scoped ENNReal

variable {D ι : Type*} [Fintype ι]

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [an input](hyp:d), and [a coordinate](hyp:i), [subtracting the
query from the released coordinate gives exactly the centered scalar Laplace law](goal).

Unfold the mechanism, compose measurable maps, cancel the query shift, and
use `measurePreserving_eval` with the probability normalization of every factor.
No measurability of the query is needed at a fixed input.

Install `laplaceMeasure_isProbabilityMeasure b hb` as a local instance before
using `measurePreserving_eval (fun _ : ι => laplaceMeasure b) i`. Its
`map_eq` field identifies the evaluation pushforward. `Measure.map_map`
reduces the release pushforward to that evaluation map; pointwise cancellation
is `Pi.add_apply` followed by `add_sub_cancel_right`.
@isnad1 id=eq.1h6v.s6.7edea38b8810 from=translated src=- shape=be7b90f0 vocab=3f206408
-/
theorem laplaceMechPi_map_centered_coord (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (d : D) (i : ι) :
    (laplaceMechPi b q d).map (fun y => y i - q d i) = laplaceMeasure b := by
  let : IsProbabilityMeasure (laplaceMeasure b) :=
    laplaceMeasure_isProbabilityMeasure b hb
  rw [laplaceMechPi, Measure.map_map (by fun_prop) (by fun_prop)]
  have hcancel : (fun y : ι → ℝ => y i - q d i) ∘
      (fun z => z + q d) = Function.eval i := by
    funext z
    simp [Pi.add_apply]
  rw [hcancel]
  exact (measurePreserving_eval (fun _ : ι => laplaceMeasure b) i).map_eq

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [an input](hyp:d), and [a coordinate](hyp:i), [the released-coordinate
error is integrable](goal).

Rewrite the scalar integrability theorem through
`laplaceMechPi_map_centered_coord`, then apply `integrable_map_measure`
with the measurable centered evaluation map and the scalar identity function.
@isnad1 id=integrab.1h6v.s6.d5a3bfb01e93 from=translated src=- shape=8bcfc872 vocab=f3c02b4d
-/
theorem laplaceMechPi_integrable_centered_coord (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (d : D) (i : ι) :
    Integrable (fun y => y i - q d i) (laplaceMechPi b q d) := by
  have h : Integrable (fun x : ℝ => x)
      ((laplaceMechPi b q d).map (fun y => y i - q d i)) := by
    rw [laplaceMechPi_map_centered_coord b hb q d i]
    exact laplaceMeasure_integrable_id b hb
  exact (integrable_map_measure h.aestronglyMeasurable
    ((measurable_pi_apply i).sub measurable_const).aemeasurable).mp h

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [an input](hyp:d), and [a coordinate](hyp:i), [the released-coordinate
error has mean zero](goal).

Use `integral_map` with the centered evaluation map, rewrite its pushforward
using `laplaceMechPi_map_centered_coord`, and reuse the scalar zero mean.
@isnad1 id=eq.1h6v.s6.60b6bccd0888 from=translated src=- shape=48735a34 vocab=6bde09dc
-/
theorem laplaceMechPi_integral_centered_coord (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (d : D) (i : ι) :
    ∫ y, y i - q d i ∂laplaceMechPi b q d = 0 := by
  have hmap := integral_map (μ := laplaceMechPi b q d)
    (φ := fun y => y i - q d i) (f := fun x : ℝ => x)
    ((measurable_pi_apply i).sub measurable_const).aemeasurable (by fun_prop)
  rw [laplaceMechPi_map_centered_coord b hb q d i,
    laplaceMeasure_integral_id b hb] at hmap
  exact hmap.symm

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [an input](hyp:d), and [a coordinate](hyp:i), [the squared released-coordinate
error is integrable](goal).

Use the same `integrable_map_measure` transfer as for the first moment,
now with the scalar square and `laplaceMeasure_integrable_sq`.
@isnad1 id=integrab.1h6v.s6.53d4e27c8721 from=translated src=- shape=0c3b011e vocab=3cccadb2
-/
theorem laplaceMechPi_integrable_centered_coord_sq (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (d : D) (i : ι) :
    Integrable (fun y => (y i - q d i) ^ 2) (laplaceMechPi b q d) := by
  have h : Integrable (fun x : ℝ => x ^ 2)
      ((laplaceMechPi b q d).map (fun y => y i - q d i)) := by
    rw [laplaceMechPi_map_centered_coord b hb q d i]
    exact laplaceMeasure_integrable_sq b hb
  exact (integrable_map_measure h.aestronglyMeasurable
    ((measurable_pi_apply i).sub measurable_const).aemeasurable).mp h

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [an input](hyp:d), and [a coordinate](hyp:i), [the squared released-coordinate
error has expectation exactly twice the squared scale](goal).

Transfer `laplaceMeasure_integral_sq` using `integral_map`; this evaluates
the actual marginal law rather than introducing a moment assumption.
@isnad1 id=eq.1h6v.s7.dd3232878fa8 from=translated src=- shape=4fc3321c vocab=e777ca22
-/
theorem laplaceMechPi_integral_centered_coord_sq (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (d : D) (i : ι) :
    ∫ y, (y i - q d i) ^ 2 ∂laplaceMechPi b q d = 2 * b ^ 2 := by
  have hmap := integral_map (μ := laplaceMechPi b q d)
    (φ := fun y => y i - q d i) (f := fun x : ℝ => x ^ 2)
    ((measurable_pi_apply i).sub measurable_const).aemeasurable (by fun_prop)
  rw [laplaceMechPi_map_centered_coord b hb q d i,
    laplaceMeasure_integral_sq b hb] at hmap
  exact hmap.symm

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [an input](hyp:d), and [a coordinate](hyp:i), [the squared released-coordinate
error has nonnegative extended expectation exactly twice the squared scale](goal).
@isnad1 id=eq.1h6v.s6.86e5361aceaa from=translated src=- shape=38e14833 vocab=3867f264
-/
theorem laplaceMechPi_lintegral_centered_coord_sq (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (d : D) (i : ι) :
    ∫⁻ y, ENNReal.ofReal ((y i - q d i) ^ 2) ∂laplaceMechPi b q d =
      ENNReal.ofReal (2 * b ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (laplaceMechPi_integrable_centered_coord_sq b hb q d i)
    (ae_of_all _ fun y => sq_nonneg (y i - q d i)),
    laplaceMechPi_integral_centered_coord_sq b hb q d i]

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [an input](hyp:d), [a coordinate](hyp:i), and [a real center](hyp:c),
[the released coordinate's squared displacement from that center is integrable](goal).

Expand around `q d i`; the square, linear error, and constant terms are
integrable under the normalized release law.

Install `laplaceMechPi_isProbabilityMeasure b hb q d` locally. Combine the
two centered integrability lemmas with `Integrable.const_mul`,
`integrable_const`, and `Integrable.add`, then identify the expansion by `ring`.
@isnad1 id=integrab.1h7v.s6.b4d72d139d0e from=translated src=- shape=4bb78b99 vocab=3cccadb2
-/
theorem laplaceMechPi_integrable_coord_sub_sq (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (d : D) (i : ι) (c : ℝ) :
    Integrable (fun y => (y i - c) ^ 2) (laplaceMechPi b q d) := by
  let := laplaceMechPi_isProbabilityMeasure b hb q d
  have hsq := laplaceMechPi_integrable_centered_coord_sq b hb q d i
  have hlin := (laplaceMechPi_integrable_centered_coord b hb q d i).const_mul
    (2 * (q d i - c))
  have hconst : Integrable (fun _ : ι → ℝ => (q d i - c) ^ 2)
      (laplaceMechPi b q d) := integrable_const _
  refine ((hsq.add hlin).add hconst).congr (ae_of_all _ fun y => ?_)
  dsimp
  ring

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [an input](hyp:d), [a coordinate](hyp:i), and [a real center](hyp:c),
[the released coordinate's squared displacement has expectation equal to the query's squared
displacement plus twice the squared scale](goal).

Expand `(y i - c)^2` into centered noise squared, the cross term, and query
displacement squared. The exact centered mean cancels the cross term.

Use `integral_add` with the established integrability obligations before
`integral_const_mul` and `integral_const`. Probability normalization makes
the constant term its own integral; `ring` orders the final two terms.
@isnad1 id=eq.1h7v.s7.f4a04adcebd0 from=translated src=- shape=910584cd vocab=0cfb3ac6
-/
theorem laplaceMechPi_integral_coord_sub_sq (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (d : D) (i : ι) (c : ℝ) :
    ∫ y, (y i - c) ^ 2 ∂laplaceMechPi b q d = (q d i - c) ^ 2 + 2 * b ^ 2 := by
  let := laplaceMechPi_isProbabilityMeasure b hb q d
  have hsq := laplaceMechPi_integrable_centered_coord_sq b hb q d i
  have hlin := (laplaceMechPi_integrable_centered_coord b hb q d i).const_mul
    (2 * (q d i - c))
  have hconst : Integrable (fun _ : ι → ℝ => (q d i - c) ^ 2)
      (laplaceMechPi b q d) := integrable_const _
  have hexpand : (fun y : ι → ℝ => (y i - c) ^ 2) =
      fun y => ((y i - q d i) ^ 2 + 2 * (q d i - c) * (y i - q d i)) +
        (q d i - c) ^ 2 := by
    funext y
    ring
  have hsum : Integrable
      (fun y : ι → ℝ => (y i - q d i) ^ 2 +
        2 * (q d i - c) * (y i - q d i)) (laplaceMechPi b q d) := hsq.add hlin
  rw [hexpand, integral_add hsum hconst, integral_add hsq hlin,
    integral_const_mul, laplaceMechPi_integral_centered_coord_sq b hb q d i,
    laplaceMechPi_integral_centered_coord b hb q d i, integral_const]
  simp
  ring

/-- At [a real scale](hyp:b) with [a positive-scale certificate](hyp:hb), [a
query](hyp:q), [an input](hyp:d), [a coordinate](hyp:i), and [a real center](hyp:c),
[the released coordinate's squared displacement has the corresponding exact nonnegative
extended moment](goal).
@isnad1 id=eq.1h7v.s7.85c18a88fd3d from=translated src=- shape=b59c1ac9 vocab=fa207c9b
-/
theorem laplaceMechPi_lintegral_coord_sub_sq (b : ℝ) (hb : 0 < b)
    (q : D → ι → ℝ) (d : D) (i : ι) (c : ℝ) :
    ∫⁻ y, ENNReal.ofReal ((y i - c) ^ 2) ∂laplaceMechPi b q d =
      ENNReal.ofReal ((q d i - c) ^ 2 + 2 * b ^ 2) := by
  rw [← ofReal_integral_eq_lintegral_ofReal
    (laplaceMechPi_integrable_coord_sub_sq b hb q d i c)
    (ae_of_all _ fun y => sq_nonneg (y i - c)),
    laplaceMechPi_integral_coord_sub_sq b hb q d i c]

end Causalean.Stat.Privacy
