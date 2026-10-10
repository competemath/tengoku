import Tengoku.Degiorgi.DeGiorgi.EllipticCoefficients

/-!
# Support: Measure Bounds

Shared measure-theoretic lemmas for essential suprema, essential infima, and
restricted ball measures used throughout the weak Harnack, Harnack, and Moser
Holder layers.
-/

noncomputable section

open MeasureTheory Filter Metric

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => AmbientSpace d

end DeGiorgi
