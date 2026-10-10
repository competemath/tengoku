module

public import Tengoku.GibbsMeasure.GibbsMeasure.Mathlib.MeasureTheory.Function.SimpleFunc
public import Tengoku

public section

open ENNReal Function

namespace MeasureTheory
variable {α E : Type*} {mα : MeasurableSpace α} [NormedAddCommGroup E] {μ : Measure α}

-- TODO: Replace in mathlib

namespace SimpleFunc
variable {mα₀ : MeasurableSpace α}

end MeasureTheory.SimpleFunc
