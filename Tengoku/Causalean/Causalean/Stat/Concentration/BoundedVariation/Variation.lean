module
public import Tengoku

/-!
# Continuous paths of bounded variation

This module fixes the compact time interval, the path norm and total variation,
and a continuous cumulative-variation control used in continuum chaining.
-/

@[expose] public section

open MeasureTheory

namespace Causalean.Stat.Concentration.BoundedVariation

/-- [The time domain](goal) is [the closed real interval from zero to
one](step:1).
-/
abbrev Time : Type := Set.Icc (0 : ℝ) 1

/-- [A path](goal) is [a continuous real-valued function on the closed
unit time interval](step:1).
-/
abbrev Path : Type := C(Time, ℝ)

/-- [The σ-algebra on continuous paths](goal) is [the Borel σ-algebra of
the uniform-norm topology](step:1).
-/
noncomputable instance : MeasurableSpace Path := borel Path

/-- [The left endpoint of the time interval](goal) is [the time
0](step:1).
-/
def timeZero : Time := ⟨0, by constructor <;> norm_num⟩

/-- [The right endpoint of the time interval](goal) is [the time
1](step:1).
-/
def timeOne : Time := ⟨1, by constructor <;> norm_num⟩

/-- [The total variation](goal) of [a continuous path f](hyp:f) is [its
extended total variation over the unit interval, converted to a real
number](step:1).

For a bounded-variation path this is its ordinary total variation; a path
of infinite variation is assigned the value 0.
-/
noncomputable def pathTV (f : Path) : ℝ := (eVariationOn f Set.univ).toReal

/-- [The size](goal) of [a continuous path f](hyp:f) is [its supremum
norm plus its total variation](step:1).
-/
noncomputable def pathSize (f : Path) : ℝ := ‖f‖ + pathTV f

/-- [The real-valued total variation of every path is
nonnegative](goal).
@isnad1 id=le.0h1v.s3.16a9e3b692ee from=translated src=- shape=b9369acb vocab=15142bd8
-/
theorem pathTV_nonneg (f : Path) : 0 ≤ pathTV f := by
  exact ENNReal.toReal_nonneg

/-- [The supremum-plus-variation size of every path is
nonnegative](goal).
@isnad1 id=le.0h1v.s3.a2f52ac6b79d from=translated src=- shape=b9369acb vocab=66e00aad
-/
theorem pathSize_nonneg (f : Path) : 0 ≤ pathSize f := by
  exact add_nonneg (norm_nonneg _) (pathTV_nonneg f)

end Causalean.Stat.Concentration.BoundedVariation
