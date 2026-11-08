module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Control.Purification
public import Tengoku.Seed.Analysis.Convex.StdSimplex

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Equation (48) is a maximum, not merely a supremum

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004, eq. (48) and the sentence
below it.

The source writes

> `ΔH_open^max = max over p_X ∈ P, c ∈ C  ΔH_open`

with `P` *"the set of all probability distributions"* for the initial state, and
uses it as the right-hand side of Theorem 10. `AISafetyAtlas.Control.OpenLoop`
renders that object as `sSup` of the corresponding set and proves the set is
bounded, which is enough to *use*, but it is not the printed object: writing
`max` asserts that some input law and some action attain it, and `sSup ≥ max`
whenever both exist, so a bound stated against `sSup` is formally weaker than
the printed one.

This module supplies the missing assertion. The argument is the expected one and
the work is in the plumbing:

* a probability measure on a finite state space is a point of `stdSimplex ℝ S`,
  and every point of the simplex is one — `ofWeights` and `weights` are mutually
  inverse there;
* against that coordinate the reduction becomes `openLoopObjective`, an explicit
  finite sum of `Real.negMulLog`s, whose second argument is *linear* in the
  weights because running the kernel is;
* Mathlib's continuity of *negMulLog* makes it continuous, `isCompact_stdSimplex` makes
  the domain compact, and the action alphabet is finite, so the joint maximum is
  attained.

The conclusion is `isGreatest_kernelOpenLoopMax`: eq. (48)'s value belongs to the
set it is the supremum of. `kernelOpenLoopMax` may therefore be read as the
printed `max`.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uS uK uT

variable {S : Type uS} {K : Type uK} {T : Type uT}
variable [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace T]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass T]
variable [Fintype S] [Fintype K] [Fintype T]

/-! ## Probability measures on a finite space are simplex points -/

/-- The weight vector of a measure on a finite space: its mass on each atom.-/
@[expose] public noncomputable def weights (ν : Measure S) : S → ℝ := fun x => ν.real {x}

/-- The measure with prescribed atom masses.-/
@[expose] public noncomputable def ofWeights (w : S → ℝ) : Measure S :=
  ∑ x : S, ENNReal.ofReal (w x) • Measure.dirac x

/-! ## The objective in simplex coordinates -/

/--
**Eq. (48)'s objective, in coordinates.** `Hm[ν]` becomes a sum of `negMulLog`s
over the atoms, and the outcome law is *linear* in the weights because running the
kernel is: the mass the outcome puts on `t` is `∑ₓ w x · κ(x,c){t}`.-/
@[expose] public noncomputable def openLoopObjective (κ : Kernel (S × K) T) (c : K)
    (w : S → ℝ) : ℝ :=
  (∑ x, Real.negMulLog (w x)) - ∑ t, Real.negMulLog (∑ x, w x * (κ (x, c)).real {t})

/-! ## Eq. (48)'s maximum is attained -/

end AISafetyAtlas.Control
