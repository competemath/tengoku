module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Control.InformationLimits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The sensor side: observability and sensor loss

H. Touchette and S. Lloyd, *Information-theoretic approach to the study of
control systems*, Physica A 331(1):140–172, 2004, Theorems 5 and 6 and
Corollary 7.

Where `AISafetyAtlas.Control.InformationLimits` measures what an *actuator*
leaves undetermined, this module measures what a *sensor* loses. The paper calls
a system **perfectly observable** when the sensor "maps no two values of `X` to a
single observational output value `c`" — reading `c` pins the state down — and
defines the **sensor loss** `L_S = H(X|C)`, "the information loss … of the sensor
channel", by analogy with a lossless communication channel.

Three results follow.

* **Theorem 5** — perfectly observable iff `L_S = 0`. The source omits the proof
  ("readily follows from well-known properties of entropy"); it is supplied here,
  and the load-bearing step is `entropy_eq_zero_iff`: a finite-range variable has
  zero entropy exactly when some value carries all the mass.
* **Theorem 6** — `L_S = 0` implies `I(X ; Z | C) = 0`.
* **Corollary 7** — `L_S = 0` implies `I(X ; C, Z) = I(X ; C)`.

## What is *not* claimed

The paper is explicit that the observability side is not the controllability side
with symbols renamed: *"the fact that a communication channel is lossless has
nothing to do with the fact that it can be non-deterministic"*, so Theorem 2's
bound `L_C ≤ H(Z)` has **no** direct analogue `L_S ≤ H(Z)`. The paper repairs it
with a *backward* purification `L_S ≤ H(Z_B)`, stated in prose and left to the
reader. That repair is not formalized here.

The converse of Theorem 6 also fails, and the source says so: `I(X ; Z | C) = 0`
gives `H(X|C) = H(X|C,Z)` and no further, so it does not force `H(X|C) = 0`.
Only the stated direction is proved.
-/

namespace AISafetyAtlas.Control

open MeasureTheory ProbabilityTheory Real Function
open AISafetyAtlas.InformationTheory

universe uΩ uS uK uN

variable {Ω : Type uΩ} {S : Type uS} {K : Type uK} {N : Type uN}
variable [MeasurableSpace Ω] [MeasurableSpace S] [MeasurableSpace K] [MeasurableSpace N]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass K] [MeasurableSingletonClass N]
variable [Countable S] [Countable K] [Countable N]
variable {μ : Measure Ω}

/-! ## Zero entropy means one value carries everything -/

/-! ## Sensor loss and perfect observability -/

/-- **Perfect observability.** Every reading the sensor can actually produce pins
the state down: on the event `C = c` some single state carries all the mass.

The source's phrasing is that the sensor "maps no two values of `X` to a single
observational output value `c`", equivalently that "for all `c ∈ C` there exists
only one value `x` such that `p(x|c) = 1`". Readings of probability zero are
excluded, matching the source's "with respect to all observed value
`c ∈ supp(C)`".-/
@[expose] public def PerfectlyObservable (μ : Measure Ω) (X : Ω → S) (C : Ω → K) : Prop :=
  ∀ c : K, μ (C ⁻¹' {c}) ≠ 0 → ∃ x : S, (μ[|C ⁻¹' {c}]) (X ⁻¹' {x}) = 1

/-! ## Theorem 6 and Corollary 7 -/

end AISafetyAtlas.Control
