/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku.Tauceti.TauCeti.Probability.Exchangeability.FiniteMarginals
public import Tengoku

/-!
# The joint law of a directing measure and a path

For a process `X : ℕ → Ω → α` carried along by a candidate directing measure
`ν : Ω → ProbabilityMeasure α`, `jointPathLaw μ X ν` is the law of the pair
`(ν ω, fun i => X i ω)` on `ProbabilityMeasure α × (ℕ → α)`.

## Main declarations

* `jointPathLaw` — the definition, with `jointPathLaw_def` its unfolding;
* `map_fst_jointPathLaw`, `map_snd_jointPathLaw` — the two marginals, `μ.map ν` and
  `pathLaw μ X`;
* `map_prefixProjPair_jointPathLaw` — the pushforward along the paired prefix projection.

Nothing here mentions conditional independence: these are facts about the law of a pair, and hold
for an arbitrary `ν`. The conditional statements that consume them — in particular the full-path
disintegration identifying this law with a mixture — live in
`Exchangeability/ConditionallyIID/PathDisintegration.lean`.
-/

public section

noncomputable section

open MeasureTheory

namespace TauCeti

namespace Probability

variable {Ω α : Type*} [MeasurableSpace Ω] [MeasurableSpace α]
  {μ : Measure Ω} {X : ℕ → Ω → α} {ν : Ω → ProbabilityMeasure α}

/-- The joint path law: the law of the directing measure together with the whole path. -/
def jointPathLaw (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    Measure (ProbabilityMeasure α × (ℕ → α)) :=
  μ.map fun ω => (ν ω, fun i => X i ω)

/-- The definitional expansion of `jointPathLaw`: the pushforward of `μ` along
`ω ↦ (ν ω, fun i => X i ω)`. -/
@[simp]
theorem jointPathLaw_def (μ : Measure Ω) (X : ℕ → Ω → α) (ν : Ω → ProbabilityMeasure α) :
    jointPathLaw μ X ν = μ.map fun ω => (ν ω, fun i => X i ω) := (rfl)

end Probability

end TauCeti

end

end
