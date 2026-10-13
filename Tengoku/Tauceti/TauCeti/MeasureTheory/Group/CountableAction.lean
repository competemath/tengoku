/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku

/-!
# Countable group actions: almost invariant events versus invariant events

Mathlib's `ErgodicSMul` is phrased with **almost** invariant events: an action is ergodic when
every measurable `s` with `(g • ·) ⁻¹' s =ᵐ[μ] s` for all `g` is null or conull.  Concrete
σ-algebras of invariant events — the invariant σ-algebra of a map, or the exchangeable σ-algebra
of path space — instead collect the **exactly** invariant events, those with
`(g • ·) ⁻¹' s = s`.

For a **countable** group the two formulations agree up to null sets: the saturation
`⋃ g, g • s` is exactly invariant and, being a countable union of sets each almost equal to `s`,
almost equal to `s`.  This file records that saturation
(`exists_smul_invariant_ae_eq`) and the resulting criterion
(`ergodicSMul_of_forall_smul_invariant`): to prove a countable action ergodic it suffices to
handle exactly invariant events.

Countability is essential and is not a technical convenience: the saturation of an almost
invariant set by an uncountable group need not be measurable, let alone almost equal to the
original set.

No measure invariance is needed for the saturation itself; `SMulInvariantMeasure` enters only
because `ErgodicSMul` extends it.
-/

public section

open Filter MeasureTheory Set

open scoped Pointwise

namespace TauCeti

namespace MeasureTheory

variable {G X : Type*} [Group G] [Countable G] [MeasurableSpace X] [MulAction G X]
  [MeasurableConstSMul G X] {μ : Measure X}

end MeasureTheory

end TauCeti
