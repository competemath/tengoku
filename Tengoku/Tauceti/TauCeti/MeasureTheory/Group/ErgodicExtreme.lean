/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.MeasureTheory.Group.Action
public import Tengoku.Tauceti.TauCeti.MeasureTheory.Group.CountableAction
import Tengoku.Tauceti.TauCeti.MeasureTheory.Measure.ProbabilityMeasure.Coding

/-!
# Ergodic group actions and extreme invariant measures

For a countable group `G` acting measurably on `X`, an invariant measure of finite total mass is
ergodic if and only if it is an extreme point of the `G`-invariant measures of that total mass;
in particular an invariant probability measure is ergodic if and only if it is an extreme point of
the invariant measures of total mass one. This is the group-action form of Mathlib's
`Ergodic.iff_mem_extremePoints`, which concerns a single measure-preserving map.

Two general facts about an ergodic action carry the characterisation and are useful on their
own: an almost invariant function is almost everywhere constant
(`ErgodicSMul.ae_eq_const_of_forall_ae_eq_comp_smul₀`), and an invariant measure absolutely
continuous with respect to an ergodic one is a multiple of it
(`ErgodicSMul.eq_smul_of_absolutelyContinuous`). These, the invariant-measure set and the
forward direction of the characterisation need only an action by a type with a scalar
multiplication; the group and its countability enter only in the reverse direction, through the
saturation of an almost invariant event in `CountableAction.lean`.

Extremality also has an integral form: an ergodic probability measure written as a mixture
`κ ∘ₘ π` of almost surely invariant probability measures has almost every component equal to
itself (`ErgodicSMul.ae_eq_of_comp_eq`). This is what removes a global randomization parameter
from a functional representation of an ergodic law.

## Main results

* `TauCeti.MeasureTheory.invariantMeasuresOfMeasureUnivEq`, with its membership and convexity
  lemmas; the invariant probability measures are the case of total mass one
* `ErgodicSMul.ae_eq_const_of_forall_ae_eq_comp_smul₀`
* `ErgodicSMul.eq_smul_of_absolutelyContinuous`,
  `ErgodicSMul.eq_of_absolutelyContinuous_measure_univ_eq`, `ErgodicSMul.eq_of_absolutelyContinuous`
* `ErgodicSMul.iff_mem_extremePoints_measure_univ_eq`, `ErgodicSMul.iff_mem_extremePoints`
* `TauCeti.MeasureTheory.smulInvariantMeasure_comp`, `ErgodicSMul.ae_eq_of_comp_eq`: a mixture of
  invariant measures is invariant, and an ergodic probability measure written as such a mixture
  has almost every component equal to itself

## References

The proofs of `eq_smul_of_absolutelyContinuous`, `eq_of_absolutelyContinuous_measure_univ_eq`,
`mem_extremePoints_measure_univ_eq` and `of_mem_extremePoints_measure_univ_eq` are adapted from
Mathlib's `Mathlib/Dynamics/Ergodic/Extreme.lean` by Yury Kudryashov, transposed from a single
measure-preserving map to an action; `ae_eq_const_of_forall_ae_eq_comp_smul₀` follows
`PreErgodic.ae_eq_const_of_ae_eq_comp` in `Mathlib/Dynamics/Ergodic/Function.lean`. The same
argument for the sortwise relabelling action on relational structures appears in
`Graphon/RelErgodicExtreme.lean` of `cameronfreer/graphon` (Apache 2.0) at commit
`18d47ebb4155d32031090ec3412eb71583a94f69`.
-/

public section

open Filter Set Function MeasureTheory Measure ProbabilityTheory
open scoped ENNReal

/-! ### Invariant measures and ergodic actions of a scalar multiplication -/

namespace TauCeti.MeasureTheory

variable {G X : Type*} [SMul G X] {m : MeasurableSpace X} {ν : Measure X}

/-- The `G`-invariant measures on `X` of total mass `c`, a convex set of measures. -/
def invariantMeasuresOfMeasureUnivEq (G X : Type*) [SMul G X] [MeasurableSpace X] (c : ℝ≥0∞) :
    Set (Measure X) :=
  {ν | SMulInvariantMeasure G X ν ∧ ν univ = c}

/-- Membership in the invariant measures of total mass `c`. -/
@[simp]
theorem mem_invariantMeasuresOfMeasureUnivEq_iff {c : ℝ≥0∞} :
    ν ∈ invariantMeasuresOfMeasureUnivEq G X c ↔ SMulInvariantMeasure G X ν ∧ ν univ = c :=
  Iff.rfl

/-- The invariant measures of a fixed total mass form a convex set. -/
theorem convex_invariantMeasuresOfMeasureUnivEq {c : ℝ≥0∞} :
    Convex ℝ≥0∞ (invariantMeasuresOfMeasureUnivEq G X c) := by
  rintro ν₁ ⟨hν₁, hν₁u⟩ ν₂ ⟨hν₂, hν₂u⟩ a b _ _ hab
  refine ⟨inferInstance, ?_⟩
  simp [Measure.add_apply, Measure.smul_apply, hν₁u, hν₂u, ← add_mul, hab]

/-- **A mixture of invariant measures is invariant**: if almost every measure of the kernel `κ` is
`G`-invariant, then so is its mixture `κ ∘ₘ π`. The integral counterpart of the convexity of
`invariantMeasuresOfMeasureUnivEq`. -/
theorem smulInvariantMeasure_comp [MeasurableConstSMul G X] {Z : Type*} {mZ : MeasurableSpace Z}
    {π : Measure Z} {κ : Kernel Z X} (hκ : ∀ᵐ z ∂π, SMulInvariantMeasure G X (κ z)) :
    SMulInvariantMeasure G X (κ ∘ₘ π) :=
  ⟨fun c s hs => by
    rw [Measure.bind_apply hs κ.aemeasurable,
      Measure.bind_apply (measurable_const_smul c hs) κ.aemeasurable]
    exact lintegral_congr_ae (hκ.mono fun z hz => hz.measure_preimage_smul c hs)⟩

end TauCeti.MeasureTheory

namespace ErgodicSMul

open TauCeti.MeasureTheory

section SMul

variable {X : Type*} {m : MeasurableSpace X} {μ ν : Measure X}

end SMul

/-! ### The reverse direction, for a countable group action -/

section Group

variable {G X : Type*} [Group G] [Countable G] [MulAction G X] {m : MeasurableSpace X}
  [MeasurableConstSMul G X] {μ : Measure X}

end Group

/-! ### Integral decompositions of an ergodic measure -/

section Mixture

variable {G X Z : Type*} [SMul G X] {m : MeasurableSpace X} [MeasurableConstSMul G X]
  {mZ : MeasurableSpace Z} {μ : Measure X} {π : Measure Z} {κ : Kernel Z X}

end Mixture

end ErgodicSMul
