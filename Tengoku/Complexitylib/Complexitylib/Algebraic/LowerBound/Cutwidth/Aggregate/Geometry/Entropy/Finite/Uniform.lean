/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Aggregate.Geometry.Entropy.Finite
public import Tengoku

/-!+# Uniform changes of coordinates for finite weight certificates

An injective selection of Boolean coordinates is uniformly distributed. Splitting
the cube into selected and unused coordinates transports local certificates to
the full input cube without any independence hypotheses about other messages.
-/

@[expose] public section

namespace Algebraic.Cutwidth.Aggregate.Geometry.Entropy

open scoped BigOperators Classical

/-- Reindex the uniform source of a weight certificate by an equivalence. -/
noncomputable def WeightBound.precompEquiv {X X' Y : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] {key : X → Y} {cost : ℝ}
    (bound : WeightBound key cost) (e : X' ≃ X) : WeightBound (key ∘ e) cost where
  weight := bound.weight
  nonneg := bound.nonneg
  mass := bound.mass
  positive x := bound.positive (e x)
  log_bound := by
    change -(Fintype.card X' : ℝ) * cost ≤
      ∑ x, Real.log (bound.weight (key (e x)))
    rw [e.sum_comp (fun x => Real.log (bound.weight (key x))), Fintype.card_congr e]
    exact bound.log_bound

/-- Reindex the uniform source of a conditional certificate. -/
noncomputable def ConditionalWeightBound.precompEquiv {X X' Y Z : Type*}
    [Fintype X] [Fintype X'] [Fintype Y] {key : X → Y} {parent : X → Z} {cost : ℝ}
    (bound : ConditionalWeightBound key parent cost) (e : X' ≃ X) :
    ConditionalWeightBound (key ∘ e) (parent ∘ e) cost where
  weight := bound.weight
  nonneg := bound.nonneg
  mass := bound.mass
  positive x := bound.positive (e x)
  log_bound := by
    change -(Fintype.card X' : ℝ) * cost ≤
      ∑ x, Real.log (bound.weight (parent (e x)) (key (e x)))
    rw [e.sum_comp (fun x => Real.log (bound.weight (parent x) (key x))),
      Fintype.card_congr e]
    exact bound.log_bound

/-- Split a Boolean cube into injectively selected coordinates and their complement. -/
noncomputable def coordinateSplit {I V : Type*} (e : I ↪ V) :
    (V → Bool) ≃ (I → Bool) × ({v // v ∉ Set.range e} → Bool) :=
  (Equiv.piEquivPiSubtypeProd (fun v => v ∈ Set.range e) (fun _ => Bool)).trans
    (Equiv.prodCongr (Equiv.arrowCongr (Equiv.ofInjective e e.injective).symm
      (Equiv.refl Bool)) (Equiv.refl _))

@[simp] theorem coordinateSplit_fst {I V : Type*} (e : I ↪ V) (x : V → Bool) :
    (coordinateSplit e x).1 = x ∘ e := rfl

end Algebraic.Cutwidth.Aggregate.Geometry.Entropy
