import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.Combinatorics.CyclicBinaryTransitions
import Tengoku.Seed.CategoryTheory.FintypeCat
import Tengoku.Seed.Data.Set.Card.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fixed-strip balance from cyclic parametrizations

The fixed-strip argument groups quotient and reversed row-`F` packets into
finite cyclic binary systems.  Quotient packets are the false-to-true
transitions and reversed packets are the true-to-false transitions.  This
file packages precisely that reduction and derives an equivalence of the two
packet types from the elementary cyclic transition count.
-/

set_option autoImplicit false
noncomputable section

namespace QuotientSubmoduleEquidistribution.FixedStripCyclicBalance

universe u v w

/-- A false-to-true transition at `i` along the permutation `step`.-/
def IsRise {α : Type u} (step : α ≃ α) (bit : α → Bool)
    (i : α) : Prop :=
  bit (step.symm i) = false ∧ bit i = true

/-- A true-to-false transition after `i` along the permutation `step`.-/
def IsFall {α : Type u} (step : α ≃ α) (bit : α → Bool)
    (i : α) : Prop :=
  bit i = true ∧ bit (step i) = false

/-- Data identifying two packet families with rises and falls in a finite
family of cyclic binary systems.-/
structure Parametrization (QuotientPacket : Type u)
    (ReversePacket : Type v) where
  Context : FintypeCat.{w}
  Position : Context → FintypeCat.{w}
  step : ∀ c, Position c ≃ Position c
  bit : ∀ c, Position c → Bool
  quotientEquiv : QuotientPacket ≃
    Σ c : Context, {i : Position c // IsRise (step c) (bit c) i}
  reverseEquiv : ReversePacket ≃
    Σ c : Context, {i : Position c // IsFall (step c) (bit c) i}

namespace Parametrization

variable {QuotientPacket : Type u} {ReversePacket : Type v}
  (P : Parametrization.{u, v, w} QuotientPacket ReversePacket)

end Parametrization

end QuotientSubmoduleEquidistribution.FixedStripCyclicBalance
