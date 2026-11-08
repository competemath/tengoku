module

public import Tengoku.Seed.Data.Nat.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Deterministic symmetry obstruction

This is the inductive core of Angluin's anonymous-network leader-election
impossibility (*Local and global properties in networks of processors*, STOC
1980): nodes with indistinguishable observations and identical deterministic
transition code remain indistinguishable, so a configuration with exactly one
leader cannot be reached.

The module isolates the symmetry argument rather than claiming Angluin's full
network/view theory.  Randomness, identifiers, asymmetric initial states, and
asymmetric observations are intentionally outside the hypotheses.
-/

namespace AISafetyAtlas.Compositional.Symmetry

/-- All nodes have the same local state.-/
@[expose] public def IsSymmetric {Node State : Type*}
    (configuration : Node → State) : Prop :=
  ∀ i j, configuration i = configuration j

/-- The node type contains two distinct nodes.-/
@[expose] public def HasAtLeastTwo (Node : Type*) : Prop :=
  ∃ i j : Node, i ≠ j

/-- Exactly one node's state satisfies the leader predicate.-/
@[expose] public def HasUniqueLeader {Node State : Type*}
    (leader : State → Prop) (configuration : Node → State) : Prop :=
  ∃ i, leader (configuration i) ∧
    ∀ j, leader (configuration j) → j = i

/--
An anonymous deterministic synchronous protocol.

The observation interface may contain arbitrary network structure.  The sole
anonymity premise used by the theorem is explicit: a symmetric configuration
gives every node the same observation.  `decide` is shared deterministic code.-/
public structure Protocol (Node State Observation : Type*) where
  observe : (Node → State) → Node → Observation
  decide : Observation → State
  symmetric_observation :
    ∀ c, IsSymmetric c → ∀ i j, observe c i = observe c j

namespace Protocol

variable {Node State Observation : Type*}

/-- One synchronous protocol round.-/
@[expose] public def step (P : Protocol Node State Observation)
    (c : Node → State) : Node → State :=
  fun i => P.decide (P.observe c i)

/-- Execute `rounds` synchronous rounds.-/
@[expose] public def run (P : Protocol Node State Observation) :
    ℕ → (Node → State) → Node → State
  | 0, c => c
  | n + 1, c => P.step (P.run n c)

end Protocol
end AISafetyAtlas.Compositional.Symmetry
