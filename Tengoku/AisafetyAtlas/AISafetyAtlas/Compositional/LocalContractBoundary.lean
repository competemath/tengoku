module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Compositional.Hyperproperties
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Compositional.Rectangularity
public import Tengoku.Seed.Data.Set.Basic
public import Tengoku.Seed.Data.Set.Subsingleton
public import Tengoku.Seed.Data.Finset.Insert
public import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Boundary: local contracts do not capture relational multiparty goals

Rectangularity and unary coordinate contracts describe **single** joint states
(or single traces): the global predicate factors as a product of per-agent
views.  Many multiparty safety goals are **relational** — they constrain how
two agents' outputs compare, or how several executions of a system relate.

This module records two elementary, machine-checked boundaries used in the
compositional-safety literature (Clarkson–Schneider hyperproperties;
communication-complexity rectangles):

1. **Agreement is not a rectangle.**  Two agents must output the same bit.
   The accepted joint configurations are the diagonal.  That set is not a
   Cartesian product of its projections, and it is not closed under coordinate
   exchange.  Independent local contracts of the form `P₁(a₁) ∧ P₂(a₂)` cannot
   express it.

2. **A 2-safety hyperproperty need not be a pure trace property.**  The
   hyperproperty "the system has at most one complete trace" is `2`-safety under
   the identity observation relation, but it is not of the form
   `{ S | S ⊆ T }` for any fixed set `T` of allowed traces.  Membership depends
   on the whole set of executions, not on each execution in isolation.

These are method limits, not AI-system claims.  They justify why the atlas keeps
both the rectangularity surface and the hyperproperty surface, and why
"verify each agent locally" is incomplete for collusion-style or
multi-execution goals.

No survey coverage row is claimed here; this is compositional infrastructure.
-/

namespace AISafetyAtlas.Compositional.LocalContractBoundary

open AISafetyAtlas.Compositional
open AISafetyAtlas.Compositional.Hyperproperties

/-! ## Boundary 1 — agreement is not a local product contract -/

/--
Two-agent agreement on a Boolean output: the joint configuration lies on the
diagonal.  This is the elementary "both principals must match" constraint.-/
@[expose] public def Agreement : Set (Bool × Bool) :=
  {p | p.1 = p.2}

/-! ## Boundary 2 — 2-safety need not be a pure trace property -/

/--
Systems with at most one complete trace.  Membership depends on the *set* of
executions: every singleton is allowed, but a two-point system is not.-/
@[expose] public def AtMostOneTrace (Trace : Type*) : Hyperproperty Trace :=
  {S | S.Subsingleton}

/--
A hyperproperty is a **pure trace property** when it is exactly the family of
all systems contained in some fixed set `T` of allowed traces.  Equivalently,
membership of a system is decided by checking each of its traces in isolation
against `T`.-/
@[expose] public def IsPureTraceProperty {Trace : Type*}
    (H : Hyperproperty Trace) : Prop :=
  ∃ T : Set Trace, H = {S | S ⊆ T}

private theorem card_pair_le_two {α : Type*} [DecidableEq α] (a b : α) :
    ({a, b} : Finset α).card ≤ 2 := by
  calc
    ({a, b} : Finset α).card ≤ ({b} : Finset α).card + 1 :=
      Finset.card_insert_le a {b}
    _ = 1 + 1 := by simp [Finset.card_singleton]
    _ = 2 := by norm_num

end AISafetyAtlas.Compositional.LocalContractBoundary
