module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Compositional.Networks
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Compositional.Hyperproperties
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A network's runs, as a trace system

## Statement intent

- **Objects.** A `Run` is a whole synchronous execution, `ℕ → Config Node State`.
  A `Snapshot` is the finite observation atom "at round `n` the configuration is
  `c`". A network with an algorithm and a set of initial configurations produces
  a `Hyperproperties.TraceSystem`.
- **Interface.** `realizes_systemOf` says exactly which finite observations that
  system realizes: those whose every snapshot is reached from some admitted
  initial configuration.
- **Payoff.** `not_electsLeader_of_fixedPointFree` is Angluin's conclusion at the
  level of trace systems, and `electsLeader_witnessed_by_one_snapshot` places
  leader election in the finite-observation vocabulary, as an
  `IsBadObservation` at `k = 1` for the complement.

## Why this direction

`Compositional.Hyperproperties` defines `TraceSystem`, `Realizes`,
`IsBadObservation`, `IsKSafety`, `IsSafetyPredicate`, the self-composition
reduction and the prefix topology — and **nothing in the tree produced a trace**.
The four modules that generate executions (`Networks`, `Symmetry`,
`Wireheading.CRMDP`, `Wireheading.GoalPreservation`) had no consumer that reads
them as traces. Both halves were live and unconnected. This module is a producer
for the first of them.

The dependency runs one way: `Hyperproperties` is untouched, and nothing here is
imported by it.

## What this does and does not commit to

- **No general answer to "what is a system".** `Trace` and `Prefix` are free type
  parameters throughout `Hyperproperties`, and `prefixOf` is supplied by the
  caller, so instantiating them for `Networks` commits nothing about how any
  other model should be read. A shared transition-system interface would be a
  different and much larger decision; this is an instantiation, not an ontology.
- **Two readings of "a trace", and both are built.** A run can be the
  round-indexed sequence of whole *configurations* (`Run`, §1), or the sequence
  one *node* observes (`ObsTrace`, §4). The first is the outside view and is what
  a global safety argument wants. The second is the more faithful notion for an
  *anonymous* network, because it is what a node actually has, and it is what
  makes anonymity statable: `not_knowable_node_of_fixedPointFree` says a node
  cannot recover its own identity from what it observes.

  The finer readings are still not built. A node's own state sequence is not
  everything it could see — `Algorithm.update` reads incoming messages, and the
  state sequence does not determine them, so a node permitted to record received
  messages would know strictly more. `ObsTrace` is the coarsest honest choice,
  not the finest possible one.
- **The machinery becomes applicable; the example exercises little of it.**
  Connecting the types puts `IsKSafety`, `IsHyperSafety`, `IsHyperLiveness`, the
  self-composition reduction and the prefix topology within reach of a real
  dynamic model. What is *worked* below is a single `k = 1` certificate. No
  `k ≥ 2` hyperproperty of networks is stated here, and the genuinely
  hyperproperty-shaped claims — non-interference, collusion, privacy under
  composition — remain unformalized over this model.
- **Not new network mathematics, and no BY-043 status follows.**
  `not_electsLeader_of_fixedPointFree` is
  `Networks.no_unique_leader_of_fixedPointFree` transported across the producer;
  it proves nothing about networks that the Angluin route did not already prove.
  `Networks` remains an upstream dependency of the survey-original BY-043 and
  this does not change that.
- **`ElectsLeader` is not offered as the interesting hyperproperty.** It is the
  one the tree can already refute, chosen so that the producer is exercised by a
  theorem rather than by a definition.

## Scope boundary

Everything inherits `Networks`' non-claims: deterministic and synchronous only,
no randomness, no asynchrony, and the simplified message routing in which the
message received on port `i` is what the port-`i` neighbour sends on index `i`.
`inits` is an arbitrary `Set`, not required finite or nonempty; the empty set
gives the empty trace system, which realizes only the empty observation.
-/

namespace AISafetyAtlas.Compositional.Networks

open AISafetyAtlas.Compositional.Hyperproperties

variable {Node State Msg : Type*} {deg : ℕ}

/-! ## The producer -/

/-- A trace of an anonymous network: the whole synchronous run, round by round.-/
public abbrev Run (Node State : Type*) : Type _ := ℕ → Config Node State

/-- A finite observation atom: "at round `n` the configuration is `c`".-/
public abbrev Snapshot (Node State : Type*) : Type _ := ℕ × Config Node State

/-- A run exhibits a snapshot when it matches there. This is the `prefixOf`
relation the trace theory is parameterized by.-/
@[expose] public def observedAt (s : Snapshot Node State) (t : Run Node State) : Prop :=
  t s.1 = s.2

/-- The run produced from one initial configuration.-/
@[expose] public def runOf (N : Network Node deg) (A : Algorithm State Msg deg)
    (c : Config Node State) : Run Node State :=
  fun n => runFor N A c n

/-- The trace system produced over a set of admitted initial configurations.-/
@[expose] public def systemOf (N : Network Node deg) (A : Algorithm State Msg deg)
    (inits : Set (Config Node State)) : TraceSystem (Run Node State) :=
  runOf N A '' inits

/-! ## Producer meets consumer -/

/-! ## Leader election over trace systems -/

/-- The hyperproperty "this system elects a unique leader at some round".-/
@[expose] public def ElectsLeader (leader : State → Prop) :
    Hyperproperty (Run Node State) :=
  {S | ∃ t ∈ S, ∃ n, Symmetry.HasUniqueLeader leader (t n)}

/-! ## 4. The other reading: what one node sees

`Run` above is the outside view. A node has no such thing: it has no identifier,
no global picture, and one shared pair of `send`/`update` functions. What it has
is its own state, round by round. That is `ObsTrace`, and stating anonymity needs
it — the configuration-level results below §2 quantify over a global object no
participant holds.
-/

/-- What one node observes: its own state, round by round.-/
@[expose] public def ObsTrace (N : Network Node deg) (A : Algorithm State Msg deg)
    (c : Config Node State) (u : Node) : ℕ → State :=
  fun n => runFor N A c n u

/-- The observation system: one trace per **node**, where `systemOf` gives one per
initial configuration.-/
@[expose] public def obsSystem (N : Network Node deg) (A : Algorithm State Msg deg)
    (c : Config Node State) : TraceSystem (ℕ → State) :=
  Set.range (ObsTrace N A c)

/-- A prefix atom for an observation trace: "at round `n` I was in state `s`".-/
@[expose] public def stateAtRound (p : ℕ × State) (t : ℕ → State) : Prop := t p.1 = p.2

end AISafetyAtlas.Compositional.Networks
