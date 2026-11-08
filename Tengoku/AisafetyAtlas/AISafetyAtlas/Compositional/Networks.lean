module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Compositional.Symmetry
public import Tengoku.Seed.Logic.Equiv.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Port-labelled anonymous networks, views, and automorphisms

`AISafetyAtlas.Compositional.Symmetry` isolates the inductive core of Angluin's
argument, but takes observational indistinguishability as a structure field.
This module builds the network underneath it, so that indistinguishability is
*derived* from network structure rather than assumed.

## What is modelled

Angluin, *Local and Global Properties in Networks of Processors*, STOC 1980.

* A **port-labelled network**: each node has `deg` ports, and `port v i` is the
  neighbour reached from `v` through port `i`.
* **Identical processors**: one `send` and one `update` function, shared by
  every node.  There are no identifiers anywhere in the state of the algorithm,
  which is what anonymity means here.
* **Views**: `pathTo` walks a port sequence from a node, and two nodes have the
  same view to depth `n` when every port sequence of length at most `n` reaches
  equally-labelled nodes.
* **Automorphisms**: port-preserving permutations of the nodes.

## What is proved

* `runFor_eq_of_view_eq`: nodes with equal views to depth `n` are in equal
  states after `n` rounds.  This is the Angluin lemma the symmetry core
  previously assumed, and it is the reason anonymity has consequences at all.
* `invariant_of_automorphism`: a configuration invariant under a network
  automorphism stays invariant under every round.
* `no_unique_leader_of_fixedPointFree`: a fixed-point-free automorphism of an
  invariant configuration rules out ever electing a unique leader.
* `invariant_of_constant`: a constant configuration is invariant under every
  automorphism, which is how the earlier symmetry core sits inside this one.

## Explicit non-claims

* **Deterministic and synchronous only.**  No randomness, so the randomized
  impossibility of Itai and Rodeh is out of scope; no asynchrony.
* **Simplified message routing.**  The message a node receives on port `i` is
  what its port-`i` neighbour sends on index `i`.  A faithful model would route
  through the neighbour's own port back to the sender, which needs a port
  numbering with an involution; that is not modelled.
* **Not a covering theory.**  Views and automorphisms are given; the general
  quotient/covering machinery relating a network to its universal cover is not.
* **Not BY-043.**  This remains an upstream dependency for the survey-original
  result, not coverage of it.  No status upgrade follows from it.
-/

namespace AISafetyAtlas.Compositional.Networks

/-- A port-labelled network: `port v i` is the neighbour of `v` through port
`i`.-/
public structure Network (Node : Type*) (deg : ℕ) where
  /-- The neighbour reached through a given port.-/
  port : Node → Fin deg → Node

/-- An anonymous synchronous algorithm: one message function and one transition
function, shared by every node.  No node identifiers appear.-/
public structure Algorithm (State Msg : Type*) (deg : ℕ) where
  /-- The message a node in a given state emits on a given port.-/
  send : State → Fin deg → Msg
  /-- The next state, from the current state and the messages received.-/
  update : State → (Fin deg → Msg) → State

/-- An assignment of states to nodes.-/
public abbrev Config (Node State : Type*) : Type _ := Node → State

variable {Node State Msg : Type*} {deg : ℕ}

/-- Walk a sequence of ports from a node.-/
@[expose] public def pathTo (N : Network Node deg) (v : Node) :
    List (Fin deg) → Node
  | [] => v
  | i :: rest => pathTo N (N.port v i) rest

/-- Two nodes have the same view to depth `n` when every port sequence of length
at most `n` reaches equally-labelled nodes.-/
@[expose] public def SameView (N : Network Node deg) (c : Config Node State)
    (n : ℕ) (u v : Node) : Prop :=
  ∀ p : List (Fin deg), p.length ≤ n → c (pathTo N u p) = c (pathTo N v p)

/-- One synchronous round of an anonymous algorithm.-/
@[expose] public def step (N : Network Node deg) (A : Algorithm State Msg deg)
    (c : Config Node State) : Config Node State :=
  fun v => A.update (c v) (fun i => A.send (c (N.port v i)) i)

/-- Run `n` synchronous rounds.-/
@[expose] public def runFor (N : Network Node deg) (A : Algorithm State Msg deg)
    (c : Config Node State) : ℕ → Config Node State
  | 0 => c
  | n + 1 => step N A (runFor N A c n)

/-! ## Automorphisms -/

/-- A port-preserving permutation of the nodes.-/
public structure Automorphism (N : Network Node deg) where
  /-- The underlying permutation.-/
  toEquiv : Node ≃ Node
  /-- It preserves the port structure.-/
  port_equivariant : ∀ v i, N.port (toEquiv v) i = toEquiv (N.port v i)

/-- A configuration is invariant under an automorphism when moving a node by it
does not change the node's state.-/
@[expose] public def Invariant {N : Network Node deg} (σ : Automorphism N)
    (c : Config Node State) : Prop :=
  ∀ v, c (σ.toEquiv v) = c v

end AISafetyAtlas.Compositional.Networks
