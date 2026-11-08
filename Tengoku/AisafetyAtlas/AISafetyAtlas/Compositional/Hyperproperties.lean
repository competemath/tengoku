module

public import Tengoku.Seed.Data.Finset.Image
public import Tengoku.Seed.Topology.Closure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Hyperproperties, finite witnesses, and self-composition

The definitions follow Clarkson and Schneider, *Hyperproperties* (JCS 2010):
a hyperproperty is a set of systems (sets of traces), and a `k`-safety
violation has a bad finite observation of at most `k` trace prefixes.

`k_safety_iff_finite_self_composition` is a set-based presentation of their
Theorem 2.  A member of the self-composition is an unordered batch of at most
`k` traces; this avoids artificial padding and duplicate coordinates while
retaining exactly the finite witnesses used by the proof.

The final decomposition theorem reproduces the generic topological theorem used
by Abate et al., *Journey Beyond Full Abstraction* (CSF 2019), in their Rocq
development.  The specialization to hypersafety/hyperliveness depends on the
chosen topology and is therefore not silently asserted here.

`AISafetyAtlas.Compositional.Hyperproperties.PrefixTopology` supplies the
observation topology that earns the operational reading: there `IsClosed` is
proved equivalent to Clarkson-Schneider hypersafety, `Dense` to hyperliveness,
and `IsKSafety` is shown to imply hypersafety, which connects the reduction
below to the decomposition.
-/

namespace AISafetyAtlas.Compositional.Hyperproperties

/-- A system is a set of complete traces.-/
public abbrev TraceSystem (Trace : Type*) := Set Trace

/-- A hyperproperty is a set of systems.-/
public abbrev Hyperproperty (Trace : Type*) := Set (TraceSystem Trace)

/-- A finite observation is a finite set of finite trace prefixes.-/
public abbrev Observation (Prefix : Type*) := Finset Prefix

/-- A system realizes an observation when every observed prefix extends to
some complete trace in the system.-/
@[expose] public def Realizes {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (M : Observation Prefix) (S : TraceSystem Trace) : Prop :=
  ∀ p ∈ M, ∃ t ∈ S, prefixOf p t

/-- `M` is a bad observation for `H`: every system realizing it violates `H`.-/
@[expose] public def IsBadObservation {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (H : Hyperproperty Trace) (M : Observation Prefix) : Prop :=
  ∀ S, Realizes prefixOf M S → S ∉ H

/--
A `k`-safety hyperproperty.  Every violating system exhibits a bad observation
containing at most `k` finite prefixes.-/
@[expose] public def IsKSafety {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (k : ℕ) (H : Hyperproperty Trace) : Prop :=
  ∀ S, S ∉ H → ∃ M : Observation Prefix,
    M.card ≤ k ∧ Realizes prefixOf M S ∧ IsBadObservation prefixOf H M

/-- Unordered finite `k`-fold self-composition: batches of at most `k` traces
drawn from `S`.-/
@[expose] public def FiniteSelfComposition {Trace : Type*}
    (k : ℕ) (S : TraceSystem Trace) : Set (Finset Trace) :=
  {batch | (batch : Set Trace) ⊆ S ∧ batch.card ≤ k}

/-- The safety predicate produced by the reduction: a trace batch contains no
bad observation of size at most `k`.-/
@[expose] public def SelfCompositionSafe {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (k : ℕ) (H : Hyperproperty Trace) (batch : Finset Trace) : Prop :=
  ¬ ∃ M : Observation Prefix,
    M.card ≤ k ∧
    Realizes prefixOf M (batch : Set Trace) ∧
    IsBadObservation prefixOf H M

/-- Ordinary finite-observation safety for a predicate on trace batches.-/
@[expose] public def IsSafetyPredicate {Prefix Trace : Type*}
    (prefixOf : Prefix → Trace → Prop)
    (P : Finset Trace → Prop) : Prop :=
  ∀ batch, ¬ P batch → ∃ M : Observation Prefix,
    Realizes prefixOf M (batch : Set Trace) ∧
    ∀ batch' : Finset Trace,
      Realizes prefixOf M (batch' : Set Trace) → ¬ P batch'

/-- Topological hypersafety predicate for an explicitly supplied topology.-/
public abbrev IsHyperSafety {Trace : Type*}
    [TopologicalSpace (TraceSystem Trace)]
    (H : Hyperproperty Trace) : Prop :=
  IsClosed H

/-- Topological hyperliveness predicate for an explicitly supplied topology.-/
public abbrev IsHyperLiveness {Trace : Type*}
    [TopologicalSpace (TraceSystem Trace)]
    (H : Hyperproperty Trace) : Prop :=
  Dense H

end AISafetyAtlas.Compositional.Hyperproperties
