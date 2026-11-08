module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge
public import Tengoku.Seed.Data.Set.Image

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Embedded measurement and Breuer's abstract core

This module formalizes the abstract set-theoretic core of Breuer's
self-measurement argument. A global state is restricted to an apparatus state;
an inference map assigns a set of compatible global states to every nonempty
set of possible apparatus readings; and the meshing condition requires the
inferred global states to restrict back to the readings that prompted them.

The two central results are:

* states with the same apparatus restriction cannot be distinguished by a
  meshing inference map (Proposition 2); and
* if the restriction is properly included (non-injective), no meshing
  inference map exactly measures every global state (Proposition 1).

Breuer's Corollary rearranges the second: measuring every state does not merely
fail, it makes the inference map inconsistent. That is the shape carrying his
Gödel analogy, and it is stated here as `meshing_fails_of_measuresAllStates`.

Proposition 1 is proved **twice**: derived from Proposition 2, and again by
Breuer's own direct chain. They prove the same statement and are not equal on
every axis — the derived route is axiom-free, the source-faithful one needs
`propext` and `Quot.sound`. The section *Breuer's own route to Proposition 1*
below states that trade in full; it is the reason both are kept.

The source uses an inference map on nonempty subsets of apparatus states and the
singleton meshing condition; those choices are retained here rather than replaced
by a single decoder. See `docs/provenance/self-measurement-kernel.md` for the
source mapping and the omitted parts of the paper.

## Primary surface

| Role | Declaration | One-line |
|---|---|---|
| **Model** | `Restriction` | Global state restricted to an apparatus state |
| **Model** | `ReadingSet` | A nonempty set of possible apparatus readings |
| **Model** | `InferenceMap` | Reading sets to compatible global states, under Breuer's union law |
| **Model** | `Meshing` | Inferred states restrict back exactly to the reading that prompted them |
| **Model** | `ProperInclusion` | Two distinct global states with the same restriction |
| **Model** | `ExactlyMeasurable` / `MeasuresAllStates` | Some reading set infers a state alone / every state |
| **Model** | `Distinguishes` | Mutually separating reading sets for two states — Breuer §3.2 |
| **Law** | `Meshing.restrict_surjective` | Meshing already forces surjectivity; the paper assumes it separately |
| **Law** | `infer_singleton_eq_of_meshing` | Breuer's unnamed LEMMA, as displayed on p. 208 |
| **Boundary** | `no_meshing_inference_distinguishes` | **Proposition 2** |
| **Boundary** | `no_meshing_inference_measures_all_states` | **Proposition 1**, derived — axiom-free |
| **Boundary** | `no_meshing_inference_measures_all_states_direct` | **Proposition 1**, Breuer's own chain |
| **Boundary** | `exists_state_not_exactly_measurable` | Proposition 1 in the paper's printed existential form |
| **Boundary** | `meshing_fails_of_measuresAllStates` | **Corollary** — measuring every state makes the inference map inconsistent |
| **Boundary** | `exists_state_meshing_failure_of_measuresAllStates` | The Corollary's printed witness, under the source's §3.3 surjectivity |
| **Bridge** | `not_knowable_state_of_properInclusion` | Proper inclusion through `AISafetyAtlas.Knowledge`; strictly weaker than the measurement result |

## Explicit non-claims

This is an **abstract measurement result, not a physical model**. Classical and
quantum state spaces, dynamics, apparatus construction, and EPR correlations are
intentionally left to separate layers.

Proper inclusion is **model data**, not derived. Nothing here says that a
physically contained apparatus must have a non-injective restriction; the source
does not derive it either, and Breuer's own counterexample shows containment need
not force a collision. Deriving it under stated hypotheses is
`Knowledge.Embedded.Composition` and `.Finite`, graded separately as atlas
modelling rather than as the paper.

Nothing here concerns AI systems. No self-monitoring, introspection, or
observability reading follows without a separate reviewed bridge.

The grade against Breuer is `EQUIVALENT` (`LAND-SELFMEAS-002`). Every statement
§3.5 displays is here — Propositions 1 and 2, the LEMMA, the Corollary — over the
paper's own §3.2 abstraction, and §§4–5 display none, they apply these. Not
`EXACT`, because the hypotheses are deliberately not the source's: meshing alone
is assumed where the paper assumes meshing and surjectivity, and the Corollary's
witness form takes surjectivity back explicitly. The physical, quantum,
dynamical and EPR material of the paper is not formalized.
-/

namespace AISafetyAtlas.Knowledge.Embedded

universe u v

/-! ## Measurement model -/

/-- A nonempty set of possible apparatus readings.-/
public abbrev ReadingSet (A : Type v) := {U : Set A // U.Nonempty}

/-- Exposed: `Meshing`, `ExactlyMeasurable` and `Distinguishes` are *stated* in
terms of this constructor, so an external consumer cannot discharge any of them
without unfolding it.-/
@[expose] public def ReadingSet.singleton {A : Type v} (a : A) : ReadingSet A :=
  ⟨{a}, ⟨a, rfl⟩⟩

/-- The reading set that excludes nothing: the apparatus reports no information.
Exposed for the same reason as `singleton` — the inference-map union law and the
proofs over it are stated in terms of these two constructors.-/
@[expose] public def ReadingSet.univ {A : Type v} [Nonempty A] : ReadingSet A :=
  ⟨Set.univ, by
    obtain ⟨a⟩ := ‹Nonempty A›
    exact ⟨a, by trivial⟩⟩

/--
An inference map from possible apparatus readings to compatible global states.

The union law is Breuer's `O(S_A) = ⋃ s_A ∈ S_A, O({s_A})` convention. The
empty reading set is excluded, as in the source paper.-/
public structure InferenceMap (Ω : Type u) (A : Type v) where
  infer : ReadingSet A → Set Ω
  infer_eq_union_singletons :
    ∀ U : ReadingSet A,
      infer U = {s | ∃ a ∈ U.1, s ∈ infer (ReadingSet.singleton a)}

/-- Restriction of a global state to the apparatus state.-/
public abbrev Restriction (Ω : Type u) (A : Type v) := Ω → A

/--
Breuer's proper-inclusion condition, expressed at the state level: two
distinct global states have the same apparatus restriction.

This is deliberately not derived from a set-theoretic claim that `A` is a
subsystem of `Ω`; the source explicitly treats the restriction map as part of
the physical model. Breuer also describes that restriction as surjective;
under `Meshing`, surjectivity is derived by `Meshing.restrict_surjective`.-/
@[expose] public def ProperInclusion
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A) : Prop :=
  ∃ s₁ s₂, restrict s₁ = restrict s₂ ∧ s₁ ≠ s₂

/--
Breuer's singleton-state consistency, called the meshing condition.

Verbatim §3.5: *"So meshing can be written: `∀ s_A ∈ 𝒮_𝒜 : {s|_A : s ∈ θ({s_A})} = {s_A}`."*
The equality is exact — not an inclusion — and this definition is that equality,
with `Set.image restrict` for `{s|A : s ∈ ·}`.-/
@[expose] public def Meshing
    {Ω : Type u} {A : Type v}
    (restrict : Restriction Ω A) (M : InferenceMap Ω A) : Prop :=
  ∀ a : A,
    Set.image restrict (M.infer (ReadingSet.singleton a)) = {a}

/--
Meshing forces the restriction map to be surjective.

Checked against the source. Breuer states surjectivity **separately**, as part of
the §3.3 apparatus setup — *"So `|A` describes a surjective map from the states
of O to the states of A"* — and then imposes meshing in §3.5. Here it is a
theorem rather than a second hypothesis, because the exact singleton-image
equality already entails it.

So this module's hypotheses are **no stronger** than the paper's: where Breuer
assumes surjectivity and meshing, the Lean assumes meshing alone and derives the
rest. `ProperInclusion` therefore only carries the genuinely obstructive
non-injectivity witness.-/
public theorem Meshing.restrict_surjective
    {Ω : Type u} {A : Type v} (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hm : Meshing restrict M) :
    Function.Surjective restrict := by
  intro a
  have ha : a ∈ Set.image restrict
      (M.infer (ReadingSet.singleton a)) := by
    rw [hm a]
    exact Set.mem_singleton a
  rcases ha with ⟨s, hs, hsa⟩
  exact ⟨s, hsa⟩

/-- A state is exactly measurable when some nonempty reading set infers it alone.-/
@[expose] public def ExactlyMeasurable
    {Ω : Type u} {A : Type v} (M : InferenceMap Ω A) (s : Ω) : Prop :=
  ∃ U : ReadingSet A, M.infer U = {s}

/-- Every global state is exactly measurable by an inference map.-/
@[expose] public def MeasuresAllStates
    {Ω : Type u} {A : Type v} (M : InferenceMap Ω A) : Prop :=
  ∀ s : Ω, ExactlyMeasurable M s

/--
The inference map distinguishes two states when it has mutually separating
reading sets for them.

This is Breuer's §3.2 definition, not a paraphrase of it: an experiment *"is said
to be able to distinguish the states `s₁`, `s₂` if there is one set `S¹_A` of
final apparatus states referring to `s₁` but not `s₂`, and another set `S²_A`
referring to `s₂` but not to `s₁`"*. Proposition 2 negates exactly this
existential, which is why the theorem below concludes `¬ Distinguishes`.-/
@[expose] public def Distinguishes
    {Ω : Type u} {A : Type v} (M : InferenceMap Ω A)
    (s₁ s₂ : Ω) : Prop :=
  ∃ U V : ReadingSet A,
    s₁ ∈ M.infer U ∧ s₂ ∉ M.infer U ∧
    s₂ ∈ M.infer V ∧ s₁ ∉ M.infer V

/-! ## Basic inference-map lemmas -/

private theorem mem_infer_univ_of_mem_infer
    {Ω : Type u} {A : Type v} [Nonempty A] (M : InferenceMap Ω A)
    {s : Ω} {U : ReadingSet A} (hs : s ∈ M.infer U) :
    s ∈ M.infer (ReadingSet.univ) := by
  rw [M.infer_eq_union_singletons U] at hs
  rcases hs with ⟨a, ha, hsa⟩
  rw [M.infer_eq_union_singletons ReadingSet.univ]
  exact ⟨a, by trivial, hsa⟩

private theorem restrict_eq_of_mem_infer_singleton
    {Ω : Type u} {A : Type v} [Nonempty A] (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hm : Meshing restrict M)
    {s : Ω} {a : A}
    (hsa : s ∈ M.infer (ReadingSet.singleton a)) : restrict s = a := by
  have himage : restrict s ∈ Set.image restrict
      (M.infer (ReadingSet.singleton a)) :=
    ⟨s, hsa, rfl⟩
  rw [hm a] at himage
  change restrict s = a at himage
  exact himage

private theorem mem_infer_singleton_iff_restrict_eq
    {Ω : Type u} {A : Type v} [Nonempty A] (restrict : Restriction Ω A)
    (M : InferenceMap Ω A) (hm : Meshing restrict M)
    {s : Ω} {a : A}
    (hs : s ∈ M.infer ReadingSet.univ) :
    s ∈ M.infer (ReadingSet.singleton a) ↔ restrict s = a := by
  constructor
  · exact restrict_eq_of_mem_infer_singleton restrict M hm
  · intro hres
    rw [M.infer_eq_union_singletons ReadingSet.univ] at hs
    rcases hs with ⟨b, -, hsb⟩
    have hb : restrict s = b :=
      restrict_eq_of_mem_infer_singleton restrict M hm hsb
    have hba : b = a := hb.symm.trans hres
    simpa [hba] using hsb

/-! ## Relation to the generic kernel -/

/-! ## Breuer's central results -/

/-! ## Breuer's own route to Proposition 1

The theorem above reaches Proposition 1 through Proposition 2. Breuer does not:
he proves Proposition 1 first, directly, and the LEMMA and Proposition 2 come
afterwards. His argument is a chain of rewrites,

`{s} = θ({s_A}) = θ({θ({s_A})|_A}) = θ({s|_A}) = θ({s'|_A}) = θ({θ({s'_A})|_A})`
`= θ({s'_A}) = {s'}`,

contradicting `s ≠ s'`. The two lemmas below are the steps that chain performs:
the union law picks a *single* reading out of an exact measurement, and meshing
identifies that reading as the state's restriction. Once both are available the
chain collapses, because `s` and `s'` then have the *same* singleton reading.

Both routes are kept. They prove the same statement, and having the source's
argument in the tree is what lets the provenance note claim proof-level fidelity
rather than only conclusion-level.

They are not equal on every axis, and the difference runs against the source:

| | axioms |
|---|---|
| `no_meshing_inference_measures_all_states` (via Prop 2) | *none* |
| `no_meshing_inference_measures_all_states_direct` (Breuer's) | `propext`, `Quot.sound` |

Breuer's route reasons by set extensionality at the union-law step — it must
produce an *equality of sets* `θ({s_A}) = {s}` — while the route through
Proposition 2 only ever moves elements in and out of sets, and so needs nothing.
So the derived proof is axiomatically cheaper and the direct one is
source-faithful. That is a real trade rather than a redundancy, which is why
neither is deleted. -/

end AISafetyAtlas.Knowledge.Embedded
