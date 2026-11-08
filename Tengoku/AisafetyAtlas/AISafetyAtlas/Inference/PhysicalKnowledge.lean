module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Device
public import Tengoku.Seed.Data.Set.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Physical knowledge — Wolpert 2018

A source-faithful first layer from D. H. Wolpert, *Constraints on physical
reality arising from a formalization of knowledge* (2018), section V.1.

The source strengthens weak inference. For a device `C = (X,Y)`, a target
`Γ : U → G`, a value `γ ∈ Γ(U)`, and a set of worlds `W`, a certificate chooses
one realized setup-partition block for every realized value of `Γ`. It must:

1. answer the corresponding probe correctly on the entire selected block;
2. answer `true` somewhere, and everywhere in `W` on the block selected for
   `γ`;
3. answer `false` somewhere, and everywhere in `W` on every block selected for
   a different realized value.

`PhysicalKnowledgeWitness` is the source's selector `ξ` together with these
three obligations. `PhysicallyKnows` is existence of such a certificate.

## Fidelity decisions

* The source's `Γ(U)` is the subtype `{g // ∃ u, Γ u = g}`. No ambient values
  outside the image are added to the selector's domain.
* The source's `X̄`, the partition induced by `X`, is represented by realized
  setup values. Equality of setup values is equality of their fibres, so this
  is the same partition with explicit labels.
* The Kronecker probe is stated without `DecidableEq G` as
  `Y u = true ↔ Γ u = g`. This is propositionally equivalent to
  `Y = δ_g ∘ Γ` and preserves the paper's unrestricted type scope.
* `W` is a `Set U`. No probability, topology, dynamics, or physical-worldline
  interpretation is added.

## Primary surface

| Source | Declaration | Content |
|---|---|---|
| Definition 11 | `PhysicalKnowledgeWitness`, `PhysicallyKnows` | Physical knowledge by a selector of setup blocks |
| prose after Definition 11 | `PhysicallyKnows.weaklyInfers` | Physical knowledge entails weak inference |
| Lemma 17(i) | `PhysicalKnowledgeWitness.eq_target_of_mem_knownBlock` | The known block meets `W` only where `Γ = γ` |
| Lemma 17(ii) | `PhysicalKnowledgeWitness.eq_target_on_of_refinesOn` | If `W` refines `Γ`, then `Γ = γ` throughout `W` |
| Proposition 18 | `physicallyKnows_false_iff_not_true` | Knowing `Γ` false is knowing `¬Γ` true |
| Corollary 19 | `true_on_of_physicallyKnows_true`, `false_on_of_physicallyKnows_false`, `not_physicallyKnows_true_and_false` | Knowledge is truthful when `W` refines the target, and cannot affirm both values |
| Corollary 22 | `exists_never_physicallyKnown` | Every device has a target it knows at no value over any `W` |

## Non-claims

This is Wolpert's device-relative physical-knowledge predicate, not
`Knowledge.Knowable`: the former chooses a setup block per probe, while the
latter uses one decoder uniformly over every state. **No identification between
them is claimed**, here or anywhere.

What is claimed, in `AISafetyAtlas.Knowledge.Devices` and not in this file, is a
one-way transport: a collision that the device cannot resolve inside *every*
realized block, straddling the value in question, refutes `PhysicallyKnows` at
that value **for every context `W`** — because Definition 11's clause (i)
constrains the whole selected block rather than its trace in `W`. Nothing in this
file depends on that module. Epistemic consequences and the event boundary live in
the downstream `PhysicalKnowledge.Epistemic` and `.Event` modules. Complexity,
Kraft, and entropy sections of the 2018 paper remain outside this development.
-/

namespace AISafetyAtlas.Inference

universe u v v'

variable {U : Type u}

/-- A value in the realized image `Γ(U)`.-/
public abbrev ImageValue {G : Type v'} (Γ : U → G) :=
  {g : G // ∃ u : U, Γ u = g}

/-- A block of the setup partition induced by a device: equivalently, a
realized setup value together with a state in its fibre.-/
public abbrev SetupBlock (C : InferenceDevice.{u, v} U) :=
  {x : C.Setup // C.Realized x}

/--
**Wolpert 2018, Definition 11 — witness form.** A selector `ξ : Γ(U) → X̄`
certifying that `C` physically knows `Γ = γ` over `W`.

The fields `yes_nonempty`/`yes_on` encode Definition 11(ii), and
`no_nonempty`/`no_on` encode Definition 11(iii). The `correct` field is
Definition 11(i) on all of `U`, not merely on `W`.-/
public structure PhysicalKnowledgeWitness
    (C : InferenceDevice.{u, v} U) {G : Type v'}
    (Γ : U → G) (γ : G) (W : Set U) where
  /-- Definition 11 requires `γ ∈ Γ(U)`.-/
  target_realized : ∃ u : U, Γ u = γ
  /-- The source's `ξ : Γ(U) → X̄`.-/
  selector : ImageValue Γ → SetupBlock C
  /-- Definition 11(i): the selected block answers the probe of `g` correctly.-/
  correct : ∀ (g : ImageValue Γ) (u : U),
    C.setup u = (selector g).1 → (C.concl u = true ↔ Γ u = g.1)
  /-- The selected block for `γ` meets `W`.-/
  yes_nonempty : ∃ u : U,
    u ∈ W ∧ C.setup u = (selector ⟨γ, target_realized⟩).1
  /-- Definition 11(ii): that intersection is contained in `Y⁻¹(true)`.-/
  yes_on : ∀ u : U, u ∈ W →
    C.setup u = (selector ⟨γ, target_realized⟩).1 → C.concl u = true
  /-- Every selected block for a different realized value meets `W`.-/
  no_nonempty : ∀ (g : ImageValue Γ), g.1 ≠ γ → ∃ u : U,
    u ∈ W ∧ C.setup u = (selector g).1
  /-- Definition 11(iii): each such intersection lies in `Y⁻¹(false)`.-/
  no_on : ∀ (g : ImageValue Γ), g.1 ≠ γ → ∀ u : U, u ∈ W →
    C.setup u = (selector g).1 → C.concl u = false

/-- **Wolpert 2018, Definition 11.** `C` physically knows `Γ = γ` over `W`
when a single selector satisfies all three source clauses.-/
@[expose] public def PhysicallyKnows
    (C : InferenceDevice.{u, v} U) {G : Type v'}
    (Γ : U → G) (γ : G) (W : Set U) : Prop :=
  Nonempty (PhysicalKnowledgeWitness C Γ γ W)

/-- The setup block selected for the value the certificate claims is known.-/
public abbrev PhysicalKnowledgeWitness.knownBlock
    {C : InferenceDevice.{u, v} U} {G : Type v'} {Γ : U → G} {γ : G} {W : Set U}
    (K : PhysicalKnowledgeWitness C Γ γ W) : SetupBlock C :=
  K.selector ⟨γ, K.target_realized⟩

/-- `W` refines `Γ`: the target is constant across `W`. This is the source's
partition language written pointwise.-/
@[expose] public def RefinesOn {G : Type v'} (W : Set U) (Γ : U → G) : Prop :=
  ∀ ⦃u v : U⦄, u ∈ W → v ∈ W → Γ u = Γ v

/-- Negate a realized Boolean target value.-/
private def negImageValue (Γ : U → Bool) :
    ImageValue (fun u => Bool.not (Γ u)) → ImageValue Γ :=
  fun z => ⟨Bool.not z.1, by
    obtain ⟨u, hu⟩ := z.2
    exact ⟨u, by rw [← hu, Bool.not_not]⟩⟩

/-- Relabel a Definition 11 certificate along Boolean negation. This is the
construction used in Proposition 18.-/
public def PhysicalKnowledgeWitness.negate
    {C : InferenceDevice.{u, v} U} {Γ : U → Bool} {γ : Bool} {W : Set U}
    (K : PhysicalKnowledgeWitness C Γ γ W) :
    PhysicalKnowledgeWitness C (fun u => Bool.not (Γ u)) (Bool.not γ) W := by
  let htarget : ∃ u : U, Bool.not (Γ u) = Bool.not γ := by
    obtain ⟨u, hu⟩ := K.target_realized
    exact ⟨u, congrArg Bool.not hu⟩
  let ξ : ImageValue (fun u => Bool.not (Γ u)) → SetupBlock C :=
    fun z => K.selector (negImageValue Γ z)
  have hknown :
      negImageValue Γ
          (⟨Bool.not γ, htarget⟩ : ImageValue (fun u => Bool.not (Γ u))) =
        (⟨γ, K.target_realized⟩ : ImageValue Γ) := by
    apply Subtype.ext
    simp [negImageValue]
  refine {
    target_realized := htarget
    selector := ξ
    correct := ?_
    yes_nonempty := ?_
    yes_on := ?_
    no_nonempty := ?_
    no_on := ?_ }
  · intro z u hu
    have hc := K.correct (negImageValue Γ z) u hu
    simpa [negImageValue] using hc
  · obtain ⟨u, huW, huX⟩ := K.yes_nonempty
    exact ⟨u, huW, by simpa [ξ, hknown] using huX⟩
  · intro u huW huX
    apply K.yes_on u huW
    simpa [ξ, hknown] using huX
  · intro z hz
    have hne : (negImageValue Γ z).1 ≠ γ := by
      intro h
      apply hz
      have hn := congrArg Bool.not h
      simpa [negImageValue] using hn
    obtain ⟨u, huW, huX⟩ := K.no_nonempty (negImageValue Γ z) hne
    exact ⟨u, huW, huX⟩
  · intro z hz u huW huX
    have hne : (negImageValue Γ z).1 ≠ γ := by
      intro h
      apply hz
      have hn := congrArg Bool.not h
      simpa [negImageValue] using hn
    exact K.no_on (negImageValue Γ z) hne u huW huX

/-! ## The weaker knowledge operator the paper raises but does not adopt

After Example 9 the paper considers relaxing Definition 11:

> *"…the definition of physical knowledge could be weakened to agree with this
> aspect of the colloquial meaning of 'knowledge'. One way to do that would be
> drop the requirement that the ID infer `Γ` in full, including for `u ∉ W`.
> Under this modified definition …we would still require that for all
> `u ∈ ξ(γ)`, if `Y(u) = 1`, then `Γ(u) = γ` (whether or not `u ∈ W`). …However
> for all `γ′ ≠ γ`, we only require that for all `u ∈ W ∩ ξ(γ′)`, if
> `Y(u) = −1`, then `δ_γ(Γ(u)) = Y(u)`."*

The arXiv HTML carries `γ′ ≠ γ`. The printed clause still writes `δ_γ`, so on
the block `ξ(γ′)` it demands `Γ(u) ≠ γ`. The next sentence describes the device
answering *"does `Γ(u) = γ′`?"*, which is `δ_{γ′}` and demands `Γ(u) ≠ γ′`
inside `W`.

The two readings are not equivalent. Only `δ_{γ′}` makes the modification a
*weakening*: under that reading Definition 11 implies it, proved below; under
the printed `δ_γ` it does not.

The Lean encodes `δ_{γ′}` and the row is `REPAIRED`. Clash 27 in
[`wolpert-2008-source-clashes.md`](../../docs/provenance/wolpert-2008-source-clashes.md)
records the printed subscript and an author comment left in the paper's LaTeX
asking whether this passage works.
-/

/--
**The weakened operator.** Definition 11 with clause (i)'s biconditional split
into its two printed halves: correctness of a `true` answer on the `γ` block
everywhere, and correctness of a `false` answer on the other blocks **only
inside `W`**.-/
public structure WeakKnowledgeWitness (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (γ : G) (W : Set U) where
  /-- Definition 11 requires `γ ∈ Γ(U)`.-/
  target_realized : ∃ u : U, Γ u = γ
  /-- The source's `ξ : Γ(U) → X̄`.-/
  selector : ImageValue Γ → SetupBlock C
  /-- *"for all `u ∈ ξ(γ)`, if `Y(u) = 1`, then `Γ(u) = γ` (whether or not
  `u ∈ W`)"* — global, as printed.-/
  yes_correct : ∀ u : U, C.setup u = (selector ⟨γ, target_realized⟩).1 →
    C.concl u = true → Γ u = γ
  /-- *"for all `γ′ ≠ γ` …for all `u ∈ W ∩ ξ(γ′)`, if `Y(u) = −1`, then
  `δ_{γ′}(Γ(u)) = Y(u)`"* — restricted to `W`, which is the whole point of the
  modification.-/
  no_correct : ∀ (g : ImageValue Γ), g.1 ≠ γ → ∀ u : U, u ∈ W →
    C.setup u = (selector g).1 → C.concl u = false → Γ u ≠ g.1

/-- `C` weakly knows `Γ = γ` over `W`, in the paper's modified sense.-/
@[expose] public def WeakPhysicallyKnows (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (γ : G) (W : Set U) : Prop :=
  Nonempty (WeakKnowledgeWitness C Γ γ W)

end AISafetyAtlas.Inference
