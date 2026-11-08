module

public import Tengoku.Seed.Logic.Function.Defs
public import Tengoku.Seed.Data.Bool.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inference devices — Wolpert 2008, the impossibility core

A source-faithful reconstruction of the definitions and impossibility results of
D. H. Wolpert, *Physical limits of inference*, Physica D 237(9):1257–1281, 2008
(arXiv:0708.1362), sections 3.1–3.4, 4.2 and 7. Sections 5, 6, 8 and 9
live in the sibling modules `Complexity`, `Reality`, `Stochastic` and
`SelfAware`.

## What an inference device is

The paper's claim is that observation, prediction, and recollection share one
mathematical structure. A device over a set `U` of universes is a pair of
functions on `U`: a **setup** function recording how the device is configured,
and a **conclusion** function recording what it ends up asserting. Nothing is
assumed about how the two are related.

## Fidelity to the source

Stated exactly, because the encoding is the claim.

* **Def 1** is `InferenceDevice`. The paper's conclusion function is onto
  `𝔹 = {-1, +1}`; here it is onto `Bool`. That is a renaming of a two-element
  codomain: the paper's identity probe `f(y) = y` becomes `id`, and its negation
  probe `f(y) = -y` becomes `not`. It is **not** the only encoding decision —
  the rest of this list is.
* **Def 2 as printed is `IsSourceProbe`** — *a mapping from a set with at least
  two elements **onto** `𝔹` that equals `1` for one and only one argument*. The
  working predicate below is `IsProbe`, which keeps only the unique-true clause,
  and **every consumer (`WeaklyInfers`, `StronglyInfers`, `Controls`) quantifies
  over `IsProbe`, not `IsSourceProbe`.**
  The two coincide wherever the source is defined: `surjective_of_isProbe` shows
  unique-true forces onto-`𝔹` as soon as the range has a second point, and
  `isSourceProbe_iff` packages that. The only divergence is a **singleton** range,
  which the source excludes by its global stipulation that every function over `U`
  takes at least two values. `weaklyInfers_iff_sourceProbes` is the bridge: on any
  range with two values, quantifying over `IsProbe` and over `IsSourceProbe` give
  the same Definition 3. So the working predicate is a convenience, not a weaker
  claim — but it *is* the predicate in every signature, and a consumer
  instantiating `IsProbe` on a singleton range is not using Wolpert's probe.
  Definition 3 quantifies over probe **functions**, as the source's `∀ f ∈ π(Γ)`
  does, and nothing needs decidable equality on the target range; `probe` is
  supplied as the canonical Kronecker delta when a range happens to have it,
  purely so finite models stay executable. `exists_isProbe` constructs a probe at
  every point, so `∀ f, IsProbe f γ → …` is never vacuously true.
  The source's two-value stipulation is **not** imposed here, on targets or on
  setup functions. On the setup side the drop is load-bearing: a device whose setup is constant is
  `Distinguishable` from itself, which the source denies. Theorem 1 then applies
  to that pair and yields `¬ InfersDevice C C`, already given by Proposition 1(ii).
  So Theorem 1 is **stronger** than in the source — it covers pairs the source's
  hypothesis never reaches. The witness is
  `Examples.Inference.Device.constSetup_distinguishable_self`.
* **Realized values.** Where the source writes `∀ x₁, x₂` in Definitions 4, 5 and
  8, the quantifier ranges over values the setup function actually takes, as its
  own shorthand convention in Definition 3 (`∃ x ∈ X(U)`) fixes. That reading is
  forced: over the whole setup type, distinguishability could never hold for a
  device with an unused setup value. It also makes Theorem 1 stronger, since more
  pairs of devices qualify as distinguishable.
* **Def 3** is `WeaklyInfers`, with the paper's quantifier order preserved:
  *for every probe there exists a setup value* such that the conclusion answers
  that probe throughout the fibre. The setup value is required to be **realized**,
  as the source's `∃ x ∈ X(U)` demands; dropping that would make weak inference
  vacuously true whenever the setup type has an unused value.
* **Def 4** is `Distinguishable`, quantified over realized setup values on both
  sides, matching the source's shorthand convention. Combined with the dropped
  two-value stipulation on setups, self-distinguishability is possible (above).
* **"Identical partitions"** in Theorem 5 is represented as equality of the two
  same-fibre relations. Two functions induce the same partition exactly when their
  kernels agree, so this is the partition statement, up to the relabelling of setup
  ranges the source itself describes.
* **Def 5** is `StronglyInfers`.
* **Def 8** is `SemiControls` and `Controls`.
* **Prop 1(i)**, **Prop 1(ii)**, **Prop 2(i)**, **Prop 2(ii)**, **Cor 1(i)**,
  **Cor 2**, **Thm 1**, **Thm 2**, the immediate strong-to-weak and
  strong-to-semi-control consequences, **Thm 3**, **Thm 5** and **Cor 3**
  (all three parts, with (ii) as `¬A ∧ ¬B`) are the theorems below.

**One strengthening.** The source proves Theorem 5 using the axiom of choice, to
pick a setup value for each value of the other device's setup. The proof here
needs no such selection: it shows directly that the block containing any state is
common to both partitions. The statement is unchanged.

`#print axioms` reports that Theorem 5 and every impossibility result here —
Proposition 1(ii), Theorems 1, 2 and 3, and the control transports — depend on
**no axioms at all**, not merely on the classical three the atlas permits.

The existence half is classical, and says so: `separatingDevice_weaklyInfers`,
`exists_isProbe` and the Proposition 1(i) / Corollary 1(i) wrappers report
`{propext, Classical.choice, Quot.sound}`, while the constructive
`semiControls_of_controls` reports `propext` alone. The unrestricted classical
`semiControls_of_controls_classical` carries the generic probe construction.
Constructing a device, or a probe at an arbitrary point, is where the classical
content sits; refuting one never needs it. Re-measure rather than assume — this
profile has already drifted once.

## What is not here

Section 5 (inference complexity, Def 6 and Thm 4), section 6 (realities and
copies, Def 7, Lemma 1, Props 3–5), section 8 (**stochastic devices**, Defs 9–11
and Prop 6 — the only place in the paper a probability measure `P` over `U`
appears: *"in the analysis above there is no probability measure P over U"*),
and section 9 (self-aware devices, Defs 12–14, Thms 6–7, Prop 7, Cors 4–5)
are mechanized in the sibling modules, not in this file.

**Corollary 1(ii) is refuted rather than omitted.** As literally stated — *any*
`Γ` over any `U` is inferred by some device — it is false: no device over a
two-state universe weakly infers the identity, since its conclusion function would
have to be constant against the surjectivity Definition 1 demands. The countermodel
is `Examples.Inference.Device.no_device_weaklyInfers_id_on_bool`. The statement
needs the hypothesis its own proof uses, a proper `W ⊂ U` on which `Γ` already
attains every value; over a large `U` that is automatic.

Also not here: Wolpert 2018's knowledge operator; its statement map is recorded in
[`docs/provenance/wolpert-2018-knowledge.md`](../../docs/provenance/wolpert-2018-knowledge.md).

## Relation to `Knowledge.Knowable` — none, and this was checked

`Knowable r f` is `∃ decoder, ∀ ω, f ω = decoder (r ω)`. Weak inference is
`∀ probe, ∃ setup, ∀ u in that fibre, …` over a **fixed** conclusion function.
Neither implies the other, and both failures are witnessed on finite models:

* a device whose setup is the identity and whose conclusion is the negation makes
  the target knowable while weakly inferring nothing;
* a three-state device weakly infers a target that does not factor through its
  setup at all.

See `AISafetyAtlas.Examples.Inference.Device`. Do **not** package weak inference
as a form of knowability; the quantifier alternation and the fixed conclusion
function are both load-bearing.

That non-identification stands. What builds on it is
`AISafetyAtlas.Knowledge.Devices`, which states the **conditional** transports
between the two — a knowability witness for the device's own setup-and-conclusion
pair, present in every realized block and straddling the target value, refutes
Definition 3 and Definition 11 alike. Those are atlas lemmas about when the two
mechanisms talk to each other, not a claim that they coincide, and no declaration
in this file depends on them.

## Explicit non-claims

No probability, no dynamics, no physics. `U` is an arbitrary set of universes and
nothing here makes it physical; the paper's own claim is that its results hold
*independent* of the physical laws, and the Lean statements inherit exactly that
generality and no more. No AI-system reading follows without a separate reviewed
bridge.
-/

namespace AISafetyAtlas.Inference

universe u v v' v''

/-! ## Devices -/

/--
**Definition 1.** An inference device over `U`: a setup function recording how the
device is configured, and a conclusion function recording what it asserts.

`Setup` is a field rather than a parameter so that devices with different setup
types can be compared in one statement, as the source's pairwise results require.
The conclusion function is onto `Bool` — the source's surjectivity requirement on
`Y`, which is what makes both probes of its range available.-/
public structure InferenceDevice (U : Type u) where
  /-- The values the device can be configured to.-/
  Setup : Type v
  /-- How the device is set up in a given universe.-/
  setup : U → Setup
  /-- What the device concludes in a given universe.-/
  concl : U → Bool
  /-- Both conclusions are reachable.-/
  concl_surjective : Function.Surjective concl

variable {U : Type u}

/-- A setup value the device actually takes somewhere.-/
@[expose] public def InferenceDevice.Realized (C : InferenceDevice.{u, v} U)
    (x : C.Setup) : Prop :=
  ∃ w : U, C.setup w = x

/-! ## Probes -/

/--
**Definition 2.** A probe of a set: the map onto `Bool` that is `true` at exactly
one argument.

For a two-valued range these are the source's identity and negation probes, which
is all the impossibility results use.-/
@[expose] public def IsProbe {A : Type v'} (f : A → Bool) (a : A) : Prop :=
  ∀ b : A, f b = true ↔ b = a

/-- The source's **identity probe** `f(y) = y` is the probe of `𝔹` at `true`.-/
public theorem isProbe_id : IsProbe (id : Bool → Bool) true := by
  intro b
  cases b
  · exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩
  · exact ⟨fun _ => rfl, fun _ => rfl⟩

/-- The source's **negation probe** `f(y) = -y` is the probe of `𝔹` at `false`.-/
public theorem isProbe_not : IsProbe (fun b : Bool => !b) false := by
  intro b
  cases b
  · exact ⟨fun _ => rfl, fun _ => rfl⟩
  · exact ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h⟩

/--
The canonical probe when the target range has decidable equality — a Kronecker
delta. Supplied for executable models; nothing in the theory requires it.-/
@[expose] public def probe {A : Type v'} [DecidableEq A] (a : A) : A → Bool :=
  fun b => decide (b = a)

public theorem isProbe_probe {A : Type v'} [DecidableEq A] (a : A) :
    IsProbe (probe a) a := by
  intro b; simp [probe]

/-- A probe is determined by the point it selects.-/
public theorem IsProbe.eq_of_isProbe {A : Type v'} {f g : A → Bool} {a : A}
    (hf : IsProbe f a) (hg : IsProbe g a) : f = g := by
  funext b
  cases hb : f b
  · have : ¬ (b = a) := fun hc => by simp [hf b |>.mpr hc] at hb
    cases hgb : g b
    · rfl
    · exact absurd (hg b |>.mp hgb) this
  · rw [hg b |>.mpr (hf b |>.mp hb)]

/-- **Definition 2 as printed:** unique-true *and* onto `Bool` *and* a second
point. Equivalent to `IsProbe` on every type the source considers.-/
@[expose] public def IsSourceProbe {A : Type v'} (f : A → Bool) (a : A) : Prop :=
  IsProbe f a ∧ Function.Surjective f ∧ ∃ b : A, b ≠ a

/-! ## Weak inference -/

/--
**Definition 3.** The device *weakly infers* a function `Γ`: for every probe of a
realized value of `Γ`, the device can be set up so that its conclusion answers
that probe throughout the resulting fibre.

The quantifier order is the content. It is *not* one rule that works everywhere;
it is one setup value per question, and the answer is only required on the fibre
that setup value induces. The source writes this `C > Γ`.-/
@[expose] public def WeaklyInfers (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) : Prop :=
  ∀ (γ : G) (f : G → Bool), IsProbe f γ → (∃ w : U, Γ w = γ) →
    ∃ x : C.Setup, C.Realized x ∧ ∀ w : U, C.setup w = x → C.concl w = f (Γ w)

/-- One device weakly infers another when it weakly infers its conclusion function.-/
@[expose] public def InfersDevice (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) : Prop :=
  WeaklyInfers C₁ C₂.concl

/-- Probe of the *image* of `Γ` — the paper's `π(Γ)`.-/
@[expose] public def IsProbeOnImage {G : Type v'} (Γ : U → G) (f : G → Bool)
    (γ : G) : Prop :=
  ∀ w : U, f (Γ w) = true ↔ Γ w = γ

/-! ## Distinguishability -/

/--
**Definition 4.** Two devices are *setup distinguishable* when every pair of
realized setup values is jointly realizable.

No device is distinguishable from itself once its setup takes two values, which is
why the source's Theorem 1 is not a statement about a device and its own copy.-/
@[expose] public def Distinguishable (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) : Prop :=
  ∀ x₁ : C₁.Setup, C₁.Realized x₁ → ∀ x₂ : C₂.Setup, C₂.Realized x₂ →
    ∃ w : U, C₁.setup w = x₁ ∧ C₂.setup w = x₂

/-! ## Every device fails some question -/

/-! ## Some device does infer -/

/--
**Proposition 1(i).** If a target takes at least two values on some subset `W`
which is neither empty nor everything, then a device weakly inferring it exists.

The source's construction, unchanged: the conclusion function is `false` exactly
on `W`, and the setup function separates the points of `W`. Given a probe at `γ`,
the device is set up to isolate a point of `W` where the target is *not* `γ` —
such a point exists precisely because the target takes two values on `W` — and
there both the conclusion and the probe read `false`.

Without this, the module would prove only that inference fails, never that it can
succeed.-/
@[expose] public def separatingDevice (inW : U → Bool)
    (hin : ∃ w : U, inW w = true) (hout : ∃ w : U, inW w = false) :
    InferenceDevice.{u, u} U where
  Setup := Option U
  setup := fun w => if inW w then some w else none
  concl := fun w => !(inW w)
  concl_surjective := by
    intro b
    cases b
    · obtain ⟨w, hw⟩ := hin; exact ⟨w, by simp [hw]⟩
    · obtain ⟨w, hw⟩ := hout; exact ⟨w, by simp [hw]⟩

/-! ## Theorem 1 — mutual weak inference is impossible between distinguishable devices -/

/--
**Theorem 1.** No two distinguishable devices can weakly infer each other.

The source's proof, unchanged: the identity probe forces the first device's
conclusion to agree with the second's on some fibre, the negation probe forces the
second's to disagree with the first's on some fibre, and distinguishability
supplies a universe in both fibres at once.-/
public theorem not_infersDevice_both_of_distinguishable
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hdist : Distinguishable C₁ C₂)
    (h₁₂ : InfersDevice C₁ C₂) (h₂₁ : InfersDevice C₂ C₁) : False := by
  obtain ⟨wt, hwt⟩ := C₂.concl_surjective true
  obtain ⟨x₁, hx₁, hfib₁⟩ := h₁₂ true id isProbe_id ⟨wt, hwt⟩
  obtain ⟨wf, hwf⟩ := C₁.concl_surjective false
  obtain ⟨x₂, hx₂, hfib₂⟩ := h₂₁ false (fun b => !b) isProbe_not ⟨wf, hwf⟩
  obtain ⟨w, hw₁, hw₂⟩ := hdist x₁ hx₁ x₂ hx₂
  have e₁ : C₁.concl w = C₂.concl w := hfib₁ w hw₁
  have e₂ : C₂.concl w = !(C₁.concl w) := hfib₂ w hw₂
  exact (Bool.self_ne_not (C₁.concl w)) (e₁.trans e₂)

/-! ## Strong inference -/

/--
**Definition 5.** The device *strongly infers* another when, for every probe of the
other's conclusion and every realized setup value of the other, it can be set up so
as to force that setup value **and** answer the probe.

This is the source's analogue of a universal Turing machine: the first device can
put the second into any configuration it likes and still report on it correctly.
The source writes this `C₁ ≫ C₂`.-/
@[expose] public def StronglyInfers (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) : Prop :=
  ∀ (γ : Bool) (f : Bool → Bool), IsProbe f γ → (∃ w : U, C₂.concl w = γ) →
    ∀ x₂ : C₂.Setup, C₂.Realized x₂ →
      ∃ x₁ : C₁.Setup, C₁.Realized x₁ ∧
        ∀ w : U, C₁.setup w = x₁ → C₂.setup w = x₂ ∧ C₁.concl w = f (C₂.concl w)

/-! ## Theorem 2 — strong inference dominates weak inference -/

/--
**Theorem 2(i).** Strong inference inherits weak inference: if the first device
strongly infers the second, then everything the second weakly infers, the first
weakly infers too.-/
@[grind →] public theorem weaklyInfers_of_stronglyInfers
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    {G : Type v''} {Γ : U → G}
    (hs : StronglyInfers C₁ C₂) (hw : WeaklyInfers C₂ Γ) :
    WeaklyInfers C₁ Γ := by
  intro γ f hf hγ
  obtain ⟨x₂, hx₂, hfib₂⟩ := hw γ f hf hγ
  obtain ⟨wt, hwt⟩ := C₂.concl_surjective true
  obtain ⟨x₁, hx₁, hfib₁⟩ := hs true id isProbe_id ⟨wt, hwt⟩ x₂ hx₂
  refine ⟨x₁, hx₁, fun w hw₁ => ?_⟩
  obtain ⟨hset₂, hconcl₁⟩ := hfib₁ w hw₁
  rw [hconcl₁]
  exact hfib₂ w hset₂

/-!
**Immediate consequence following Theorem 2.** Strong inference implies weak
inference of the target device's conclusion function. The source states this
immediately after Theorem 2(i) and (ii), without numbering it as a third part.
-/

/-! ## Control (section 7) -/

/--
**Definition 8, first half.** The device *semi-controls* a function when it can be
set up so as to force any realized value of that function.

Semi-control says nothing about the conclusion function: it is entirely a
statement about which fibres of the setup sit inside which fibres of the target.-/
@[expose] public def SemiControls (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) : Prop :=
  ∀ γ : G, (∃ w : U, Γ w = γ) →
    ∃ x : C.Setup, C.Realized x ∧ ∀ w : U, C.setup w = x → Γ w = γ

/--
**Definition 8, second half.** The device *controls* a function when, for every
probe and every truth value, it can be set up so that its conclusion **and** the
probe both take that value.

Control is strictly more than inference: inference requires the conclusion to
track the answer, control requires the device to be able to *set* the answer.-/
@[expose] public def Controls (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) : Prop :=
  ∀ (γ : G) (f : G → Bool), IsProbe f γ → (∃ w : U, Γ w = γ) → ∀ b : Bool,
    ∃ x : C.Setup, C.Realized x ∧
      ∀ w : U, C.setup w = x → C.concl w = b ∧ f (Γ w) = b

/-!
**Section 7 consequence.** Strong inference semi-controls the target device's
setup function. The conclusion component of strong inference is not enough to
semi-control the target conclusion function; the source explicitly distinguishes
these two claims.
-/

/-!
**Section 7 consequence, unrestricted range.** The source's statement that
control implies semi-control does not require decidable equality on the target
range. This classical form uses the generic probe-existence theorem; the theorem
above remains the constructive specialization for decidable ranges.
-/

/-! ## Corollary 3 — consequences of mutual semi-control of setups -/

/-- On `Bool`, the only probes are the source's identity and negation.-/
public theorem isProbe_bool {f : Bool → Bool} {γ : Bool} (hf : IsProbe f γ) :
    (γ = true ∧ f = id) ∨ (γ = false ∧ f = fun b => !b) := by
  cases γ
  · exact Or.inr ⟨rfl, IsProbe.eq_of_isProbe hf isProbe_not⟩
  · exact Or.inl ⟨rfl, IsProbe.eq_of_isProbe hf isProbe_id⟩

/-! ## Corollary 2 — cardinality of setup vs inferrability

The source: if `X` fine-grains `Y`, then `|X(U)| > 2` iff some function is
inferred. Forward: two setup blocks inside one `Y`-block give identity and
negation fibres. Reverse: `|X(U)| ≤ 2` and fine-graining force `X ≅ Y`, and
that pair answers no two-valued target.
-/

/-- Setup partition refines the conclusion partition: `X` fine-grains `Y`.-/
@[expose] public def SetupRefinesConcl (C : InferenceDevice.{u, v} U) : Prop :=
  ∀ w w' : U, C.setup w = C.setup w' → C.concl w = C.concl w'

/-- At least three distinct realized setup values — the source's `|X(U)| > 2`.-/
@[expose] public def ThreeSetupValues (C : InferenceDevice.{u, v} U) : Prop :=
  ∃ x₁ x₂ x₃ : C.Setup,
    C.Realized x₁ ∧ C.Realized x₂ ∧ C.Realized x₃ ∧
      x₁ ≠ x₂ ∧ x₁ ≠ x₃ ∧ x₂ ≠ x₃

/-- The paper's target for Cor 2, →: value `b` on setup-block `a` and on every
opposite-`Y` block; `¬b` on the other same-`Y` block.-/
public noncomputable def cor2Target (C : InferenceDevice.{u, v} U)
    (a : C.Setup) (b : Bool) : U → Bool := fun u =>
  have := Classical.propDecidable (C.setup u = a)
  have := Classical.propDecidable (C.concl u = b)
  if C.setup u = a ∨ C.concl u ≠ b then b else !b

/-! ## Proposition 2(ii) — existence of a strong inferrer

The source builds, on each fibre of `C` (size `> 2`), a partial device that
answers both probes of `Y` while forcing that fibre, then stitches. Here the
stitching is the identity setup on `U`: each `C'`-fibre is a singleton, so
strong inference reduces to finding, in every `C`-fibre, one point of
**agreement** (`Y' = Y`) and one of **disagreement** (`Y' = ¬Y`). The third
point makes `Y'` surjective on that fibre.
-/

/-- Every realized setup fibre contains at least three points.-/
@[expose] public def LargeSetupFibres (C : InferenceDevice.{u, v} U) : Prop :=
  ∀ x : C.Setup, C.Realized x →
    ∃ a b d : U, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧
      C.setup a = x ∧ C.setup b = x ∧ C.setup d = x

/-- Three distinct points of setup-fibre `x`.-/
@[expose] public def IsFibreTriple (C : InferenceDevice.{u, v} U) (x : C.Setup)
    (p : U × U × U) : Prop :=
  p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2 ∧
    C.setup p.1 = x ∧ C.setup p.2.1 = x ∧ C.setup p.2.2 = x

/-- A triple of fibre points for setup value `x`. Depends only on `x`.-/
public noncomputable def fibreTripleOf (C : InferenceDevice.{u, v} U)
    (x : C.Setup) : U × U × U :=
  let _ : Nonempty U := ⟨Classical.choose (C.concl_surjective true)⟩
  Classical.epsilon (IsFibreTriple C x)

/-- Under `LargeSetupFibres`, the chosen triple really is three fibre points.-/
public theorem fibreTripleOf_spec {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) {x : C.Setup} (hx : C.Realized x) :
    IsFibreTriple C x (fibreTripleOf C x) := by
  obtain ⟨u, hu⟩ := hx
  let _ : Nonempty U := ⟨u⟩
  refine Classical.epsilon_spec (p := IsFibreTriple C x) ?_
  obtain ⟨a, b, d, hab, had, hbd, ha, hb, hd⟩ := h x ⟨u, hu⟩
  exact ⟨(a, b, d), hab, had, hbd, ha, hb, hd⟩

public theorem fibreTripleOf_spec_at {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    IsFibreTriple C (C.setup u) (fibreTripleOf C (C.setup u)) :=
  fibreTripleOf_spec h ⟨u, rfl⟩

/-- Agreement / disagreement / spare point of a setup fibre.-/
public noncomputable def agreeOf (C : InferenceDevice.{u, v} U) (x : C.Setup) : U :=
  (fibreTripleOf C x).1

public noncomputable def disagreeOf (C : InferenceDevice.{u, v} U) (x : C.Setup) : U :=
  (fibreTripleOf C x).2.1

public noncomputable def spareOf (C : InferenceDevice.{u, v} U) (x : C.Setup) : U :=
  (fibreTripleOf C x).2.2

public noncomputable def agreePoint (C : InferenceDevice.{u, v} U) (u : U) : U :=
  agreeOf C (C.setup u)

public noncomputable def disagreePoint (C : InferenceDevice.{u, v} U) (u : U) : U :=
  disagreeOf C (C.setup u)

public noncomputable def sparePoint (C : InferenceDevice.{u, v} U) (u : U) : U :=
  spareOf C (C.setup u)

public theorem agreePoint_in_fibre {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    C.setup (agreePoint C u) = C.setup u :=
  (fibreTripleOf_spec_at h u).2.2.2.1

public theorem sparePoint_in_fibre {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    C.setup (sparePoint C u) = C.setup u :=
  (fibreTripleOf_spec_at h u).2.2.2.2.2

public theorem sparePoint_ne_agree {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    sparePoint C u ≠ agreePoint C u :=
  (fibreTripleOf_spec_at h u).2.1.symm

public theorem sparePoint_ne_disagree {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    sparePoint C u ≠ disagreePoint C u :=
  (fibreTripleOf_spec_at h u).2.2.1.symm

public theorem agreePoint_eq_of_setup_eq {C : InferenceDevice.{u, v} U}
    {u v : U} (heq : C.setup u = C.setup v) :
    agreePoint C u = agreePoint C v := by
  simp [agreePoint, heq]

/-- Proposition 2(ii) conclusion: agree with `C` at the agreement point,
disagree at the disagreement point, opposite of the agreement bit elsewhere.-/
public noncomputable def strongInferrerConcl (C : InferenceDevice.{u, v} U)
    (u : U) : Bool :=
  have := Classical.propDecidable (u = agreePoint C u)
  have := Classical.propDecidable (u = disagreePoint C u)
  if u = agreePoint C u then C.concl u
  else if u = disagreePoint C u then !(C.concl u)
  else !(C.concl (agreePoint C u))

public theorem strongInferrerConcl_agree {C : InferenceDevice.{u, v} U}
    (h : LargeSetupFibres C) (u : U) :
    strongInferrerConcl C (agreePoint C u) = C.concl (agreePoint C u) := by
  classical
  have hsa : C.setup (agreePoint C u) = C.setup u := agreePoint_in_fibre h u
  simp [strongInferrerConcl, agreePoint_eq_of_setup_eq hsa]

/-- **Proposition 2(ii) construction.** Identity setup; conclusion as above.-/
public noncomputable def strongInferrer (C : InferenceDevice.{u, v} U)
    (h : LargeSetupFibres C) : InferenceDevice.{u, u} U where
  Setup := U
  setup := id
  concl := strongInferrerConcl C
  concl_surjective := by
    classical
    intro b
    obtain ⟨w0, _⟩ := C.concl_surjective true
    let a := agreePoint C w0
    let s := sparePoint C w0
    have hsa : C.setup a = C.setup w0 := agreePoint_in_fibre h w0
    have hss : C.setup s = C.setup w0 := sparePoint_in_fibre h w0
    have hne : s ≠ a := sparePoint_ne_agree h w0
    have hne2 : s ≠ disagreePoint C w0 := sparePoint_ne_disagree h w0
    have hsConcl : strongInferrerConcl C s = !(C.concl a) := by
      unfold strongInferrerConcl
      have : agreePoint C s = a := agreePoint_eq_of_setup_eq hss
      have : disagreePoint C s = disagreePoint C w0 := by
        simp [disagreePoint, hss]
      rw [‹agreePoint C s = a›, ‹disagreePoint C s = disagreePoint C w0›,
        ite_eq_right hne, ite_eq_right hne2]
    cases b
    · cases ha : C.concl a
      · exact ⟨a, (strongInferrerConcl_agree h w0).trans ha⟩
      · exact ⟨s, hsConcl.trans (by simp [ha])⟩
    · cases ha : C.concl a
      · exact ⟨s, hsConcl.trans (by simp [ha])⟩
      · exact ⟨a, (strongInferrerConcl_agree h w0).trans ha⟩

end AISafetyAtlas.Inference
