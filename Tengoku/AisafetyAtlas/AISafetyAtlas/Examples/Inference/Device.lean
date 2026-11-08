module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Knowledge.Ambiguity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inference devices — worked models

Five things this file settles, none of which the abstract development settles on
its own.

1. **Weak inference is not vacuous.** `witnessInfers` really does weakly infer a
   target, built the way Wolpert's Proposition 1(i) builds one: a conclusion
   function that is `false` exactly on a distinguishing set, and a setup that
   separates that set's points.
2. **Theorem 1 has a genuine instance.** A distinguishable pair in which *one*
   direction of weak inference holds, so distinguishability is what rules out the
   other. (A pair where neither direction holds does not exercise the theorem.)
3. **Weak inference is not knowability, in either direction.** Both countermodels
   are here, and they are why the relationship to the atlas knowability kernel is
   recorded as `RELATED` rather than as a definitional identification. That is the
   *kernel* relationship; BY-024's own grade against Wolpert 2008 is separate.
4. **Strong inference, control, Theorem 5 and Corollary 3 are inhabited.**
   `StronglyInfers` has a positive witness; `Controls` has a positive witness;
   a shared-setup pair exhibits mutual weak inference, identical partitions, and
   the failure of either to control that setup. A constant-setup device is
   distinguishable from itself — the source excludes that case.
5. **Section 9's Theorem 6 hypotheses are inhabited.** `saDev` instantiates
   Theorem 6(i); `saStrongDev` and `saTargetDevice` instantiate the strictly
   stronger setup-pair hypotheses of Theorem 6(ii). Before these witnesses, the
   only `SelfAwareDevice` in the tree was Proposition 7's `uncorrectable`.

Every model is finite and every check is `decide`-able.
-/

namespace AISafetyAtlas.Examples.Inference.Device

open AISafetyAtlas.Inference
open AISafetyAtlas.Knowledge

/-! ## 1. Weak inference is not vacuous -/

/-- Wolpert's Proposition 1(i) conclusion function: `false` exactly on the
distinguishing set `W = {0, 1}`.-/
public abbrev wConcl : Fin 3 → Bool
  | 0 => false
  | 1 => false
  | 2 => true

public theorem wConcl_surjective : Function.Surjective wConcl := by
  intro b
  cases b
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩

/-- The setup separates the points of `W`, as the construction requires.-/
public abbrev witnessInfers : InferenceDevice (Fin 3) where
  Setup := Fin 3
  setup := id
  concl := wConcl
  concl_surjective := wConcl_surjective

/-- A target taking both values on `W`.-/
public abbrev wTarget : Fin 3 → Bool
  | 0 => true
  | 1 => false
  | 2 => true

/-! ## 2. Theorem 1 — one direction holds, distinguishability kills the other

Wolpert's grid: the row device can match the column device's conclusion on one
row and mismatch it on the other, so it weakly infers that conclusion. The two
setups are independent, so Theorem 1 forbids the reverse. Independent coordinates
with matching conclusions would not exercise the theorem, so that rejected pair
is not retained as a public example.
-/

/-- Row index as setup; conclusion equals the column on row `false` and its
negation on row `true`.-/
public abbrev rowDevice : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := fun p => xor p.1 p.2
  concl_surjective := fun b => ⟨(false, b), by cases b <;> rfl⟩

/-- Column index as setup; conclusion is the column.-/
public abbrev colDevice : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.snd
  concl := Prod.snd
  concl_surjective := fun b => ⟨(b, b), rfl⟩

/-! ## 3. Weak inference is not knowability

The two countermodels behind the `RELATED` relationship.
-/

/-- Setup is the identity, so the target factors through it — but the device's
conclusion is the negation, and a device's conclusion function is fixed, not
chosen the way a decoder is.-/
public abbrev negDevice : InferenceDevice Bool where
  Setup := Bool
  setup := id
  concl := not
  concl_surjective := fun b => ⟨!b, by cases b <;> rfl⟩

/-- The converse failure. This setup cannot separate `1` from `2`.-/
public abbrev coarseConcl : Fin 3 → Bool
  | 0 => true
  | 1 => false
  | 2 => true

public theorem coarseConcl_surjective : Function.Surjective coarseConcl := by
  intro b
  cases b
  · exact ⟨1, rfl⟩
  · exact ⟨0, rfl⟩

/-- The target for the second countermodel. It is deliberately *not* the device's
conclusion function: the negation probe has to be answerable somewhere.-/
public abbrev coarseTarget : Fin 3 → Bool
  | 0 => true
  | 1 => true
  | 2 => false

/-- Two setup values only: `0`, and everything else.-/
public abbrev coarseDevice : InferenceDevice (Fin 3) where
  Setup := Bool
  setup := fun i => decide (i = 0)
  concl := coarseConcl
  concl_surjective := coarseConcl_surjective

/-! ## 4. Corollary 1(ii) needs a hypothesis the source leaves implicit

Wolpert's Corollary 1(ii) reads: *"For any function `Γ` with domain `U` there is a
device that infers `Γ`."* It is offered as a consequence of Proposition 1(i), which
requires a **proper** subset `W ⊂ U` on which `Γ` already attains all its values.

When `Γ` is injective and `U` has no spare state, no such `W` exists — and the
conclusion fails outright, not merely the construction. Two states suffice to show
it.

The failure depends on reading `∃ x` as ranging over *realized* setup values, which
is the source's own convention in Definition 3 (`∃ x ∈ X(U)`). Allowing an
unrealized setup value would make weak inference vacuously true and the corollary
trivially so.

This is a missing hypothesis, not a broken theorem: on a set of universes large
enough for some value of `Γ` to be attained twice, Proposition 1(i) applies and the
corollary holds. It is recorded because the atlas grades statements, not intentions.
-/

/-- **No device over a two-state universe weakly infers the identity.** Whichever
setup values answer the two probes, the conclusion function is forced to be
constant, contradicting its surjectivity.-/
public theorem no_device_weaklyInfers_id_on_bool :
    ¬ ∃ C : InferenceDevice.{0, 0} Bool, WeaklyInfers C (id : Bool → Bool) := by
  rintro ⟨C, h⟩
  obtain ⟨x₁, ⟨w₁, hw₁⟩, hf₁⟩ := h true id isProbe_id ⟨true, rfl⟩
  obtain ⟨x₂, ⟨w₂, hw₂⟩, hf₂⟩ := h false (fun b => !b) isProbe_not ⟨false, rfl⟩
  have e₁ : C.concl w₁ = w₁ := hf₁ w₁ hw₁
  have e₂ : C.concl w₂ = !w₂ := hf₂ w₂ hw₂
  by_cases hx : x₁ = x₂
  · -- one fibre answers both probes, so its states must disagree with themselves
    subst hx
    have := hf₂ w₁ hw₁
    rw [e₁] at this
    cases w₁ <;> simp at this
  · -- distinct fibres exhaust a two-state universe, forcing a constant conclusion
    have hne : w₁ ≠ w₂ := by
      intro hc; apply hx; rw [← hw₁, ← hw₂, hc]
    have hconst : ∀ v : Bool, C.concl v = C.concl w₁ := by
      intro v
      cases w₁ <;> cases w₂ <;> simp_all <;> cases v <;> simp_all
    obtain ⟨b, hb⟩ := C.concl_surjective (!(C.concl w₁))
    rw [hconst b] at hb
    exact Bool.self_ne_not _ hb

/-! ## 5. Constant setup — self-distinguishability

The source says no device is distinguishable from itself, under its global
two-value stipulation on every function. Dropping that on *setups* makes a
constant-setup device distinguishable from itself.
-/

public abbrev constSetupDevice : InferenceDevice Bool where
  Setup := Unit
  setup := fun _ => ()
  concl := id
  concl_surjective := fun b => ⟨b, rfl⟩

/-! ## 6. Strong inference is satisfiable

Each coarse fibre must contain a point where the fine conclusion agrees with the
coarse conclusion and a point where it disagrees, so both probes can be answered
while forcing the coarse setup.
-/

public abbrev fineDevice : InferenceDevice (Fin 4) where
  Setup := Fin 4
  setup := id
  concl := fun i => decide (i.val < 2)
  concl_surjective := by
    intro b
    cases b
    · exact ⟨2, rfl⟩
    · exact ⟨0, rfl⟩

public abbrev coarseForcedDevice : InferenceDevice (Fin 4) where
  Setup := Bool
  setup := fun i => decide (2 ≤ i.val)
  concl := fun i => decide (i.val % 2 = 1)
  concl_surjective := by
    intro b
    cases b
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

/-! ## 7. Control is satisfiable

Singleton fibres: pick the pair `(desired conclusion bit, target value)` so the
probe and the conclusion both equal the requested bit.
-/

public abbrev controlDevice : InferenceDevice (Bool × Bool) where
  Setup := Bool × Bool
  setup := id
  concl := Prod.fst
  concl_surjective := fun b => ⟨(b, b), rfl⟩

/-! ## 8. Shared setup — Theorem 5 and Corollary 3 -/

/-- Shared setup `Prod.fst`. Conclusion is the second bit.-/
public abbrev sharedSetupLeft : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

/-- Same setup; conclusion equals the second bit on `{true}×_` and its
negation on `{false}×_`. The two fibres are exactly the identity and negation
witnesses of Corollary 3(i).-/
public abbrev sharedSetupRight : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := fun p => decide (p.1 = p.2)
  concl_surjective := by
    intro b
    cases b
    · exact ⟨(false, true), rfl⟩
    · exact ⟨(true, true), rfl⟩

/-! ## 9. Definition 7 across two universes

Definition 7 opens *"Let `U` and `Û` be two (perhaps identical) sets"* — copies
across different realities are the concept. These two devices live over `Bool` and
over `Fin 2` and realize the same `(setup, conclusion)` pairs, so each mimics the
other. A same-universe `Copies` API could not state this.
-/

public abbrev boolDev : InferenceDevice Bool where
  Setup := Bool
  setup := id
  concl := id
  concl_surjective := fun b => ⟨b, rfl⟩

public abbrev fin2Dev : InferenceDevice (Fin 2) where
  Setup := Bool
  setup := fun i => decide (i = 1)
  concl := fun i => decide (i = 1)
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨1, rfl⟩

/-! ## 10. Section 8 has an inhabited model

Definitions 9–11 take a probability measure. This is one, so the stochastic layer
is not a set of formulas with no instance.
-/

/-- The uniform mass on a two-state universe.-/
@[expose] public noncomputable def uniformBool : FinPMF Bool where
  mass := fun _ => 1 / 2
  nonneg := fun _ => by norm_num
  sum_one := by simp

/-! ## 11. Proposition 6 is not vacuous — the paper's own extremal example

The source's remark after Proposition 6: *"The maximum for `α = β = 1/2` can occur
in several ways. One is when `z₁ = 1`, and `z₂, z₃, z₄` all equal `0`. At these
values, both devices have an inference accuracy of `1/2` at inferring each other."*

That is this model. `U` is the four-point square with the uniform measure, so the
two setups `X₁ = fst` and `X₂ = snd` are independent and `α = β = 1/2`. Each cell
is a single universe, so each `zᵢ` is `0` or `1`; the conclusions are chosen to
agree exactly on `(false, false)`, giving `z = (1, 0, 0, 0)`.

Without this, `prop6_product_eq` would be a theorem whose hypothesis nothing is
known to satisfy.
-/

/-- `Y₁ = 1` exactly on the left column.-/
public abbrev p6dev1 : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.fst
  concl := fun q => !q.1
  concl_surjective := fun
    | true => ⟨(false, false), rfl⟩
    | false => ⟨(true, false), rfl⟩

/-- `Y₂ = -1` exactly at `(false, true)`, so `Y₁ = Y₂` only at `(false, false)`.-/
public abbrev p6dev2 : InferenceDevice (Bool × Bool) where
  Setup := Bool
  setup := Prod.snd
  concl := fun q => q.1 || !q.2
  concl_surjective := fun
    | true => ⟨(true, false), rfl⟩
    | false => ⟨(false, true), rfl⟩

/-- The uniform measure on the square. `X₁` and `X₂` are then independent, which
is what the source's step 2 needs.-/
@[expose] public noncomputable def p6pmf : FinPMF (Bool × Bool) where
  mass := fun _ => 1 / 4
  nonneg := fun _ => by norm_num
  sum_one := by simp

public theorem p6dev1_mass_false : setupMass p6pmf p6dev1 false = 1 / 2 := by
  have h : (Finset.univ.filter (fun u : Bool × Bool => u.1 = false)).card = 2 := by decide
  norm_num [setupMass, pushOnImage, p6pmf, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_bool, h]

public theorem p6dev1_mass_true : setupMass p6pmf p6dev1 true = 1 / 2 := by
  have h : (Finset.univ.filter (fun u : Bool × Bool => u.1 = true)).card = 2 := by decide
  norm_num [setupMass, pushOnImage, p6pmf, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_bool, h]

public theorem p6dev2_mass_false : setupMass p6pmf p6dev2 false = 1 / 2 := by
  have h : (Finset.univ.filter (fun u : Bool × Bool => u.2 = false)).card = 2 := by decide
  norm_num [setupMass, pushOnImage, p6pmf, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_bool, h]

public theorem p6dev2_mass_true : setupMass p6pmf p6dev2 true = 1 / 2 := by
  have h : (Finset.univ.filter (fun u : Bool × Bool => u.2 = true)).card = 2 := by decide
  norm_num [setupMass, pushOnImage, p6pmf, Finset.sum_filter,
    Fintype.sum_prod_type, Fintype.sum_bool, h]

/-! ### Proposition 6's *printed* premise, witnessed

`p6_law` witnesses `Prop6Law`, and `p6_setups_independent` witnesses independence.
Neither witnesses what Proposition 6 actually assumes: **mutual-information
distinguishability `1`**. Without that, `prop6_half_of_miDistinguishability_eq_one`
is a theorem whose hypothesis was never shown satisfiable.

The uniform square supplies it. Both setups are fair coins, so each carries
entropy `log 2`, and they are independent, so the mutual information vanishes and
the Definition 10 ratio is `1 − 0/(2 log 2) = 1`. -/

private theorem p6dev1_image :
    Finset.univ.image p6dev1.setup = {false, true} :=
  image_setup_eq_pair p6dev1 ⟨(false, false), rfl⟩ ⟨(true, false), rfl⟩
    (fun w => by cases h : w.1 <;> simp [p6dev1, h])

private theorem p6dev2_image :
    Finset.univ.image p6dev2.setup = {false, true} :=
  image_setup_eq_pair p6dev2 ⟨(false, false), rfl⟩ ⟨(false, true), rfl⟩
    (fun w => by cases h : w.2 <;> simp [p6dev2, h])

private theorem p6_entropy_dev1 : setupEntropy p6dev1 p6pmf = Real.log 2 := by
  unfold setupEntropy shannonEntropyOn
  rw [p6dev1_image, Finset.sum_insert (by simp), Finset.sum_singleton]
  rw [show pushOnImage p6pmf p6dev1.setup false = 1 / 2 from p6dev1_mass_false,
    show pushOnImage p6pmf p6dev1.setup true = 1 / 2 from p6dev1_mass_true]
  rw [ite_eq_right (by norm_num : (1 : ℝ) / 2 ≠ 0)]
  have hlog : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

private theorem p6_entropy_dev2 : setupEntropy p6dev2 p6pmf = Real.log 2 := by
  unfold setupEntropy shannonEntropyOn
  rw [p6dev2_image, Finset.sum_insert (by simp), Finset.sum_singleton]
  rw [show pushOnImage p6pmf p6dev2.setup false = 1 / 2 from p6dev2_mass_false,
    show pushOnImage p6pmf p6dev2.setup true = 1 / 2 from p6dev2_mass_true]
  rw [ite_eq_right (by norm_num : (1 : ℝ) / 2 ≠ 0)]
  have hlog : Real.log (1 / 2) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hlog]
  ring

/-! ## Section 9 — an infallible self-aware device

Before the witnesses below were added, the positive hypotheses of Theorem 6
were uninhabited. The only `SelfAwareDevice` then in the tree was
`uncorrectable`, constructed inside Proposition 7's proof, whose question
function is constant and which is **not** infallible. The examples below now
inhabit both halves of Theorem 6. They do not claim to inhabit every positive
hypothesis elsewhere in section 9.

`saU = 𝔹 × 𝔹`. The first bit names the question, the second is the fact asked about.
Question `true` asks *"is the second bit set?"*; question `false` asks its negation.
The device answers by evaluating its own question, so it is infallible by
construction, and its setup **is** its question, so it semi-controls it.
-/

/-- The universe of the section 9 witness.-/
public abbrev saU : Type := Bool × Bool

/-- Question `true` asks *"is the second bit set?"*; `false` asks the negation.-/
public abbrev saEval : Bool → saU → Bool := fun q u => if q then u.2 else !u.2

public abbrev saDevice : InferenceDevice saU where
  Setup := Bool
  setup := Prod.fst
  concl := fun u => saEval u.1 u
  concl_surjective := fun
    | true => ⟨(true, true), rfl⟩
    | false => ⟨(true, false), rfl⟩

/-- **Definition 12** inhabited: `Y ⊗ Q` hits all four pairs.-/
public abbrev saDev : SelfAwareDevice saU where
  toDevice := saDevice
  Question := Bool
  question := Prod.fst
  eval := saEval
  pair_surjective := by decide

/-! ### Theorem 6(ii) — the stronger hypotheses are inhabited -/

/-- Identity setup makes each setup fibre a singleton, so it can semi-control the
question/setup pair used by Theorem 6(ii).-/
public abbrev saStrongDevice : InferenceDevice saU where
  Setup := saU
  setup := id
  concl := fun u => saEval u.1 u
  concl_surjective := fun
    | true => ⟨(true, true), rfl⟩
    | false => ⟨(true, false), rfl⟩

public abbrev saStrongDev : SelfAwareDevice saU where
  toDevice := saStrongDevice
  Question := Bool
  question := Prod.fst
  eval := saEval
  pair_surjective := by decide

/-- The target device exposes the second bit as both setup and conclusion.-/
public abbrev saTargetDevice : InferenceDevice saU where
  Setup := Bool
  setup := Prod.snd
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

/-! ## Proposition 3(ii)'s hypothesis, inhabited

`not_mutually_distinguishable_weak_cycle` derives a contradiction from mutual
distinguishability plus a weak-inference cycle. If no reality were mutually
distinguishable the theorem would hold for nothing, so the hypothesis needs a
model of its own — separately from the cycle, which the theorem refutes.

The uniform square is one: the two setups are the two coordinates, so **every**
pair of setup values is realized, by the state that has them. -/

public abbrev mutualReality : DeviceReality (Bool × Bool) 2
  | ⟨0, _⟩ => p6dev1
  | ⟨1, _⟩ => p6dev2

/-! ## Proposition 4's hypotheses, inhabited

`unique_strong_root` asks for a weakly connected strong-inference graph whose
incomparable pairs are distinguishable, every device carrying two realized setup
values. Nothing satisfied that, so the unique root was a root of nothing.

Two devices suffice, and one strong-inference edge is already here:
`fineDevice ≫ coarseForcedDevice`. Connectivity is that single edge, and the
distinguishability clause is **vacuous** — it constrains only pairs that are
incomparable, and these two are comparable. -/

public abbrev prop4Reality : DeviceReality (Fin 4) 2
  | ⟨0, _⟩ => fineDevice
  | ⟨1, _⟩ => coarseForcedDevice

/-! ## Theorem 7's hypotheses, inhabited

Theorem 7 asks for a pair of self-aware devices, each finding the other's `P` map
intelligible. Nothing satisfied that either, and it was not obvious that anything
could: Corollary 4 forbids mutual *device*-intelligibility whenever the question
ranges are finite, and this premise is adjacent to it.

It is satisfiable, and the reason Corollary 4 does not block it is that
intelligibility here is of the **question map alone**, not of the pair `(Y, Q)`.
A device with a single constantly-true question finds any single-valued map
intelligible, because the only probe of a one-point range is the constant `true`.

This witness is degenerate: `|Q(U)| = 1`. A non-degenerate one follows it below —
`saSelfProbe`, whose questions are the probes of its own question map, so
`|Q(U)| = 2`. It was reached by taking the condition this note stated as the
obstacle (*"would have to ask, as one of its own questions, every probe of the
other's question map"*) and building the device that satisfies it. -/

public abbrev saTrivialDevice : InferenceDevice saU where
  Setup := Bool
  setup := Prod.fst
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

/-- A Definition-12 device whose single question is constantly true.-/
public abbrev saTrivial : SelfAwareDevice saU where
  toDevice := saTrivialDevice
  Question := PUnit
  question := fun _ => PUnit.unit
  eval := fun _ _ => true
  pair_surjective := by
    rintro ⟨b, ⟨⟩⟩
    exact ⟨(false, b), rfl⟩

/-! ## A non-degenerate Theorem 7 witness, and the section-9 prose definitions

The paragraph above left one thing open: whether Theorem 7's mutual-intelligibility
premise can be met with more than one question. It can, and the device that meets
it is exactly the one the previous note described — *"a device whose question range
has two or more values would have to ask, as one of its own questions, every probe
of the other's question map"*. Make the two devices the same one, and make its
questions the probes of its own question function.

`saSelfProbe` asks, at question `q`, *"is my question `q`?"* — `eval q u =
⟦Q(u) = q⟧`. Then `eval q` **is** the probe of `Q` at `q`, so `Q` is intelligible
to it, and `Q` takes two values. `|Q(U)| = 2`, against `saTrivial`'s `1`.

The same device settles three prose items at once. Its conclusion is the second
bit while its own question is always answered `true`, so it is fallible
everywhere, and `Y Q̄` — the source's `agreesWithQuestion` — is the second bit.
That is a function `saDev` finds intelligible, so footnote 9's alternative
correction relation `CorrectsAlt` holds between them. -/

public abbrev saSelfProbeDevice : InferenceDevice saU where
  Setup := Bool
  setup := Prod.fst
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

/-- Its questions are the probes of its own question function: `q(u) = ⟦Q(u) = q⟧`.-/
public abbrev saSelfProbe : SelfAwareDevice saU where
  toDevice := saSelfProbeDevice
  Question := Bool
  question := Prod.fst
  eval := fun q u => decide (u.1 = q)
  pair_surjective := by decide

/-! ### `InfallibleFor` is strictly between nothing and `Infallible`

The relativized clause would be idle vocabulary if every device that satisfied it
on a nonempty question set were infallible outright. `saPartial` answers question
`true` correctly and question `false` backwards, so it is infallible for `{true}`
and not infallible. -/

public abbrev saPartialDevice : InferenceDevice saU where
  Setup := Bool
  setup := Prod.fst
  concl := Prod.snd
  concl_surjective := fun b => ⟨(false, b), rfl⟩

public abbrev saPartial : SelfAwareDevice saU where
  toDevice := saPartialDevice
  Question := Bool
  question := Prod.fst
  eval := saEval
  pair_surjective := by decide

/-! ## Definition 11, computed

`countingDistinguishability` had no worked instance — a gap the module-level
coverage gate cannot see, since `Stochastic.lean` has other coverage, and one the
declaration dependency view surfaced as a definition no statement and no example
mentions.

On the uniform square every pair of setup values is jointly realized, so the
fraction of unrealized pairs is `0`. That is the same fact
`mutualReality_mutuallyDistinguishable` records qualitatively, now as Definition
11's number. -/

/-! ## The `|U| > 3` sentence — hypotheses inhabited

A one-device reality whose extra-function family is that device's own
conclusion. `func_two` holds by surjectivity onto `Bool` — the honesty check
the repaired row needs — and the device is then not universal, on any `U`.
-/

public def conclInFamilyReality :
    FullReality Bool (fun _ : Unit => Bool) (fun _ : Unit => Bool) where
  setupOf := fun _ => id
  conclOf := fun _ => id
  funcOf := fun _ => id

end AISafetyAtlas.Examples.Inference.Device
