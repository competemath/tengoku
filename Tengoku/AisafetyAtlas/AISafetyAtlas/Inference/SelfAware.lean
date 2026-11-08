module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Device
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Complexity
public import Tengoku.Seed.Data.Fintype.Card
public import Tengoku.Seed.SetTheory.Cardinal.Order
public import Tengoku.Seed.Data.Fintype.Prod
public import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/mbrcic/ai-safety-formalization-atlas@a65e32f80475, `AISafetyAtlas/Inference/SelfAware.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Self-aware devices — Wolpert 2008 §9

A self-aware device is a triple `(X, Y, Q)`: an inference device together with
a question function whose values are binary predicates on `U`. This is **not**
`Knowledge.Knowable` and **not** Wolpert 2018's physical-knowledge operator.
-/

namespace AISafetyAtlas.Inference

universe u v v' w w'

variable {U : Type u}

-- `linter.checkUnivs` (new at Lean v4.33) observes that these universes only
-- occur together and could be merged. Merging them changes a public
-- declaration's universe parameters, which is a statement change rather than
-- a toolchain fix; it is not made as part of a version bump.
/-- **Definition 12.**-/
public structure SelfAwareDevice (U : Type u) where
  toDevice : InferenceDevice.{u, v} U
  Question : Type w
  question : U → Question
  eval : Question → U → Bool
  pair_surjective :
    Function.Surjective (fun u : U => (toDevice.concl u, question u))

/-- The source's overline operator `Q̄`.-/
@[expose] public def SelfAwareDevice.ask (D : SelfAwareDevice.{u, v, w} U)
    (u : U) : Bool :=
  D.eval (D.question u) u

/-- **Definition 13(i).**-/
@[expose] public def Intelligible (D : SelfAwareDevice.{u, v, w} U)
    {G : Type v'} (Γ : U → G) : Prop :=
  ∀ (γ : G) (f : G → Bool), IsProbe f γ → (∃ w, Γ w = γ) →
    ∃ q : D.Question, (∃ u, D.question u = q) ∧ ∀ u, D.eval q u = f (Γ u)

/-- **Definition 13(ii).**-/
@[expose] public def Infallible (D : SelfAwareDevice.{u, v, w} U) : Prop :=
  ∀ u : U, D.toDevice.concl u = D.ask u

/-- **Definition 13(ii), relativized**, from the sentence after the printed clause:

> *"We say that `D` is infallible for `Q₀ ⊆ Q(U)` iff `∀q ∈ Q₀`, `∀u ∈ U` such
> that `Q(u) = q`, `Y(u) = q(u)`."*

Footnote 9's alternative definition of *correction* is stated in terms of this, so
it is not optional vocabulary.-/
@[expose] public def InfallibleFor (D : SelfAwareDevice.{u, v, w} U)
    (Q₀ : Set D.Question) : Prop :=
  ∀ q ∈ Q₀, ∀ u : U, D.question u = q → D.toDevice.concl u = D.eval q u

/-- `D'` is intelligible to `D` when `(Y', Q')` is.-/
@[expose] public def DeviceIntelligible (D : SelfAwareDevice.{u, v, w} U)
    (D' : SelfAwareDevice.{u, v', w'} U) : Prop :=
  Intelligible D (fun u => (D'.toDevice.concl u, D'.question u))

/-- The canonical probe at a realized value of `Γ`.-/
@[expose] public def canonProbe {G : Type v'} [DecidableEq G]
    {Γ : U → G} (z : {x // ∃ u, Γ u = x}) : G → Bool :=
  fun b => decide (b = z.1)

public theorem isProbe_canonProbe {G : Type v'} [DecidableEq G]
    {Γ : U → G} (z : {x // ∃ u, Γ u = x}) : IsProbe (canonProbe (Γ := Γ) z) z.1 :=
  fun b => by simp [canonProbe]

/-- The realized question that intelligibility supplies for the probe at `z`.
Paper Theorem 7: *each probe of `Γ` is a realized question.*-/
public noncomputable def intelligibleQuestion
    (D : SelfAwareDevice.{u, v, w} U) {G : Type v'} [DecidableEq G]
    {Γ : U → G} (hint : Intelligible D Γ) (z : {x // ∃ u, Γ u = x}) :
    {q // ∃ u, D.question u = q} :=
  ⟨(hint z.1 (canonProbe (Γ := Γ) z) (isProbe_canonProbe z) z.2).choose,
    (hint z.1 (canonProbe (Γ := Γ) z) (isProbe_canonProbe z) z.2).choose_spec.1⟩

/-- **Definition 14.** `C` corrects `D` when some setup fibre reports
whether `D` is answering its own question.-/
@[expose] public def Corrects (C : InferenceDevice.{u, v} U)
    (D : SelfAwareDevice.{u, v', w'} U) : Prop :=
  ∃ x : C.Setup, C.Realized x ∧
    ∀ w, C.setup w = x →
      C.concl w = decide (D.toDevice.concl w = D.ask w)

/-- A Definition-12 witness in the Atlas's relaxed model: same conclusion, one
constantly-false question (`PUnit` so the question universe matches). The paper's
two-question construction `Q ∈ {Y, ¬Y}` makes `Y⊗Q` miss two of the four pairs.
The replacement satisfies Definition 12, but not the paper's separate global
convention that every function considered has at least two image values; this is
why Proposition 7 remains `REPAIRED`, not source-exact. See the tracked source-
clash note.-/
public def uncorrectable (C : InferenceDevice.{u, v} U) :
    SelfAwareDevice.{u, v, w} U where
  toDevice := C
  Question := PUnit.{w + 1}
  question := fun _ => PUnit.unit
  eval := fun _ _ => false
  pair_surjective := by
    intro p
    obtain ⟨w, hw⟩ := C.concl_surjective p.1
    exact ⟨w, Prod.ext hw (by cases p.2; rfl)⟩

/-- The source's `Y₂ Q̄₂`: `true` exactly where the device answers its own
question. Definition 14 asks a second device to report this function.-/
@[expose] public def agreesWithQuestion (D : SelfAwareDevice.{u, v, w} U) : U → Bool :=
  fun u => decide (D.toDevice.concl u = D.ask u)

/-- **Footnote 9's alternative definition of correction.**

> *"Then we can modify the definition to say that `D₁` corrects `D₂` iff two
> conditions are met: all probes in `π(Y₂ Q̄₂)` are intelligible to `D₁`, and `D₁`
> is infallible for `π(Y₂ Q̄₂)`."*

Two things the footnote does not say, recorded rather than smoothed over:

* Definition 14's `D₁` is a **plain device**. This variant needs it to be
  **self-aware**, since intelligibility and infallibility are both defined only
  for those. The signature says so.
* `π(Y₂ Q̄₂)` is a set of probe *functions*, while `InfallibleFor` takes a set of
  `D₁`'s question labels. The two agree in the source, where `Q(U)` **is** a set of
  functions; here the second clause ranges over those labels of `D₁` whose
  evaluation is such a probe, which is the label-model reading of
  `π(Y₂ Q̄₂) ∩ Q₁(U)`.

No relation to `Corrects` is claimed. The footnote presents this as a different
definition, and Proposition 7 is stated for Definition 14.-/
@[expose] public def CorrectsAlt (C : SelfAwareDevice.{u, v, w} U)
    (D : SelfAwareDevice.{u, v', w'} U) : Prop :=
  Intelligible C (agreesWithQuestion D) ∧
    InfallibleFor C {q : C.Question |
      ∃ (γ : Bool) (f : Bool → Bool), IsProbe f γ ∧
        C.eval q = fun u => f (agreesWithQuestion D u)}

/-! ## Theorem 7(i) without finiteness

The source puts *"if `Q(U)` is finite"* in **(ii)**. Its **(i)** is an unrestricted
cardinality equality, so `Fintype.card` is a restriction the printed statement does
not carry. `Cardinal.mk` removes it: the three inequalities are the same
injections, and antisymmetry on `Cardinal` is Schröder–Bernstein, which is exactly
what the printed proof appeals to when it says two cardinalities that each dominate
the other are equal.

One restriction remains, and it is Lean's rather than the paper's: `Cardinal.mk`
compares types in a single universe, so the four types here share one. `thm7_card`
stays as the finite instance, where `Fintype.card : ℕ` sidesteps universes
entirely.
-/

/-- The realized questions inject into the labels their question map factors
through. Extracted from Theorem 7(i)'s proof, where it appeared twice inline,
and stated with the label type in its **own** universe.-/
@[expose] public noncomputable def questionLabel (D : SelfAwareDevice.{u, v, w} U)
    {P : Type p₀} (pMap : U → P) (R : P → D.Question)
    (_hQ : ∀ u, D.question u = R (pMap u))
    (z : {x // ∃ u, D.question u = x}) : {x // ∃ u, pMap u = x} :=
  ⟨pMap z.2.choose, ⟨z.2.choose, rfl⟩⟩

/-! ## Theorem 7(ii) — the realized questions *are* the probes

The source concludes an equality of **sets of functions** on `U`:
`Q′ = π(P) = π(Q)`. Questions here are a label type plus `eval`, so the
comparison is made after evaluation: `evalImage` is the set of binary functions
the device can actually ask, which is the source's `Q(U)`. Two labels with equal
`eval` collapse to one element of `evalImage`, exactly as the source's function
set would have them.
-/

/-- The source's `Q(U)`: the binary functions on `U` that `D` can ask,
recovered from the label model by evaluation.-/
@[expose] public def evalImage (D : SelfAwareDevice.{u, v, w} U) : Set (U → Bool) :=
  {g | ∃ q : D.Question, (∃ u, D.question u = q) ∧ D.eval q = g}

/-- The source's `π(P)`: probes of `P` at realized values, composed with `P`.-/
@[expose] public def probeImage {P : Type v'} (pMap : U → P) : Set (U → Bool) :=
  {g | ∃ (γ : P) (f : P → Bool), IsProbe f γ ∧ (∃ u, pMap u = γ) ∧
        g = fun u => f (pMap u)}

/-! ### The other half of Theorem 7(ii): `π(P) = π(Q)`

Printed (ii) is a chain, not one equality: *"`Q′ = π(P) = π(Q)` and
`Q = π(P′) = π(Q′)`"*. `thm7_ii` gives the outer equalities. The inner ones come
from `Q = R(P)` with equally many realized values, which forces `R` to be injective
on the image, so `P` and `Q` induce the same partition of `U` and therefore have the
same probes.
-/

/-! ## Self-aware inference complexity

Section 9 displays, in running prose rather than a numbered environment:

> *"one might want to modify the definition of inference complexity slightly for
> self-aware devices. Let `D` be a self-aware infallible device that
> semi-controls its question function and `Γ` a function over `U` where `Γ(U)` is
> countable and `Γ` is intelligible to `D`. Then rather than `𝒞(Γ ∣ (X,Y))`, it
> may be more appropriate to consider the self-aware inference complexity of `Γ`
> with respect to `D`, defined as*
>
> `𝒟(Γ ∣ (X,Y,Q)) ≜ Σ_{f ∈ π(Γ)} min_{x : X = x ⇒ Q = f(Γ)} [ℒ(x)]`

Definition 6 with the answering condition moved from the **conclusion** to the
**question**: a setup counts when it forces the device to be *asking* the probe,
regardless of what it then answers. Like `Ĉ`, it is a displayed definition that
no numbered environment announces.

**One interpretive choice, and it is Definition 12's.** `Q = f(Γ)` equates a
question with a function, and questions here are a label type plus `eval`
(clashes 9–10). The reading taken is the pointwise one already used by
`Intelligible`: the label the device asks at `u` *denotes* `f ∘ Γ`, i.e.
`∀ v, eval (question u) v = f (Γ v)`. That is the only reading under which the
source's own hypothesis — `Γ` intelligible to `D` — supplies the questions the
minimum ranges over.

The source's standing hypotheses for this display (infallible, semi-controls its
question function, `Γ(U)` countable, `Γ` intelligible) are **not** attached: the
object is defined for every self-aware device, and `ℒ` is a parameter as in
`inferenceComplexityTotal`, so counting measure and `−ln μ(X⁻¹(x))` are both
instances.
-/

open scoped Classical in
/-- The setups whose fibre forces the device to be **asking** the probe `f` of
`Γ` — the source's `X = x ⇒ Q = f(Γ)`.-/
@[expose] public noncomputable def questionAnsweringSet (D : SelfAwareDevice.{u, v, w} U)
    [DecidableEq D.toDevice.Setup] [FiniteRange D.toDevice.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) : Finset D.toDevice.Setup :=
  (realizedSetups D.toDevice).filter fun x =>
    ∀ u : U, D.toDevice.setup u = x → ∀ v : U, D.eval (D.question u) v = f (Γ v)

/-- The cheapest such setup, totalized by `0` where none exists — as
`minAnsweringLength` is.-/
@[expose] public noncomputable def minQuestionLength (D : SelfAwareDevice.{u, v, w} U)
    [DecidableEq D.toDevice.Setup] [FiniteRange D.toDevice.setup]
    (ℓ : D.toDevice.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  if h : (questionAnsweringSet D Γ f).Nonempty then
    (questionAnsweringSet D Γ f).inf' h ℓ
  else 0

/-- **Self-aware inference complexity**, `𝒟(Γ ∣ (X,Y,Q))`.-/
@[expose] public noncomputable def selfAwareInferenceComplexity
    (D : SelfAwareDevice.{u, v, w} U)
    [DecidableEq D.toDevice.Setup] [FiniteRange D.toDevice.setup]
    (ℓ : D.toDevice.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G)
    [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum fun γ => minQuestionLength D ℓ Γ (probe γ)

/-! ### Why Proposition 7 has no source-admissible witness on a small universe

`uncorrectable` takes `Question := PUnit`, one question value, and so violates
the paper's §1.2 stipulation that every function considered takes at least two
values. That is why Proposition 7 is graded `REPAIRED` rather than
`SOURCE-EXACT`, and it raises the question of whether an admissible witness
exists at all.

Half of that question has a short answer. Definition 12's `pair_surjective`
makes `u ↦ (Y(u), Q(u))` **onto** `𝔹 × Q(U)`, so an admissible self-aware
device — one whose question map takes at least two values, as §1.2 requires —
needs at least four states to exist. On `|U| ∈ {2, 3}` there is no admissible
self-aware device whatever, so the printed *"there is a self-aware device that
`C` cannot correct"* has nothing to quantify over and fails there.

The other half — whether an admissible witness exists for **every** device once
`|U| ≥ 4` — is open. It is not the same construction: `uncorrectable` sets
`D.toDevice := C`, and that choice cannot generally be made admissible, since
`(Y, Q)` surjective onto `𝔹 × Q(U)` fails outright when one of `C`'s conclusion
fibres is a singleton.
-/

/-! ## Definition 12 as the source prints it, and the encoding that represents it

Clash 9 records that questions here are a **label type plus `eval`** where the
source's `Q(U)` is a set of binary functions on `U`, and argues the encoding is a
generalization rather than a distortion: *"instantiating `Question` as the
source's `Q(U)` with `eval := id` recovers the printed model."* That was an
argument, not a theorem. It is a theorem now.

`FunctionValuedSelfAware` is Definition 12 read literally — a device together
with one binary function per state, and the printed surjectivity of `Y ⊗ Q` onto
`𝔹 × Q(U)`. `toSelfAware` is the representation, and the three theorems after it
say the representation loses nothing: the source's `Q̄` is the encoding's `ask`,
the evaluated questions are exactly the printed `Q(U)`, and the round trip is the
identity on both.
-/

/-- **Definition 12 as printed.** `Q` assigns a binary function on `U` to each
state, and `Y ⊗ Q` is onto `𝔹 × Q(U)` — the product with the **image**, which is
what the source writes.-/
public structure FunctionValuedSelfAware (U : Type u) where
  /-- The underlying device.-/
  toDevice : InferenceDevice.{u, v} U
  /-- The question at a state, as a binary function on `U`.-/
  askOf : U → (U → Bool)
  /-- `Y ⊗ Q` is onto `𝔹 × Q(U)`.-/
  pair_surjective : ∀ (b : Bool) (f : U → Bool), (∃ u, askOf u = f) →
    ∃ u, toDevice.concl u = b ∧ askOf u = f

/-- The printed device, represented in the label encoding: take the labels to be
the image of `Q` and `eval` to be the inclusion.-/
@[expose] public def FunctionValuedSelfAware.toSelfAware
    (F : FunctionValuedSelfAware.{u, v} U) : SelfAwareDevice.{u, v, u} U where
  toDevice := F.toDevice
  Question := {f : U → Bool // ∃ u, F.askOf u = f}
  question := fun u => ⟨F.askOf u, u, rfl⟩
  eval := fun f => f.1
  pair_surjective := by
    rintro ⟨b, ⟨f, u₀, hu₀⟩⟩
    obtain ⟨u, hb, hf⟩ := F.pair_surjective b f ⟨u₀, hu₀⟩
    exact ⟨u, by simp [hb, Subtype.ext_iff]; exact hf⟩

/-- The other direction: every device in the label encoding **is** a printed
device, by forgetting the labels.-/
@[expose] public def SelfAwareDevice.toFunctionValued
    (D : SelfAwareDevice.{u, v, w} U) : FunctionValuedSelfAware.{u, v} U where
  toDevice := D.toDevice
  askOf := fun u => D.eval (D.question u)
  pair_surjective := by
    rintro b f ⟨u₀, hu₀⟩
    obtain ⟨u, hu⟩ := D.pair_surjective (b, D.question u₀)
    refine ⟨u, ?_, ?_⟩
    · exact congrArg Prod.fst hu
    · rw [show D.question u = D.question u₀ from congrArg Prod.snd hu, hu₀]

/-! ## Proposition 7's positive half, at four states

`question_constant_of_card_lt_four` shows the printed existential **fails**
below four states, because no source-admissible self-aware device exists there
at all. The converse was left open twice, on the ground that `uncorrectable`
sets `D.toDevice := C` and that choice cannot generally be made admissible —
`(Y, Q)` onto `𝔹 × Q(U)` fails outright when one of `C`'s conclusion fibres is a
singleton.

That reasoning was right about `uncorrectable` and wrong about the proposition.
**`D`'s device is not required to be `C`.** Choosing it freely, with a
conclusion whose two fibres each hold two of four named states, makes
admissibility available for *every* `C`, and the evaluation can then be tuned so
that `Q̄` disagrees with `D`'s own conclusion exactly where `C` concludes `true`.
The agreement function is then `¬Y_C`, which no fibre of `C` can report, since
that would need `Y_C(w) = ¬Y_C(w)`.

So the printed proposition is **true at four or more states and false below**,
and the two theorems together settle it.
-/

section Prop7Positive

variable {a b c d : U}

/-- `D`'s conclusion: `true` on `{a, b}`, `false` on `{c, d}`. Both fibres hold
two of the four states, which is what `pair_surjective` needs.-/
@[expose] public def splitOn (a b : U) [DecidableEq U] : U → Bool :=
  fun u => decide (u = a ∨ u = b)

/-- `D`'s question map, chosen to cross `splitOn` so all four pairs are
realized.-/
@[expose] public def crossOn (a c : U) [DecidableEq U] : U → Bool :=
  fun u => decide (u = a ∨ u = c)

/-- `D`'s evaluation, tuned against `C`: it agrees with `D`'s own conclusion
exactly where `C` concludes `false`.-/
@[expose] public def tunedAsk [DecidableEq U] (C : InferenceDevice.{u, v} U)
    (a b : U) : U → Bool :=
  fun w => if C.concl w then !splitOn a b w else splitOn a b w

/-- **A source-admissible self-aware device that `C` cannot correct.** Its
question map takes two values — `crossOn` separates `a` from `b` — so it meets
the §1.2 stipulation `uncorrectable` violates, and **so does its setup map**,
which is `crossOn` as well. A `Unit` setup would satisfy Definition 12 while
violating the same stipulation the row exists to record.-/
@[expose] public def admissibleUncorrectable [DecidableEq U]
    (C : InferenceDevice.{u, v} U) (a b c d : U)
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hcd : c ≠ d) :
    SelfAwareDevice.{u, 0, 0} U where
  toDevice :=
    { Setup := Bool
      -- The setup map is two-valued, as §1.2 requires of every function
      -- considered. A `Unit` setup would satisfy Definition 12 and violate the
      -- paper's own stipulation, which is the defect this whole row is about.
      setup := crossOn a c
      concl := splitOn a b
      concl_surjective := by
        intro t
        cases t with
        | true => exact ⟨a, by simp [splitOn]⟩
        | false => exact ⟨c, by simp [splitOn, hac.symm, hbc.symm]⟩ }
  Question := Bool
  question := crossOn a c
  eval := fun _ => tunedAsk C a b
  pair_surjective := by
    rintro ⟨t, q⟩
    cases t <;> cases q
    · exact ⟨d, by simp [splitOn, crossOn, had.symm, hbd.symm, hcd.symm]⟩
    · exact ⟨c, by simp [splitOn, crossOn, hac.symm, hbc.symm]⟩
    · exact ⟨b, by simp [splitOn, crossOn, hab.symm, hbc]⟩
    · exact ⟨a, by simp [splitOn, crossOn]⟩

end Prop7Positive

/-! ## §9's `𝒟` over an arbitrary setup range

`questionAnsweringSet` is a `Finset`, so `selfAwareInferenceComplexity` carries
`[FiniteRange D.toDevice.setup]` where §9 inherits Definition 6's **countable**
setup range. This is the same restriction `answeringSetOn` removed for
Definition 6, and it comes off the same way: the printed `min` needs the minimum
to **exist**, not the index to be finite.
-/

/-- The setups whose question, evaluated, is the probe — as a **set**.-/
@[expose] public def questionAnsweringSetOn (D : SelfAwareDevice.{u, v, w} U)
    {G : Type v'} (Γ : U → G) (f : G → Bool) : Set D.toDevice.Setup :=
  {x | D.toDevice.Realized x ∧
    ∀ u : U, D.toDevice.setup u = x → ∀ v : U, D.eval (D.question u) v = f (Γ v)}

/-- The printed `min` over them, as an infimum.-/
@[expose] public noncomputable def minQuestionLengthOn (D : SelfAwareDevice.{u, v, w} U)
    (ℓ : D.toDevice.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  sInf (ℓ '' questionAnsweringSetOn D Γ f)

/-- **§9's `𝒟` with no finiteness on the setup range.**-/
@[expose] public noncomputable def selfAwareInferenceComplexityOn
    (D : SelfAwareDevice.{u, v, w} U) (ℓ : D.toDevice.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum fun γ => minQuestionLengthOn D ℓ Γ (probe γ)

end AISafetyAtlas.Inference
