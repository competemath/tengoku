module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Device
public import Tengoku.Seed.Data.Fintype.Card
public import Tengoku.Seed.Data.Finset.Max
public import Tengoku.Seed.Logic.Equiv.Defs
public import Tengoku.Seed.Logic.Relation
public import Tengoku.Seed.Tactic.FinCases
public import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Realities and copies — Wolpert 2008 §6

A *reality* is a universe together with a family of devices and a family of
arbitrary functions over it.

* **Definition 7** is mimicry and copies, `Mimics` / `Copies`, stated across two
  universes as the source requires.
* **Lemma 1** is `lemma1_reducedForm_iff_admissible`: the reduced forms of
  realities are exactly the admissible tuple families, `K₁ = K₂`.
* **Propositions 3–5** are the graph constraints: a pairwise-distinguishable
  weak-inference 3-cycle exists; a mutually distinguishable weak-inference cycle
  does not; a strong-inference cycle does not; copies may one-way weakly infer
  (finite) and may strongly infer only if infinite.

`DeviceReality` — used by Propositions 3 and 4 — is a **finite** family
`Fin n → InferenceDevice` over one universe. Each device may have a different
setup type, and those types are universe-polymorphic. The
source's reality may be countably infinite and carries the extra functions
`{Γ_β}`; those live in `FullReality`, which Lemma 1 uses. Propositions 3 and 4 are
therefore finite-subgraph statements, which is what their conclusions need.

**Proposition 3(ii).** The source defines *"mutually (setup) distinguishable"* in
prose just before Proposition 3: *"the reality as a whole is mutually (setup)
distinguishable iff `∀ x₁ ∈ X₁(U), x₂ ∈ X₂(U), … ∃ u ∈ U` s.t.
`X₁(u) = x₁, X₂(u) = x₂, …`"*. That is `n`-wise joint realizability, which is
`MutuallyDistinguishable` verbatim, and is strictly stronger than the pairwise
distinguishability of Definition 4 — as it must be, since Proposition 3(i) exhibits
a *pairwise*-distinguishable weak cycle.
-/

namespace AISafetyAtlas.Inference

universe u v

variable {U : Type u}

/-- A finite family of devices over one universe; setup types may differ.-/
@[expose] public def DeviceReality (U : Type u) (n : ℕ) : Type _ :=
  Fin n → InferenceDevice.{u, v} U

/-- Pairwise setup-distinguishability.-/
@[expose] public def PairwiseDistinguishable {n : ℕ} (R : DeviceReality U n) : Prop :=
  ∀ i j : Fin n, i ≠ j → Distinguishable (R i) (R j)

/-- Mutual setup-distinguishability: every tuple of realized setups is
jointly realized.-/
@[expose] public def MutuallyDistinguishable {n : ℕ} (R : DeviceReality U n) : Prop :=
  ∀ x : (i : Fin n) → (R i).Setup,
    (∀ i, (R i).Realized (x i)) →
      ∃ w : U, ∀ i, (R i).setup w = x i

/-- Successor on `Fin n`, wrapping. Needs `n ≠ 0`.-/
public def finSuccMod {n : ℕ} [NeZero n] (i : Fin n) : Fin n := i + 1

/-- Directed weak-inference edges `R i > R (i+1)`, wrapping.-/
@[expose] public def WeakInferenceCycle {n : ℕ} [NeZero n]
    (R : DeviceReality U n) : Prop :=
  ∀ i : Fin n, InfersDevice (R i) (R (finSuccMod i))

/-- Directed strong-inference edges, wrapping.-/
@[expose] public def StrongInferenceCycle {n : ℕ} [NeZero n]
    (R : DeviceReality U n) : Prop :=
  ∀ i : Fin n, StronglyInfers (R i) (R (finSuccMod i))

/-- **Outside distinguishability**, defined in §6's running prose rather than in a
numbered environment:

> *"a device `(Xᵢ, Yᵢ)` in that reality is **outside distinguishable** iff
> `∀xᵢ ∈ Xᵢ(U)` and all `x′₋ᵢ` in the range of `⊗_{j≠i} Xⱼ`, there is a `u ∈ U`
> such that simultaneously `Xᵢ(u) = xᵢ` and `Xⱼ(u) = x′ⱼ ∀j ≠ i`."*

The tuple `x′₋ᵢ` ranges over the **image** of the joint map of the other devices,
so it is written here as the values those devices take at some state `w`.

The paper reads this as free will: *"the way the other devices are setup does not
restrict how `C` can be setup"*, and Theorem 1 then says two devices that both have
it cannot observe each other with guaranteed accuracy.-/
@[expose] public def OutsideDistinguishable {n : ℕ} (R : DeviceReality U n)
    (i : Fin n) : Prop :=
  ∀ xᵢ : (R i).Setup, (R i).Realized xᵢ → ∀ w : U,
    ∃ u : U, (R i).setup u = xᵢ ∧ ∀ j : Fin n, j ≠ i → (R j).setup u = (R j).setup w

/-! ## Proposition 3(i) — a pairwise-distinguishable 3-cycle

Three devices on `Fin 4` whose setups are the three nontrivial linear
partitions of the square (pairwise independent, so distinguishable).
Each conclusion is a cyclic shift of those partitions: one fibre answers
the identity probe of the next device, the other answers negation.
-/

/-- One row of the 3-cycle: `(Xᵢ, Yᵢ)` for `i = 1,2,3`.-/
public structure Cycle3Row where
  x1 : Bool
  y1 : Bool
  x2 : Bool
  y2 : Bool
  x3 : Bool
  y3 : Bool

/-- Universes `0,1,2,3` as the four corners of the square.-/
public def cycle3Table : Fin 4 → Cycle3Row
  | 0 => { x1 := false, y1 := false, x2 := false, y2 := false, x3 := false, y3 := false }
  | 1 => { x1 := false, y1 := true,  x2 := true,  y2 := true,  x3 := true,  y3 := false }
  | 2 => { x1 := true,  y1 := false, x2 := false, y2 := true,  x3 := true,  y3 := true }
  | 3 => { x1 := true,  y1 := true,  x2 := true,  y2 := false, x3 := false, y3 := true }

public def cycle3device1 : InferenceDevice (Fin 4) where
  Setup := Bool
  setup := fun u => (cycle3Table u).x1
  concl := fun u => (cycle3Table u).y1
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨1, rfl⟩

public def cycle3device2 : InferenceDevice (Fin 4) where
  Setup := Bool
  setup := fun u => (cycle3Table u).x2
  concl := fun u => (cycle3Table u).y2
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨1, rfl⟩

public def cycle3device3 : InferenceDevice (Fin 4) where
  Setup := Bool
  setup := fun u => (cycle3Table u).x3
  concl := fun u => (cycle3Table u).y3
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨2, rfl⟩

public def cycle3Reality : DeviceReality (Fin 4) 3
  | ⟨0, _⟩ => cycle3device1
  | ⟨1, _⟩ => cycle3device2
  | ⟨2, _⟩ => cycle3device3

/-! ## Proposition 3(ii)–(iii) -/

/-! ## Definition 7 — mimicry and copies -/

/-- Realized `(X, Y)` pairs.-/
@[expose] public def realizedPairs (C : InferenceDevice.{u, v} U) :
    Set (C.Setup × Bool) :=
  {p | ∃ w, C.setup w = p.1 ∧ C.concl w = p.2}

/--
**Definition 7.** `C₁` mimics `C₂`.

*"Let `U` and `Û` be two (perhaps identical) sets. Let `C₁` be a device in a
reality with domain `U` … let `R₂` be the relation between `X₂` and `Y₂` for some
separate device `C₂` in the reduced form of a reality having domain `Û`. Then
`C₁` mimics `C₂` iff there is an injection `ρ_X : X₂(Û) → X₁(U)` and a bijection
`ρ_Y : Y₂(Û) ↔ Y₁(U)` such that `∀ x₂, y₂`, `x₂ R₂ y₂ ⇔ ρ_X(x₂) R₁ ρ_Y(y₂)`."*

The two universes are **kept distinct**, as the source's opening sentence
requires: a device may be a copy of a device in another reality. `ρ_Y` is
`Bool ≃ Bool` because Definition 1 forces `Y₁(U) = Y₂(Û) = 𝔹`. `ρ_X` is
deliberately **not** surjective — the source notes that this is what lets one
device mimic several others.

`realizedPairs` is the single-device reduced-form relation: `(x, y)` is in it
exactly when some universe realizes both.-/
@[expose] public def Mimics {Û : Type u'} (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u', v'} Û) : Prop :=
  ∃ (ρX : {x // C₂.Realized x} → {x // C₁.Realized x}) (ρY : Bool ≃ Bool),
    Function.Injective ρX ∧
      ∀ (x₂ : {x // C₂.Realized x}) (y₂ : Bool),
        ((x₂.1, y₂) ∈ realizedPairs C₂) ↔
          ((ρX x₂).1, ρY y₂) ∈ realizedPairs C₁

/-- **Definition 7.** Copies: mimicry in both directions.-/
@[expose] public def Copies {Û : Type u'} (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u', v'} Û) : Prop :=
  Mimics C₁ C₂ ∧ Mimics C₂ C₁

/-! ## Lemma 1 — reduced forms of realities are exactly the admissible families

The source defines the **reduced form** of a reality `(U; {F_φ})` as the range of
`⊗_φ F_φ`: for a device reality with extra functions, the set of tuples
`([x₁,y₁],[x₂,y₂],…; γ₁,γ₂,…)` for which some `u ∈ U` realizes all coordinates at
once.

**Lemma 1** says that set of reduced forms, `K₁`, equals `K₂`: the families of
tuples whose conclusion coordinates cover `𝔹` and whose setup and function
coordinates each take at least two values.

The `≥ 2` and `= 𝔹` conditions are the source's global stipulations. This
development drops them globally, so here they appear as `SourceStipulations` on
the reality side and as the explicit clauses of `AdmissibleTuples` on the other.
-/

/-- The device with a prescribed setup and conclusion. Lemma 1's realisation
step: the index set of the tuples *is* `U`.-/
@[expose] public def deviceOf {R S : Type*} (s : R → S) (t : R → Bool)
    (hY : Function.Surjective t) : InferenceDevice R where
  Setup := S
  setup := s
  concl := t
  concl_surjective := hY

/-- A tuple of a device reality: a `(setup, conclusion)` pair per device index,
and a value per extra-function index.-/
@[expose] public def RealityTuple {A B : Type*} (S : A → Type*) (V : B → Type*) :
    Type _ :=
  ((α : A) → S α × Bool) × ((β : B) → V β)

/-- A reality `(U; {C_α}; {Γ_β})`: a family of devices and a family of arbitrary
functions over one universe.-/
public structure FullReality (U : Type u) {A B : Type*}
    (S : A → Type*) (V : B → Type*) where
  /-- The setup function of device `α`.-/
  setupOf : (α : A) → U → S α
  /-- The conclusion function of device `α`.-/
  conclOf : A → U → Bool
  /-- The extra function `Γ_β`.-/
  funcOf : (β : B) → U → V β

/-- The source's standing stipulations, dropped globally in this development and
therefore stated here: every conclusion is onto `𝔹`, and every setup function and
every extra function takes at least two values.-/
public structure FullReality.SourceStipulations {U : Type u} {A B : Type*}
    {S : A → Type*} {V : B → Type*} (R : FullReality U S V) : Prop where
  /-- The source defines a reality from a nonempty family of functions.-/
  family_nonempty : Nonempty (Sum A B)
  /-- `Y_α` is onto `𝔹`.-/
  concl_surj : ∀ α, Function.Surjective (R.conclOf α)
  /-- `|X_α(U)| ≥ 2`.-/
  setup_two : ∀ α, ∃ u u', R.setupOf α u ≠ R.setupOf α u'
  /-- `|Γ_β(U)| ≥ 2`.-/
  func_two : ∀ β, ∃ u u', R.funcOf β u ≠ R.funcOf β u'

/-- **Reduced form**: the range of the tupling map `⊗_φ F_φ`.-/
@[expose] public def FullReality.reducedForm {U : Type u} {A B : Type*}
    {S : A → Type*} {V : B → Type*} (R : FullReality U S V) :
    Set (RealityTuple S V) :=
  Set.range (fun u : U =>
    ((fun α => (R.setupOf α u, R.conclOf α u)), fun β => R.funcOf β u))

/-- **`K₂`**: the tuple families the source calls admissible.-/
@[expose] public def AdmissibleTuples {A B : Type*} {S : A → Type*} {V : B → Type*}
    (k : Set (RealityTuple S V)) : Prop :=
  Nonempty (Sum A B) ∧
    (∀ (α : A) (b : Bool), ∃ t ∈ k, (t.1 α).2 = b) ∧
    (∀ α : A, ∃ t ∈ k, ∃ t' ∈ k, (t.1 α).1 ≠ (t'.1 α).1) ∧
      (∀ β : B, ∃ t ∈ k, ∃ t' ∈ k, t.2 β ≠ t'.2 β)

/-- **`K₁`**: the reduced forms of realities satisfying the source's stipulations.
The universe is the family itself, which is the source's own construction — *"the
index set of the tuples is `U`"*.-/
@[expose] public def IsReducedForm {A B : Type*} {S : A → Type*} {V : B → Type*}
    (k : Set (RealityTuple S V)) : Prop :=
  ∃ R : FullReality {t : RealityTuple S V // t ∈ k} S V,
    R.SourceStipulations ∧ R.reducedForm = k

/-! ## Proposition 5(ii) — infinite copies with strong inference

`C₁` has identity setup and parity conclusion. `C₂` has setup `n/2` and
the same parity-of-setup conclusion. Each `C₂`-fibre `{2k, 2k+1}` holds both
`Y₁` values, so `C₁` strongly infers `C₂`. Both devices realise the pairs
`(k, k even)`, so they are copies.
-/

@[expose] public def infiniteCopy1 : InferenceDevice ℕ where
  Setup := ℕ
  setup := id
  concl := fun n => decide (n % 2 = 0)
  concl_surjective := fun
    | true => ⟨0, rfl⟩
    | false => ⟨1, rfl⟩

@[expose] public def infiniteCopy2 : InferenceDevice ℕ where
  Setup := ℕ
  setup := fun n => n / 2
  concl := fun n => decide ((n / 2) % 2 = 0)
  concl_surjective := fun
    | true => ⟨0, rfl⟩
    | false => ⟨2, rfl⟩

/-- `Setup` of each infinite copy is definitionally `ℕ`. Instance search
does not unfold the structure field; these wrappers do.-/
@[expose] public def asNat1 (x : infiniteCopy1.Setup) : ℕ := x
@[expose] public def asNat2 (x : infiniteCopy2.Setup) : ℕ := x

/-- **Proposition 4, uniqueness core.** Two distinguishable devices cannot
both strongly infer a third at two different setup values.-/
public theorem not_two_strong_inferrers_conflict
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    {C₃ : InferenceDevice.{u, v''} U}
    (h13 : StronglyInfers C₁ C₃) (h23 : StronglyInfers C₂ C₃)
    (hdist : Distinguishable C₁ C₂)
    {x a : C₃.Setup} (hxa : x ≠ a)
    (hx : C₃.Realized x) (ha : C₃.Realized a) : False := by
  obtain ⟨wt, hwt⟩ := C₃.concl_surjective true
  obtain ⟨x₁, hx₁, h₁⟩ := h13 true id isProbe_id ⟨wt, hwt⟩ x hx
  obtain ⟨x₂, hx₂, h₂⟩ := h23 true id isProbe_id ⟨wt, hwt⟩ a ha
  obtain ⟨w, hw₁, hw₂⟩ := hdist x₁ hx₁ x₂ hx₂
  exact hxa ((h₁ w hw₁).1.symm.trans (h₂ w hw₂).1)

/-! ## Proposition 5(i) — the paper's five quadruples

`{(−1,−1,−1,−1); (−1,−1,1,−1); (1,−1,−1,1); (1,1,1,−1); (−1,1,1,1)}`
with `−1 ↦ false`, `1 ↦ true`. Both devices realise every `Bool × Bool`
pair, so the identity on setup labels is a copy map. `X₁ = true` answers
negation of `Y₂`; `X₁ = false` answers the identity.
-/

public structure FiniteCopyRow where
  x1 : Bool
  y1 : Bool
  x2 : Bool
  y2 : Bool

@[expose] public def finiteCopyTable : Fin 5 → FiniteCopyRow
  | 0 => { x1 := false, y1 := false, x2 := false, y2 := false }
  | 1 => { x1 := false, y1 := false, x2 := true,  y2 := false }
  | 2 => { x1 := true,  y1 := false, x2 := false, y2 := true }
  | 3 => { x1 := true,  y1 := true,  x2 := true,  y2 := false }
  | 4 => { x1 := false, y1 := true,  x2 := true,  y2 := true }

@[expose] public def finiteCopy1 : InferenceDevice (Fin 5) where
  Setup := Bool
  setup := fun u => (finiteCopyTable u).x1
  concl := fun u => (finiteCopyTable u).y1
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨3, rfl⟩

@[expose] public def finiteCopy2 : InferenceDevice (Fin 5) where
  Setup := Bool
  setup := fun u => (finiteCopyTable u).x2
  concl := fun u => (finiteCopyTable u).y2
  concl_surjective := fun
    | false => ⟨0, rfl⟩
    | true => ⟨2, rfl⟩

/-! ## Proposition 5(ii) necessity — two injective fibre maps

`C₁ ≫ C₂` supplies, for each realised `x₂`, a setup answering the identity
probe on that fibre and one answering negation. Those maps are injective
and pointwise distinct, so `|X₁(U)| ≥ 2|X₂(U)|`. Copies force equal
cardinality. Hence both images are infinite.
-/

/-- Identity-probe setup of `C₁` on the fibre of `x₂`.-/
public noncomputable def identityFibreSetup
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) (x₂ : {x // C₂.Realized x}) :
    {x // C₁.Realized x} :=
  ⟨(hs true id isProbe_id (C₂.concl_surjective true) x₂.1 x₂.2).choose,
    (hs true id isProbe_id (C₂.concl_surjective true) x₂.1 x₂.2).choose_spec.1⟩

/-- Negation-probe setup of `C₁` on the fibre of `x₂`.-/
public noncomputable def negationFibreSetup
    {C₁ : InferenceDevice.{u, v} U} {C₂ : InferenceDevice.{u, v'} U}
    (hs : StronglyInfers C₁ C₂) (x₂ : {x // C₂.Realized x}) :
    {x // C₁.Realized x} :=
  ⟨(hs false (fun b => !b) isProbe_not (C₂.concl_surjective false)
      x₂.1 x₂.2).choose,
    (hs false (fun b => !b) isProbe_not (C₂.concl_surjective false)
      x₂.1 x₂.2).choose_spec.1⟩

/-- **Proposition 4.** Unique root of a finite weakly-connected
strong-inference graph whose incomparable pairs are distinguishable.
The combinatorial core is `not_two_strong_inferrers_conflict`; existence
of a root is maximality of the successor-count (paper: finite + acyclic).-/
@[expose] public def StrongEdge {n : ℕ} (R : DeviceReality U n) (i j : Fin n) : Prop :=
  StronglyInfers (R i) (R j) ∨ StronglyInfers (R j) (R i)

@[expose] public def StrongGraphWeaklyConnected {n : ℕ} (R : DeviceReality U n) : Prop :=
  ∀ i j : Fin n, Relation.ReflTransGen (StrongEdge R) i j

@[expose] public def IsStrongRoot {n : ℕ} (R : DeviceReality U n) (r : Fin n) : Prop :=
  ∀ i : Fin n, StronglyInfers (R i) (R r) → i = r

/-! ## Universal devices — the source's "monotheism theorem"

Both papers define this in prose and immediately draw a consequence from it.
2008, after Definition 7: *"Define a universal device as any device in a reality
that can strongly infer all other devices and weakly infer all functions in that
reality. Theorem 3 means that no reality can contain more than one universal
device."* 2018 repeats it word for word, citing its Proposition 6 — which is
2008's Theorem 3. The paper names the pair of results the **monotheism theorem**.

Neither the definition nor the uniqueness claim was tracked until an adversarial
review of the coverage tables went looking for prose that states a claim.

**Stronger than printed.** The printed definition has two clauses — strongly
infers every other device, *and* weakly infers every function of the reality —
and uniqueness needs only the first. `IsUniversal` therefore carries only the
device clause, so `universal_unique` rules out more devices than the source's
argument does. `DeviceReality` has no `{Γ_β}` component to state the second
clause against; the source's functions live in `FullReality`.
-/

/-- **A universal device**, on the clause uniqueness actually uses: it strongly
infers every other device of the reality.-/
@[expose] public def IsUniversal {n : ℕ} (R : DeviceReality U n) (i : Fin n) : Prop :=
  ∀ j : Fin n, j ≠ i → StronglyInfers (R i) (R j)

/-! ### The printed two-clause universal device

`IsUniversal` above carries only the clause uniqueness needs. The printed
definition has two:

> *"Define a universal device as any device in a reality that can **strongly
> infer all other devices** and **weakly infer all functions** in that reality."*

`DeviceReality` has no function family to state the second clause against, so it
is stated here over `FullReality`, which carries the source's `{Γ_β}`.

Uniqueness is **inherited rather than reproved**: it never used the second
clause, so the same argument applies verbatim and the two-clause version is a
weaker hypothesis with the same conclusion.
-/

variable {A B : Type*} {S : A → Type v} {V : B → Type*}

/-- The device at index `α` of a full reality, given the source's surjectivity
stipulation.-/
@[expose] public def FullReality.device (R : FullReality U S V)
    (hsurj : ∀ α, Function.Surjective (R.conclOf α)) (α : A) :
    InferenceDevice.{u, v} U :=
  deviceOf (R.setupOf α) (R.conclOf α) (hsurj α)

/--
**The printed definition of a universal device**, both clauses.

`IsUniversal` is this with the second clause dropped; that is why the uniqueness
theorem there is *stronger* than the source's, and why this one is the faithful
transcription rather than the useful one.-/
@[expose] public def FullReality.IsUniversalFull (R : FullReality U S V)
    (hsurj : ∀ α, Function.Surjective (R.conclOf α)) (α : A) : Prop :=
  (∀ α' : A, α' ≠ α → StronglyInfers (R.device hsurj α) (R.device hsurj α')) ∧
    (∀ β : B, WeaklyInfers (R.device hsurj α) (R.funcOf β))

/-! ### The `|U| > 3` sentence — repaired, not bridged from Proposition 7(2)

2018, after Definition 10: *"Prop. 7(ii) means that no reality with `|U| > 3`
can have a universal device if the reality contains all functions defined over
`U`."*

Proposition 7(2) is an existential over **pairs**. Universality's first clause
quantifies over **devices**. An existential over pairs cannot discharge a
universal over devices, whatever witness is chosen. The source's own witness
`S = T = id` is a device pair only at `U = Bool`, which `|U| > 3` excludes.
Clash 28.

The conclusion is nevertheless true, and needs no cardinality: a universal
device must weakly infer every function in the reality, including — once the
family contains it — its own conclusion, which Proposition 1(ii) forbids. The
function family is specialized to `U → Bool` so the membership is an equality
of maps, not a `HEq`.
-/

/-- The extra-function family contains every two-valued Boolean map — the
source's own stipulation, not the type-theoretic "all functions", which would
include constants that `func_two` rejects.-/
@[expose] public def FullReality.ContainsEveryTwoValuedBool
    {B : Type*} (R : FullReality U S (fun _ : B => Bool)) : Prop :=
  ∀ Γ : U → Bool, Function.Surjective Γ → ∃ β : B, R.funcOf β = Γ

end AISafetyAtlas.Inference
