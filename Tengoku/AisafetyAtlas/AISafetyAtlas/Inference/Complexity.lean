module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Device
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.FiniteRange
public import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
public import Tengoku.Seed.Data.Fintype.Card
public import Tengoku.Seed.Data.Real.Basic
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
public import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
public import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Inference complexity — Wolpert 2008 §5

The paper's analogue of Kolmogorov complexity: the length of a setup value
is `ℒ(x) = −ln |X⁻¹(x)|`, and the inference complexity of `Γ` is the sum,
over probes of `Γ`, of the shortest answering fibre (Definition 6). Theorem 4
is the encoding bound: if `C₁ ≫ C₂` and `C₂ > Γ`, the complexity difference
is at most `|Γ(U)|` times the worst-case emulation cost.

Stated under counting measure on a finite `U` (the source's Example 6). The
source allows a general measure `dμ`; the counting case is the one in which
`ℒ` is a fibre cardinality, so the bound is a statement about those
cardinalities rather than an uninterpreted integral.

The per-probe inequality is `minAnsweringLength_le_emulation` (pick the
shortest `C₂` fibre that answers the probe, then a `C₁` fibre that emulates
it); the displayed theorem sums that inequality.
-/

namespace AISafetyAtlas.Inference

open scoped Classical

variable {U : Type u}

/-- Counting volume of a setup fibre.-/
@[expose] public noncomputable def setupFibreCard [Fintype U] (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] (x : C.Setup) : ℕ :=
  (Finset.univ.filter (fun u : U => C.setup u = x)).card

/-- **Section 5 length.** `ℒ(x) = -ln |X⁻¹(x)|`.-/
@[expose] public noncomputable def setupLength [Fintype U] (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] (x : C.Setup) : ℝ :=
  -Real.log (setupFibreCard C x : ℝ)

/-- Realized setup values, as a finite set. Finiteness sits on the setup map,
which is Definition 6's own hypothesis (*"`X(U)` … countable"*), not on `U`.-/
@[expose] public noncomputable def realizedSetups (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] : Finset C.Setup :=
  rangeFinset C.setup

/-- The setup answers probe `f` of `Γ`.-/
@[expose] public def AnswersProbe (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (f : G → Bool) (x : C.Setup) : Prop :=
  C.Realized x ∧ ∀ w, C.setup w = x → C.concl w = f (Γ w)

@[expose] public noncomputable def answeringSet (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) :
    Finset C.Setup :=
  (realizedSetups C).filter (fun x => ∀ w, C.setup w = x → C.concl w = f (Γ w))

/-- Membership in the answering set, stated so callers never have to match the
`Finset.filter` decidability instance this module's `open scoped Classical` picks.

Without it a finite model elaborates `Nat.decidableForallFin` where the definition
carries `Classical.propDecidable`, and `Finset.mem_filter` fails to apply.-/
public theorem mem_answeringSet_iff (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) (x : C.Setup) :
    x ∈ answeringSet C Γ f ↔
      C.Realized x ∧ ∀ w, C.setup w = x → C.concl w = f (Γ w) := by
  unfold answeringSet realizedSetups
  rw [Finset.mem_filter, mem_rangeFinset]
  exact Iff.rfl

/-- **Definition 6's minima are over nonempty sets.** Under the definition's own
hypothesis `C > Γ`, every probe of a realized target value is answered by some
realized setup, so `minAnsweringLength` below never falls through to its
totalizing `0`.-/
public theorem answeringSet_nonempty_of_weaklyInfers (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] {Γ : U → G} (hw : WeaklyInfers C Γ)
    (γ : G) (hγ : ∃ w, Γ w = γ) :
    (answeringSet C Γ (probe γ)).Nonempty := by
  obtain ⟨x, hx, hfib⟩ := hw γ (probe γ) (isProbe_probe γ) hγ
  exact ⟨x, (mem_answeringSet_iff C Γ (probe γ) x).mpr ⟨hx, hfib⟩⟩

/-- The source's `min_{x : X=x ⇒ Y=f(Γ)} ℒ(x)`, for an arbitrary length
assignment `ℓ`.

`ℒ` is a **parameter**, not `setupLength`. Section 5 never uses any property of
it: every step of Theorem 4 below compares lengths through `inf'` and `sup'` and
never unfolds one. So the theorem holds for the counting length the source's
Example 6 uses, for `−log` of any measure's fibre mass, and for anything else.-/
@[expose] public noncomputable def minAnsweringLength (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  if h : (answeringSet C Γ f).Nonempty then
    (answeringSet C Γ f).inf' h ℓ
  else 0

/--
The Definition 6 sum, defined for every `C` and `Γ`.

Where no setup answers a probe, `minAnsweringLength` contributes `0`. The source
never evaluates that case: Definition 6 is stated only for `C > Γ`, so every
`min` there is over a nonempty set. Total failure would otherwise look *cheaper*
than success, since `ℒ` is `-log` of a fibre size and so is at most `0`. Use
`inferenceComplexity`, which carries the hypothesis, unless the totalization is
what you want.-/
@[expose] public noncomputable def inferenceComplexityTotal (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum (fun γ => minAnsweringLength C ℓ Γ (probe γ))

/--
**Definition 6.** *"Let `C` be a device and `Γ` a function over `U` where `X(U)`
and `Γ(U)` are countable **and `C > Γ`**."*

The hypothesis is the source's and is carried in the signature, so the object is
never formed outside the regime the paper defines it on. It is proof-irrelevant:
`inferenceComplexity_eq_total` discharges it.-/
@[expose] public noncomputable def inferenceComplexity
    (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (_hW : WeaklyInfers C Γ) : ℝ :=
  inferenceComplexityTotal C ℓ Γ

public theorem inferenceComplexity_eq_total (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup] (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hW : WeaklyInfers C Γ) :
    inferenceComplexity C ℓ Γ hW = inferenceComplexityTotal C ℓ Γ := rfl

@[expose] public def EmulatesAt (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) (x₁ : C₁.Setup) (x₂ : C₂.Setup) : Prop :=
  C₁.Realized x₁ ∧ C₂.Realized x₂ ∧
    ∀ w, C₁.setup w = x₁ → C₂.setup w = x₂ ∧ C₁.concl w = C₂.concl w

@[expose] public noncomputable def emulationSet (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] [FiniteRange C₁.setup]
    (x₂ : C₂.Setup) : Finset C₁.Setup :=
  (realizedSetups C₁).filter (fun x₁ =>
    ∀ w, C₁.setup w = x₁ → C₂.setup w = x₂ ∧ C₁.concl w = C₂.concl w)

@[expose] public noncomputable def emulationCostAt (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] [FiniteRange C₁.setup]
    (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ) (x₂ : C₂.Setup) : ℝ :=
  if h : (emulationSet C₁ C₂ x₂).Nonempty then
    (emulationSet C₁ C₂ x₂).inf' h (fun x₁ => ℓ₁ x₁ - ℓ₂ x₂)
  else 0

@[expose] public noncomputable def emulationCost (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ) : ℝ :=
  if h : (realizedSetups C₂).Nonempty then
    (realizedSetups C₂).sup' h (emulationCostAt C₁ C₂ ℓ₁ ℓ₂)
  else 0

/-! ## Definition 6 over an arbitrary setup range

2008 Definition 6 and 2018 Definition 7 both admit **countable** `X(U)`, and
`answeringSet` is a `Finset`, so every complexity object above carries
`[FiniteRange C.setup]`. 2018 Proposition 13's own scope delta names exactly
that restriction.

Under the acceptance rule the question is what the printed `min_x` needs in
order to denote. It needs the minimum to **exist** — a set of reals bounded
below and nonempty — not the index to be finite. So the restriction below is an
`IsLeast` hypothesis, which `[FiniteRange C.setup]` supplies and which a
countable range can also supply.

**What is *not* widened here, and why.** Theorem 4 multiplies by `|Γ(U)|`. On a
countably infinite target range that factor is not a real number, so the printed
inequality does not denote and finiteness of `Γ(U)` is forced rather than
chosen. The target side stays a `Finset`; only the setup side moves.
-/

/-- The answering setups as a **set**: the printed condition with no finiteness
on `X(U)`.-/
@[expose] public def answeringSetOn (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (f : G → Bool) : Set C.Setup :=
  {x | C.Realized x ∧ ∀ w, C.setup w = x → C.concl w = f (Γ w)}

/-- The printed `min_x` as an infimum over that set. It denotes for any setup
range; `IsLeast` below is what makes it the printed *minimum*.-/
@[expose] public noncomputable def minAnsweringLengthOn (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  sInf (ℓ '' answeringSetOn C Γ f)

/-- **Definition 6 with no finiteness on the setup range.** The sum is still
over `Γ(U)`, which the print keeps finite wherever it multiplies by `|Γ(U)|`.-/
@[expose] public noncomputable def inferenceComplexityOn (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum (fun γ => minAnsweringLengthOn C ℓ Γ (probe γ))

/-! ## Theorem 4 over an arbitrary setup range

The definition layer above needs no finiteness on `X(U)`. Theorem 4 still
consumed the `Finset` forms, because `emulationCost` is a `Finset.sup'` of
`Finset.inf'`s. The set forms below remove that, and the theorem is restated
over them.

The hypotheses are the printed `min` and `max` **existing**, which is what the
printed formula needs in order to denote and what a finite range supplies. They
are stated as `IsLeast`/`IsGreatest` rather than as boundedness, because
`min_{x₁}` and `max_{x₂}` assert attainment, not merely an infimum.
-/

/-- The emulating setups as a **set**.-/
@[expose] public def emulationSetOn (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) (x₂ : C₂.Setup) : Set C₁.Setup :=
  {x₁ | C₁.Realized x₁ ∧
    ∀ w, C₁.setup w = x₁ → C₂.setup w = x₂ ∧ C₁.concl w = C₂.concl w}

/-- The printed `min_{x₁}` of the emulation gap, as an infimum.-/
@[expose] public noncomputable def emulationCostAtOn (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ)
    (x₂ : C₂.Setup) : ℝ :=
  sInf ((fun x₁ => ℓ₁ x₁ - ℓ₂ x₂) '' emulationSetOn C₁ C₂ x₂)

/-- The printed `max_{x₂}`, as a supremum over the realized setups of `C₂`.-/
@[expose] public noncomputable def emulationCostOn (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U) (ℓ₁ : C₁.Setup → ℝ) (ℓ₂ : C₂.Setup → ℝ) : ℝ :=
  sSup (emulationCostAtOn C₁ C₂ ℓ₁ ℓ₂ '' {x₂ | C₂.Realized x₂})

/-! ## Definition 6 over a countable target range

The printed display is `∑_{f ∈ π(Γ)} min_x [ℒ(x)]` under the hypothesis that
`X(U)` **and** `Γ(U)` are countable. The setup side is handled above by
`answeringSetOn`. This section handles the target side.

Checked against the LaTeX source: Definition 6 carries **no `|Γ(U)|` factor** —
that belongs to Theorem 4, a different statement, which prints `Γ(U)` finite of
its own accord. So target-range finiteness here would be an atlas restriction,
not a forced one.

`∑'` totalizes to `0` when the family is not summable, so the printed sum is
this object exactly where the print denotes: on a summable family. Summability
is the hypothesis, not a property of the definition, which is why it appears on
the theorems below rather than in the definition.
-/

/-- One term of the countable complexity sum. Unrealized target values
contribute nothing — the guard is needed, because on an unrealized `γ` the probe
is constantly `false` and the answering set can still be inhabited.-/
@[expose] public noncomputable def complexityTerm (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) (γ : G) : ℝ :=
  if ∃ u, Γ u = γ then minAnsweringLengthOn C ℓ Γ (probe γ) else 0

/-- **Definition 6 with no finiteness on either range.** The sum is a `tsum`
over the whole target type; the realized values are the printed `π(Γ)`.-/
@[expose] public noncomputable def inferenceComplexitySum (C : InferenceDevice.{u, v} U)
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) : ℝ :=
  ∑' γ : G, complexityTerm C ℓ Γ γ

/-! ## Theorem 4 from strong inference, at set scope

`inferenceComplexityOn_le_of_perProbe` assumes the per-probe inequality. That
is not Theorem 4: the printed theorem derives it from `C₁ ≫ C₂` and `C₂ > Γ`,
so no scope claim may rest on the assumed-hypothesis form.

The derivation is below. What it needs beyond the printed hypotheses is
attainment of the printed `min` and `max`, and that is what the print asserts
by writing them: `min_{x₁ : X₁ = x₁ ⇒ …}` and `max_{x₂}` denote only when
attained. A finite setup range supplies attainment; so does a countable one
with the infimum reached. That is the acceptance rule, not a weakening.
-/

end AISafetyAtlas.Inference
