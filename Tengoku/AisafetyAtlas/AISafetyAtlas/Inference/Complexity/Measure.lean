module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Complexity
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Stochastic.Measure
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Stochastic
public import Tengoku.Seed.InformationTheory.KullbackLeibler.Basic
public import Tengoku.Seed.MeasureTheory.Measure.Count

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Section 5's length under a general measure

Definition 6's length is `ℒ(x) = −ln μ(X⁻¹(x))` for a measure `dμ` the source
leaves general; its Example 6 takes counting measure, which is the case
`Complexity.lean` names `setupLength`.

Nothing else in section 5 has to change. Theorem 4 is stated there for an
arbitrary length assignment, because its proof compares lengths through `inf'`
and `sup'` and never unfolds one. So the general-measure case is an
instantiation, not a second development.
-/

namespace AISafetyAtlas.Inference

open MeasureTheory

open scoped Classical

universe u v v' v''

variable {U : Type u} [MeasurableSpace U]

/-- **Definition 6's length**, `ℒ(x) = −ln μ(X⁻¹(x))`, for a general measure.-/
@[expose] public noncomputable def measureLength (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (x : C.Setup) : ℝ :=
  -Real.log (massOn μ C.setup x)

/-- **Definition 6 under a general measure.**-/
@[expose] public noncomputable def inferenceComplexityMeasure (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hW : WeaklyInfers C Γ) : ℝ :=
  inferenceComplexity C (measureLength μ C) Γ hW

/-! ## Stochastic inference complexity

Section 8 defines, in running prose rather than a numbered environment:

> `C̄_ε(Γ ∣ C) ≜ Σ_{f ∈ π(Γ)} min_{x : E_P(Y f(Γ)∣x) ≥ ε} [−H(U ∣ x)]`

It is Definition 6 with the *exact*-answering condition on a setup relaxed to
*accurate to within `ε`*, and with the same length — the source notes that when
`P ∝ dμ` on the support, `−H(U ∣ x)` and `−ln μ(X⁻¹(x))` agree. So it is another
instantiation of the section 5 machinery, differing only in which setups the
minimum ranges over.

This was the largest gap in the prose layer of section 8. -/

/-- The setups whose Definition 9 accuracy at this probe is at least `ε`.-/
@[expose] public noncomputable def accurateSet (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) (ε : ℝ) : Finset C.Setup :=
  (realizedSetups C).filter fun x =>
    ε ≤ condExpectPmOn μ C.setup x (fun u => C.concl u == f (Γ u))

@[expose] public noncomputable def minAccurateLength (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    (ℓ : C.Setup → ℝ) {G : Type v'} (Γ : U → G) (f : G → Bool) (ε : ℝ) : ℝ :=
  if h : (accurateSet μ C Γ f ε).Nonempty then
    (accurateSet μ C Γ f ε).inf' h ℓ
  else 0

/-- **Stochastic inference complexity**, `C̄_ε(Γ ∣ C)`.-/
@[expose] public noncomputable def stochasticInferenceComplexity (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    (ℓ : C.Setup → ℝ) {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (ε : ℝ) : ℝ :=
  (rangeFinset Γ).sum fun γ => minAccurateLength μ C ℓ Γ (probe γ) ε

/-- Membership in the accuracy set, stated so callers never have to match the
`Finset.filter` decidability instance this module's `open scoped Classical` picks
— the same hazard `mem_answeringSet_iff` exists for.-/
public theorem mem_accurateSet_iff (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) (ε : ℝ) (x : C.Setup) :
    x ∈ accurateSet μ C Γ f ε ↔
      C.Realized x ∧ ε ≤ condExpectPmOn μ C.setup x (fun u => C.concl u == f (Γ u)) := by
  unfold accurateSet realizedSetups
  rw [Finset.mem_filter, mem_rangeFinset]
  exact Iff.rfl

/-- A setup that answers a probe exactly, on a fibre of positive mass, is accurate
to within `1`. This is the inclusion behind the source's remark that at `ε = 1` the
stochastic complexity collapses to Definition 6.-/
public theorem mem_accurateSet_of_answersProbe (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) {x : C.Setup}
    (hx : massOn μ C.setup x ≠ 0) (hmem : x ∈ answeringSet C Γ f) :
    x ∈ accurateSet μ C Γ f 1 := by
  have hfib : ∀ w, C.setup w = x → C.concl w = f (Γ w) := (Finset.mem_filter.mp hmem).2
  have hset : (fun u => (C.setup u, C.concl u == f (Γ u))) ⁻¹' {(x, true)}
      = C.setup ⁻¹' {x} := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    refine ⟨fun h => h.1, fun h => ⟨h, ?_⟩⟩
    rw [hfib u h]
    simp
  refine Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hmem).1, ?_⟩
  unfold condExpectPmOn condAgreeOn
  rw [ite_eq_right hx, show massOn μ (fun u => (C.setup u, C.concl u == f (Γ u))) (x, true)
      = massOn μ C.setup x by simp [massOn, hset]]
  rw [div_self hx]
  norm_num

/-! ### The converse inclusion, and where the source's second hypothesis goes

Accuracy `1` says the disagreeing part of a fibre has **measure zero**. Exact
answering says it is **empty**. Those differ by exactly the null sets, which is
what the source's *"`P` is proportional to `dμ` across the support of `P`"* is
doing: it forbids a point that the accuracy measure ignores but the length
measure still counts.

The atlas model uses one measure for both, so the condition becomes the
statement that no point is null — `hatom` below. It is stated on the fibre
rather than globally, because that is all the argument uses, and it is a genuine
hypothesis rather than a technicality: without it a device can be accurate to
within `1` at a probe it answers wrongly at a null point, and the two complexities
come apart. -/

/-- **Accuracy `1` forces exact answering when no point of the fibre is null.**-/
public theorem answersProbe_of_mem_accurateSet (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup]
    (hC : Measurable C.setup)
    {G : Type v'} (Γ : U → G) (f : G → Bool)
    (hagree : Measurable fun u => C.concl u == f (Γ u))
    (hatom : ∀ u : U, μ {u} ≠ 0)
    {x : C.Setup} (hx : x ∈ accurateSet μ C Γ f 1) :
    x ∈ answeringSet C Γ f := by
  classical
  obtain ⟨hxR, hacc⟩ := (mem_accurateSet_iff μ C Γ f 1 x).mp hx
  set h : U → Bool := fun u => C.concl u == f (Γ u) with hdef
  have hmass : massOn μ C.setup x ≠ 0 := by
    intro h0
    rw [condExpectPmOn, condAgreeOn, ite_eq_left h0] at hacc
    norm_num at hacc
  have hMpos : 0 < massOn μ C.setup x :=
    lt_of_le_of_ne (massOn_nonneg _ _ _) (Ne.symm hmass)
  have hsplit := massOn_bool_split μ C.setup h hC hagree x
  have hBnonneg := massOn_nonneg μ (fun u => (C.setup u, h u)) (x, false)
  have hB : massOn μ (fun u => (C.setup u, h u)) (x, false) = 0 := by
    rw [condExpectPmOn, condAgreeOn, ite_eq_right hmass] at hacc
    have hone : (1 : ℝ) ≤ massOn μ (fun u => (C.setup u, h u)) (x, true) /
        massOn μ C.setup x := by linarith
    have hle := (one_le_div hMpos).mp hone
    linarith
  refine (mem_answeringSet_iff C Γ f x).mpr ⟨hxR, fun w hw => ?_⟩
  by_contra hne
  have hfw : h w = false := by simp [hdef, hne]
  have hsub : ({w} : Set U) ⊆ (fun u => (C.setup u, h u)) ⁻¹' {(x, false)} := by
    intro v hv
    rw [Set.mem_singleton_iff] at hv
    subst hv
    simp [Set.mem_preimage, hw, hfw]
  have hzero : μ ((fun u => (C.setup u, h u)) ⁻¹' {(x, false)}) = 0 :=
    ((ENNReal.toReal_eq_zero_iff _).mp hB).resolve_right (measure_ne_top μ _)
  exact hatom w (le_antisymm (hzero ▸ measure_mono hsub) (zero_le))

/-- At `ε = 1` the two sets a minimum can range over are the same set.-/
public theorem accurateSet_eq_answeringSet (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup]
    (hC : Measurable C.setup)
    {G : Type v'} (Γ : U → G) (f : G → Bool)
    (hagree : Measurable fun u => C.concl u == f (Γ u))
    (hatom : ∀ u : U, μ {u} ≠ 0)
    (hpos : ∀ x : C.Setup, x ∈ realizedSetups C → massOn μ C.setup x ≠ 0) :
    accurateSet μ C Γ f 1 = answeringSet C Γ f :=
  Finset.Subset.antisymm
    (fun _ hy => answersProbe_of_mem_accurateSet μ C hC Γ f hagree hatom hy)
    (fun y hy =>
      mem_accurateSet_of_answersProbe μ C Γ f (hpos y (Finset.mem_filter.mp hy).1) hy)

/-- **The source's `ε = 1` remark, in full.** *"if `P` is proportional to `dμ`
across the support of `P` and `C > Γ`, then for `ε = 1`, `C̄_ε(Γ ∣ C) =
𝒞(Γ ∣ C)`."*

`C > Γ` is not needed for this direction — with the two sets equal, the
totalizations agree too, so the equality holds wherever the sets do. It stays in
`inferenceComplexity`'s signature, where the source put it.-/
public theorem stochasticInferenceComplexity_eq (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    [MeasurableSpace C.Setup] [MeasurableSingletonClass C.Setup]
    (hC : Measurable C.setup) (ℓ : C.Setup → ℝ)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ]
    (hagree : ∀ f : G → Bool, Measurable fun u => C.concl u == f (Γ u))
    (hatom : ∀ u : U, μ {u} ≠ 0)
    (hpos : ∀ x : C.Setup, x ∈ realizedSetups C → massOn μ C.setup x ≠ 0) :
    stochasticInferenceComplexity μ C ℓ Γ 1 = inferenceComplexityTotal C ℓ Γ := by
  unfold stochasticInferenceComplexity inferenceComplexityTotal
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  unfold minAccurateLength minAnsweringLength
  rw [accurateSet_eq_answeringSet μ C hC Γ (probe γ) (hagree _) hatom hpos]

/-! ## `Ĉ` — the min-free variant, which **both** papers display

2008 after Definition 6: *"A natural modification to Definition 6 is to remove
the min by considering all `x`'s that cause `Y = f(Γ)`, not just of one of
them."* 2018 repeats it verbatim after Definition 7, as `Ĉ(Γ; D)`.

Both papers then display the same equality, with the same one-line justification
(*"the equality follows from the fact that for any `x`, `x' ≠ x`,
`X⁻¹(x) ∩ X⁻¹(x') = ∅`"*):

`Ĉ(Γ ∣ C) ≜ Σ_f −ln μ(⋃_{x : X=x ⇒ Y=f(Γ)} X⁻¹(x)) = Σ_f −ln (Σ_{x : …} e^{−ℒ(x)})`

It is a *displayed* definition that no numbered environment announces — the class
of item a transcription table keyed on numbered environments cannot see, which is
why both ledgers enumerate displayed equations and prose claims as well.

Unlike Definition 6, `Ĉ` needs no `min` to be attained, so nothing here forces
the setup range to be finite for the display to denote — `FiniteRange` is carried
only because `answeringSet` is a `Finset`. The disjointness the source waves at
is where the measurability comes in: a `Measure` is merely sub-additive on
arbitrary sets, so the printed equality is exactly as strong as the fibres being
measurable.
-/

/-- The mass of the union of **every** fibre answering a probe — the argument of
the logarithm in `Ĉ`.-/
@[expose] public noncomputable def answeringMass (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  (μ (⋃ x ∈ answeringSet C Γ f, C.setup ⁻¹' {x})).toReal

/-- **`Ĉ(Γ ∣ C)`**, the min-free inference complexity displayed in both papers.-/
@[expose] public noncomputable def unionInferenceComplexity (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum (fun γ => -Real.log (answeringMass μ C Γ (probe γ)))

/-! ### `C̄_ε` at the source's own length

`stochasticInferenceComplexity` takes `ℓ` as a parameter, which is faithful — the
source separates the distribution `P` fixing accuracy from the volume `dμ` fixing
length — but it left the **printed** object unnamed. `sourceStochasticComplexity`
fixes `ℓ` at `−ℍ(U ∣ x)`, so section 8's display finally has a declaration.

The source's bridge is *"if `P` is proportional to `dμ` across the support of `P`
and `C > Γ`, then for `ε = 1`, `C̄_ε(Γ ∣ C) = 𝒞(Γ ∣ C)"*. Both halves are here:
`condEntropy_eq_log_card_of_uniform` is the proportionality half at counting
measure, and `stochasticInferenceComplexity_eq` is the `ε = 1` half.
-/

/-- **`C̄_ε(Γ ∣ C)`** with the source's own length, `ℓ(x) = −ℍ(U ∣ x)`.-/
@[expose] public noncomputable def sourceStochasticComplexity [Fintype U] (μ : Measure U)
    (p : FinPMF U) (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] (ε : ℝ) : ℝ :=
  stochasticInferenceComplexity μ C (fun x => -condEntropy p C.setup x) Γ ε

omit [MeasurableSpace U] in
/-- **`P ∝ dμ` on a fibre makes the two lengths agree.** At counting measure the
proportionality the source assumes is uniformity, and then `−ℍ(U ∣ x)` is exactly
`setupLength x`. This is the sentence *"these two definitions of the length of
`x` are the same"*, proved.-/
public theorem neg_condEntropy_eq_setupLength_of_uniform [Fintype U]
    (p : FinPMF U) (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    (x : C.Setup) {c : ℝ} (hc : 0 < c)
    (huniform : ∀ u : U, C.setup u = x → p.mass u = c) :
    -condEntropy p C.setup x = setupLength C x := by
  rw [condEntropy_eq_log_card_of_uniform p C x hc huniform, setupLength, setupFibreCard]

/-! ## `Ĉ` over an arbitrary setup range

`answeringMass` sums the measure of the union of the answering fibres, and took
that union over a `Finset`, so it carried `[FiniteRange C.setup]` where the
source states none. A union does not need a finite index. `answeringSetOn`
supplies the set form, and nothing else changes — the printed `Ĉ` is the same
displayed formula with the same disjointness justification.
-/

/-- The mass of the union of **all** answering fibres, with no finiteness on the
setup range.-/
@[expose] public noncomputable def answeringMassOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U)
    {G : Type v'} (Γ : U → G) (f : G → Bool) : ℝ :=
  (μ (⋃ x ∈ answeringSetOn C Γ f, C.setup ⁻¹' {x})).toReal

/-- **`Ĉ` with no finiteness on the setup range.** The sum is still over `Γ(U)`,
which the source keeps finite wherever it counts target values.-/
@[expose] public noncomputable def unionInferenceComplexityOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  (rangeFinset Γ).sum (fun γ => -Real.log (answeringMassOn μ C Γ (probe γ)))

/-! ## `C̄_ε` under a prior, via Mathlib's relative entropy

§8 fixes the length at `−ℍ(U ∣ x)`, the conditional Shannon entropy of
`P(u ∣ x)`. `sourceStochasticComplexity` above is the **discrete** form, built on
`condEntropy` over a `FinPMF`. The general-measure form of *"entropy under a
prior `dμ`"* is relative entropy, and the 2008 map has recorded since S4 that
when it is built it should **instantiate** `InformationTheory.klDiv` rather than
define anything. That is what happens here.

The length is the divergence of the conditional law on a setup fibre from the
prior. Its two structural facts come from Mathlib unchanged: it is nonnegative
because `klDiv` is `ℝ≥0∞`-valued, and it vanishes exactly when the fibre's
conditional law *is* the prior — a device whose setup value says nothing pays
nothing.
-/

/-- The conditional law on a setup fibre, `P(· ∣ x)`.-/
@[expose] public noncomputable def condLawOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (x : C.Setup) : Measure U :=
  ProbabilityTheory.cond μ (C.setup ⁻¹' {x})

/-- **The source's `−ℍ(U ∣ x)` under a prior `dμ`**, as relative entropy. No new
definition: this is `InformationTheory.klDiv` at the conditional law.-/
@[expose] public noncomputable def relativeLength (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (x : C.Setup) : ℝ :=
  (InformationTheory.klDiv (condLawOn μ C x) μ).toReal

/-- **`C̄_ε` with the printed length, at general measure.**-/
@[expose] public noncomputable def relativeStochasticComplexity (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] (ε : ℝ) : ℝ :=
  stochasticInferenceComplexity μ C (relativeLength μ C) Γ ε

end AISafetyAtlas.Inference
