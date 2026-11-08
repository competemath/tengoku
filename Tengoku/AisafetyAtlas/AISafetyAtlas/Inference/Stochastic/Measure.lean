module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Device
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.FiniteRange
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Stochastic.Algebra
public import Tengoku.Seed.MeasureTheory.Measure.Typeclasses.Probability
public import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
public import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Section 8 over a general measure — Wolpert 2008

`Stochastic.lean` states Definitions 9–11 and Proposition 6 for a `FinPMF` on a
`Fintype U`. That is not the paper's setting. Wolpert's `U` is *"the set of
worldlines consistent with the laws of physics"*, which is uncountable, so a
finite `U` excludes the intended model outright.

The finiteness the source actually states sits somewhere else: on the **ranges**.
Definition 9 takes *"a function `Γ` with domain `U` and finite range"*, and
Definition 11 is *"for simplicity phrased for countable `X(U)`"*. Nothing in
section 8 asks `U` itself to be finite.

This module states the section-8 ingredients that way: an arbitrary measurable
space `U`, a probability measure, and finiteness on the maps.

## Why no disintegration is needed

The obvious fear about a measure-theoretic restatement is conditioning: `E_P(· ∣ x)`
on a null fibre needs a regular conditional probability, and that needs a standard
Borel space. It does not arise here. Every fibre is `X ⁻¹' {x}` for a map with
finite range, and the accuracy in Definition 9 already maximises only over fibres
of positive mass — the restriction `Stochastic.lean` carries as
`positiveMassSetups`. Conditioning is on positive-measure sets throughout.

## Why no dependency is needed

The mass of a fibre is `μ (X ⁻¹' {x})`, and a Mathlib `Measure` is defined on
*every* set through its outer measure, so no measurability hypothesis is needed to
state anything. Measurability enters only where additivity does, and it is
requested there rather than globally.

`FiniteRange` is deliberately a local three-line class rather than an import:
the only Lean library that has one is PFR, and this development does not depend
on PFR.
-/

namespace AISafetyAtlas.Inference

open MeasureTheory

universe u v v'

variable {U : Type u}

/-! ## Measurability, discharged rather than assumed

Every §8 statement carries `Measurable C.setup` or `Measurable C.concl`. On a
discrete universe those are free, and `fun_prop` is the tactic that knows it — so
models write `by fun_prop` instead of naming the lemma, and the hypothesis stops
being friction. This is the reason the general layer does not make finite models
more expensive to write.
-/

/-- The mass a measure gives the fibre of `X` over `x`.

Stated with no measurability hypothesis: a `Measure` is an outer measure on every
set. Additivity lemmas below request measurability where they need it.-/
@[expose] public noncomputable def massOn [MeasurableSpace U] (μ : Measure U)
    {α : Type v} (X : U → α) (x : α) : ℝ :=
  (μ (X ⁻¹' {x})).toReal

public theorem massOn_nonneg [MeasurableSpace U] (μ : Measure U)
    {α : Type v} (X : U → α) (x : α) : 0 ≤ massOn μ X x :=
  ENNReal.toReal_nonneg

public theorem massOn_eq_zero_of_notMem [MeasurableSpace U] (μ : Measure U)
    {α : Type v} (X : U → α) [FiniteRange X] {x : α} (hx : x ∉ rangeFinset X) :
    massOn μ X x = 0 := by
  have hempty : X ⁻¹' {x} = (∅ : Set U) := by
    ext u
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro h
    exact hx ((mem_rangeFinset X x).mpr ⟨u, h⟩)
  simp [massOn, hempty]

/-! ## Finite additivity over the range

The fibres of a finite-range map partition `U`, so the masses sum to `1` and the
joint masses marginalise. These are the two facts every entropy argument below
rests on, and they are the only place measurability is needed. -/

variable [MeasurableSpace U]

omit [MeasurableSpace U] in
private theorem fibres_pairwiseDisjoint {α : Type v} (X : U → α) (s : Finset α) :
    (s : Set α).PairwiseDisjoint (fun x => X ⁻¹' {x}) := by
  intro a _ b _ hab
  refine Set.disjoint_left.mpr (fun u ha hb => hab ?_)
  simp only [Set.mem_preimage, Set.mem_singleton_iff] at ha hb
  exact ha.symm.trans hb

private theorem measure_fibre_ne_top (μ : Measure U) [IsFiniteMeasure μ]
    {α : Type v} (X : U → α) (x : α) : μ (X ⁻¹' {x}) ≠ ⊤ :=
  measure_ne_top μ _

/-- The masses of a finite-range map sum to `1`.-/
public theorem sum_massOn (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : U → α) [FiniteRange X] (hX : Measurable X) :
    (rangeFinset X).sum (massOn μ X) = 1 := by
  have hmeas : ∀ x ∈ rangeFinset X, MeasurableSet (X ⁻¹' {x}) :=
    fun x _ => hX (measurableSet_singleton x)
  have hcover : (⋃ x ∈ rangeFinset X, X ⁻¹' {x}) = (Set.univ : Set U) := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      Set.mem_univ, iff_true]
    exact ⟨X u, self_mem_rangeFinset X u, rfl⟩
  have hsum := measure_biUnion_finset
    (fibres_pairwiseDisjoint X (rangeFinset X)) hmeas (μ := μ)
  rw [hcover, measure_univ] at hsum
  have : ((1 : ENNReal)).toReal = ((rangeFinset X).sum (fun x => μ (X ⁻¹' {x}))).toReal := by
    rw [hsum]
  rw [ENNReal.toReal_sum (fun x _ => measure_fibre_ne_top μ X x)] at this
  -- The goal's sum is eta-contracted -- `(rangeFinset X).sum (massOn μ X)` --
  -- and `simp [massOn]` no longer fires through that; `unfold` still does.
  unfold massOn
  simpa using this.symm

/-- Joint masses marginalise onto the first coordinate.-/
public theorem sum_massOn_marginal (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} {β : Type v'}
    [MeasurableSpace α] [MeasurableSingletonClass α]
    [MeasurableSpace β] [MeasurableSingletonClass β]
    (X : U → α) (Y : U → β) [FiniteRange Y] (hX : Measurable X) (hY : Measurable Y)
    (a : α) :
    (rangeFinset Y).sum (fun b => massOn μ (fun u => (X u, Y u)) (a, b)) =
      massOn μ X a := by
  have hpair : Measurable (fun u => (X u, Y u)) := hX.prodMk hY
  have hmeas : ∀ b ∈ rangeFinset Y,
      MeasurableSet ((fun u => (X u, Y u)) ⁻¹' {(a, b)}) :=
    fun b _ => hpair (measurableSet_singleton _)
  have hdisj : ((rangeFinset Y : Set β)).PairwiseDisjoint
      (fun b => (fun u => (X u, Y u)) ⁻¹' {(a, b)}) := by
    intro b₁ _ b₂ _ hb
    refine Set.disjoint_left.mpr (fun u h₁ h₂ => hb ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
    exact h₁.2.symm.trans h₂.2
  have hcover : (⋃ b ∈ rangeFinset Y, (fun u => (X u, Y u)) ⁻¹' {(a, b)}) = X ⁻¹' {a} := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
    constructor
    · rintro ⟨b, -, hu, -⟩; exact hu
    · intro hu; exact ⟨Y u, self_mem_rangeFinset Y u, hu, rfl⟩
  have hsum := measure_biUnion_finset hdisj hmeas (μ := μ)
  rw [hcover] at hsum
  have : (μ (X ⁻¹' {a})).toReal =
      ((rangeFinset Y).sum (fun b => μ ((fun u => (X u, Y u)) ⁻¹' {(a, b)}))).toReal := by
    rw [hsum]
  rw [ENNReal.toReal_sum (fun b _ => measure_ne_top μ _)] at this
  simpa [massOn] using this.symm

/-! ## Entropy and mutual information over a general measure -/

/-- A pair of finite-range maps has finite range.-/
public instance instFiniteRangeProd {α : Type v} {β : Type v'}
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y] :
    FiniteRange (fun u => (X u, Y u)) where
  finite_range := by
    refine Set.Finite.subset
      (((FiniteRange.finite_range (X := X)).prod
        (FiniteRange.finite_range (X := Y)))) ?_
    rintro _ ⟨u, rfl⟩
    exact ⟨⟨u, rfl⟩, ⟨u, rfl⟩⟩

omit [MeasurableSpace U] in
public theorem rangeFinset_prod_subset {α : Type v} {β : Type v'}
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y] [DecidableEq α] [DecidableEq β] :
    rangeFinset (fun u => (X u, Y u)) ⊆ rangeFinset X ×ˢ rangeFinset Y := by
  intro c hc
  obtain ⟨u, rfl⟩ := (mem_rangeFinset _ c).mp hc
  exact Finset.mem_product.mpr ⟨self_mem_rangeFinset X u, self_mem_rangeFinset Y u⟩

/-- A joint cell weighs no more than either marginal.-/
public theorem massOn_joint_le_fst (μ : Measure U) [IsFiniteMeasure μ]
    {α : Type v} {β : Type v'} (X : U → α) (Y : U → β) (a : α) (b : β) :
    massOn μ (fun u => (X u, Y u)) (a, b) ≤ massOn μ X a := by
  refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_)
  intro u hu
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hu ⊢
  exact hu.1

public theorem massOn_joint_le_snd (μ : Measure U) [IsFiniteMeasure μ]
    {α : Type v} {β : Type v'} (X : U → α) (Y : U → β) (a : α) (b : β) :
    massOn μ (fun u => (X u, Y u)) (a, b) ≤ massOn μ Y b := by
  refine ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono ?_)
  intro u hu
  simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at hu ⊢
  exact hu.2

/-- Shannon entropy of a finite-range map under `μ`, natural logarithm.-/
@[expose] public noncomputable def entropyOn (μ : Measure U) {α : Type v}
    (X : U → α) [FiniteRange X] : ℝ :=
  - (rangeFinset X).sum fun a =>
      if massOn μ X a = 0 then 0 else massOn μ X a * Real.log (massOn μ X a)

/-- Mutual information of two finite-range maps under `μ`.-/
@[expose] public noncomputable def mutualInfoOn (μ : Measure U) {α : Type v} {β : Type v'}
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y] : ℝ :=
  entropyOn μ X + entropyOn μ Y - entropyOn μ (fun u => (X u, Y u))

/-- Statistical independence, pointwise on the joint pushforward. The `FinPMF`
layer's `StatisticallyIndependent` is this over a finite `U`.-/
@[expose] public def IndependentOn (μ : Measure U) {α : Type v} {β : Type v'}
    (X : U → α) (Y : U → β) : Prop :=
  ∀ a b, massOn μ (fun u => (X u, Y u)) (a, b) = massOn μ X a * massOn μ Y b

/-! ## Gibbs' inequality and its equality case, over a general measure

The pointwise steps are `gibbs_cell` and `gibbs_cell_eq_iff`, which are statements
about real numbers and transfer unchanged. Only the summation apparatus differs:
the rectangle is `X(U) × Y(U)` rather than a product of image `Finset`s over a
finite `U`. -/

variable {α : Type v} {β : Type v'}
variable [MeasurableSpace α] [MeasurableSingletonClass α] [DecidableEq α]
variable [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β]

/-- The Gibbs term contributed by one cell of `X(U) × Y(U)`.-/
private noncomputable def cellFn (μ : Measure U) (X : U → α) (Y : U → β) (c : α × β) : ℝ :=
  (if massOn μ (fun u => (X u, Y u)) c = 0 then 0
    else massOn μ (fun u => (X u, Y u)) c * Real.log (massOn μ X c.1)) +
  (if massOn μ (fun u => (X u, Y u)) c = 0 then 0
    else massOn μ (fun u => (X u, Y u)) c * Real.log (massOn μ Y c.2)) -
  (if massOn μ (fun u => (X u, Y u)) c = 0 then 0
    else massOn μ (fun u => (X u, Y u)) c *
      Real.log (massOn μ (fun u => (X u, Y u)) c))

private noncomputable def slackFn (μ : Measure U) (X : U → α) (Y : U → β) (c : α × β) : ℝ :=
  massOn μ X c.1 * massOn μ Y c.2 - massOn μ (fun u => (X u, Y u)) c

omit [MeasurableSpace α] [MeasurableSingletonClass α] [DecidableEq α] [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β] in
private theorem cellFn_le (μ : Measure U) [IsFiniteMeasure μ]
    (X : U → α) (Y : U → β) (c : α × β) : cellFn μ X Y c ≤ slackFn μ X Y c :=
  gibbs_cell (massOn_nonneg μ _ c)
    (massOn_joint_le_fst μ X Y c.1 c.2) (massOn_joint_le_snd μ X Y c.1 c.2)

omit [MeasurableSpace α] [MeasurableSingletonClass α] [DecidableEq α] [MeasurableSpace β] [MeasurableSingletonClass β] [DecidableEq β] in
private theorem cellFn_eq_iff (μ : Measure U) [IsFiniteMeasure μ]
    (X : U → α) (Y : U → β) (c : α × β) :
    cellFn μ X Y c = slackFn μ X Y c ↔
      massOn μ (fun u => (X u, Y u)) c = massOn μ X c.1 * massOn μ Y c.2 :=
  gibbs_cell_eq_iff (massOn_nonneg μ _ c)
    (massOn_joint_le_fst μ X Y c.1 c.2) (massOn_joint_le_snd μ X Y c.1 c.2)

private theorem sum_slackFn (μ : Measure U) [IsProbabilityMeasure μ]
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) :
    (rangeFinset X ×ˢ rangeFinset Y).sum (slackFn μ X Y) = 0 := by
  have hjoint : (rangeFinset X ×ˢ rangeFinset Y).sum
      (massOn μ (fun u => (X u, Y u))) = 1 := by
    rw [← Finset.sum_subset (rangeFinset_prod_subset X Y)
      (fun c _ hc => massOn_eq_zero_of_notMem μ _ hc)]
    exact sum_massOn μ (fun u => (X u, Y u)) (hX.prodMk hY)
  have hprod : (rangeFinset X ×ˢ rangeFinset Y).sum
      (fun c => massOn μ X c.1 * massOn μ Y c.2) = 1 := by
    rw [Finset.sum_product]
    have hrow : ∀ a ∈ rangeFinset X,
        (rangeFinset Y).sum (fun b => massOn μ X a * massOn μ Y b) = massOn μ X a := by
      intro a _
      rw [← Finset.mul_sum, sum_massOn μ Y hY, mul_one]
    rw [Finset.sum_congr rfl hrow]
    exact sum_massOn μ X hX
  unfold slackFn
  rw [Finset.sum_sub_distrib, hprod, hjoint, sub_self]

/-- `−M` is the cell-by-cell Gibbs sum over the rectangle `X(U) × Y(U)`.-/
private theorem neg_mutualInfoOn_eq_cellSum (μ : Measure U) [IsProbabilityMeasure μ]
    (X : U → α) (Y : U → β) [FiniteRange X] [FiniteRange Y]
    (hX : Measurable X) (hY : Measurable Y) :
    -mutualInfoOn μ X Y = (rangeFinset X ×ˢ rangeFinset Y).sum (cellFn μ X Y) := by
  classical
  set qm := massOn μ (fun u => (X u, Y u)) with hqm
  set pX := massOn μ X with hpX
  set pY := massOn μ Y with hpY
  have hext : ∀ f : α × β → ℝ, (∀ c, qm c = 0 → f c = 0) →
      (rangeFinset (fun u => (X u, Y u))).sum f = (rangeFinset X ×ˢ rangeFinset Y).sum f := by
    intro f hf
    exact Finset.sum_subset (rangeFinset_prod_subset X Y)
      (fun c _ hc => hf c (massOn_eq_zero_of_notMem μ _ hc))
  have hXsum : (rangeFinset X).sum (fun a => if pX a = 0 then 0 else pX a * Real.log (pX a)) =
      (rangeFinset X ×ˢ rangeFinset Y).sum (fun c => if qm c = 0 then 0 else qm c * Real.log (pX c.1)) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hpa : pX a = 0
    · refine (ite_eq_left hpa).trans ?_
      refine (Finset.sum_eq_zero (fun b _ => ?_)).symm
      have hq0 : qm (a, b) = 0 :=
        le_antisymm (hpa ▸ massOn_joint_le_fst μ X Y a b) (massOn_nonneg μ _ (a, b))
      exact ite_eq_left hq0
    · rw [ite_eq_right hpa]
      have hz : ∀ b ∈ rangeFinset Y,
          (if qm (a, b) = 0 then 0 else qm (a, b) * Real.log (pX a)) = qm (a, b) * Real.log (pX a) := by
        intro b _
        by_cases hb : qm (a, b) = 0
        · rw [ite_eq_left hb, hb, zero_mul]
        · rw [ite_eq_right hb]
      rw [Finset.sum_congr rfl hz, ← Finset.sum_mul, hqm, sum_massOn_marginal μ X Y hX hY]
  have hYsum : (rangeFinset Y).sum (fun b => if pY b = 0 then 0 else pY b * Real.log (pY b)) =
      (rangeFinset X ×ˢ rangeFinset Y).sum (fun c => if qm c = 0 then 0 else qm c * Real.log (pY c.2)) := by
    rw [Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hpb : pY b = 0
    · refine (ite_eq_left hpb).trans ?_
      refine (Finset.sum_eq_zero (fun a _ => ?_)).symm
      have hq0 : qm (a, b) = 0 :=
        le_antisymm (hpb ▸ massOn_joint_le_snd μ X Y a b) (massOn_nonneg μ _ (a, b))
      exact ite_eq_left hq0
    · rw [ite_eq_right hpb]
      have hz : ∀ a ∈ rangeFinset X,
          (if qm (a, b) = 0 then 0 else qm (a, b) * Real.log (pY b)) = qm (a, b) * Real.log (pY b) := by
        intro a _
        by_cases ha : qm (a, b) = 0
        · rw [ite_eq_left ha, ha, zero_mul]
        · rw [ite_eq_right ha]
      rw [Finset.sum_congr rfl hz, ← Finset.sum_mul]
      congr 1
      have hswap : ∀ a ∈ rangeFinset X, qm (a, b) = massOn μ (fun u => (Y u, X u)) (b, a) := by
        intro a _
        have hset : (fun u => (X u, Y u)) ⁻¹' {(a, b)}
            = (fun u => (Y u, X u)) ⁻¹' {(b, a)} := by
          ext u
          simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq]
          tauto
        simp [hqm, massOn, hset]
      rw [Finset.sum_congr rfl hswap, sum_massOn_marginal μ Y X hY hX]
  have hJsum : (rangeFinset (fun u => (X u, Y u))).sum
        (fun c => if qm c = 0 then 0 else qm c * Real.log (qm c)) =
      (rangeFinset X ×ˢ rangeFinset Y).sum (fun c => if qm c = 0 then 0 else qm c * Real.log (qm c)) :=
    hext _ (fun c hc => ite_eq_left hc)
  unfold cellFn
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← hXsum, ← hYsum, ← hJsum]
  unfold mutualInfoOn entropyOn
  ring

/-! ## Definitions 9–11 over a general measure

Conditional expectation is taken **without an integral**. The only function
Definition 9 conditions on is `Y · f(Γ)`, a product of two `±1`-valued functions,
so it is `+1` exactly where the device's conclusion agrees with the probe and `−1`
elsewhere. Its conditional expectation is therefore `2·P(agree ∣ x) − 1`, and that
probability is a ratio of two fibre masses. No Bochner integral, no integrability
side condition, and the same shape the finite layer already uses. -/

/-- Realized setup values of positive `μ`-mass. Definition 9's maximum ranges over
these: the source's conditional expectation is undefined on a null fibre.-/
@[expose] public noncomputable def positiveMassSetupsOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup] : Finset C.Setup :=
  (rangeFinset C.setup).filter fun x => 0 < massOn μ C.setup x

/-- Some fibre carries positive mass, because the total is `1`.

**No measurability hypothesis.** An earlier version required `Measurable C.setup`
and derived the contradiction from `sum_massOn`, which needs the fibres to be
measurable so that their masses add *exactly*. Nonemptiness needs far less: the
fibres cover `U`, so sub-additivity alone forces one of them to be non-null, and
`measure_biUnion_finset_le` holds for arbitrary sets. Removing the hypothesis
here is what lets Definition 9 be stated without it — the source states no
measurability anywhere.-/
public theorem positiveMassSetupsOn_nonempty (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup] :
    (positiveMassSetupsOn μ C).Nonempty := by
  classical
  by_contra hempty
  rw [Finset.not_nonempty_iff_eq_empty] at hempty
  have hzero : ∀ x ∈ rangeFinset C.setup, μ (C.setup ⁻¹' {x}) = 0 := by
    intro x hx
    by_contra hne
    have hpos : 0 < massOn μ C.setup x := by
      rw [massOn]
      exact ENNReal.toReal_pos hne (measure_ne_top μ _)
    have : x ∈ positiveMassSetupsOn μ C := Finset.mem_filter.mpr ⟨hx, hpos⟩
    rw [hempty] at this
    exact absurd this (Finset.notMem_empty x)
  -- The fibres over the realized values cover `U`.
  have hcover : (Set.univ : Set U) ⊆ ⋃ x ∈ rangeFinset C.setup, C.setup ⁻¹' {x} := by
    intro u _
    exact Set.mem_biUnion ((mem_rangeFinset C.setup (C.setup u)).mpr ⟨u, rfl⟩) rfl
  have hle : (1 : ENNReal) ≤ 0 := by
    calc (1 : ENNReal) = μ Set.univ := (measure_univ (μ := μ)).symm
      _ ≤ μ (⋃ x ∈ rangeFinset C.setup, C.setup ⁻¹' {x}) := measure_mono hcover
      _ ≤ (rangeFinset C.setup).sum (fun x => μ (C.setup ⁻¹' {x})) :=
          measure_biUnion_finset_le _ _
      _ = 0 := by rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero]
  simp at hle

/-- `P(the device's conclusion agrees with `h` ∣ `X = x`)`, `0` on a null fibre.-/
@[expose] public noncomputable def condAgreeOn (μ : Measure U)
    {α : Type v} (X : U → α) (x : α) (h : U → Bool) : ℝ :=
  if massOn μ X x = 0 then 0
  else massOn μ (fun u => (X u, h u)) (x, true) / massOn μ X x

/-- The conditional expectation of a `±1`-valued function, as `2p − 1`.-/
@[expose] public noncomputable def condExpectPmOn (μ : Measure U)
    {α : Type v} (X : U → α) (x : α) (h : U → Bool) : ℝ :=
  2 * condAgreeOn μ X x h - 1

/--
**Definition 9 over a general measure.** *"a device `(X,Y)` (weakly) infers `Γ`
with (covariance) accuracy `ε` iff `[Σ_{f ∈ π(Γ)} max_x E_P(Y f(Γ) ∣ x)] / |Γ(U)| = ε`."*

`U` is arbitrary; the finiteness is the source's own, on `Γ(U)`.

**No measurability hypothesis.** Nonemptiness of `positiveMassSetupsOn` — all
the `sup'` needs — follows from sub-additivity alone
(`positiveMassSetupsOn_nonempty`), so `Measurable C.setup` never enters. It
would have been the one condition here the source never states: the source never
has to say which sets it can weigh.

**`[FiniteRange C.setup]` is in this signature**, where the source states no
finiteness on `X(U)` for this definition. It is what makes the printed `max_x`
denote at a `Finset.sup'`: over an infinite realized setup range the maximum
need not be attained. That restriction is why `inferenceAccuracySupOn` exists —
it states the printed `max_x` as an `sSup` over the positive-mass setups and
carries no finiteness, and `accuracySupOn_eq_of_isGreatest` says it *is* the
printed maximum wherever that exists. The provenance row is `SOURCE-EXACT` on
the supremum form; this one is its finite-range instance.-/
public noncomputable def inferenceAccuracyOn (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup]
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  if (rangeFinset Γ).card = 0 then 0
  else
    (rangeFinset Γ).sum (fun γ =>
      (positiveMassSetupsOn μ C).sup' (positiveMassSetupsOn_nonempty μ C)
        (fun x => condExpectPmOn μ C.setup x
          (fun u => C.concl u == probe γ (Γ u)))) /
      ((rangeFinset Γ).card : ℝ)

/-- Setup entropy of a device under `μ`.-/
@[expose] public noncomputable def setupEntropyOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup] : ℝ :=
  entropyOn μ C.setup

/--
**Definition 10 over a general measure.** `1 − M_P(X₁,X₂) / [H_P(X₁) + H_P(X₂)]`.

The zero-denominator branch is a Lean totalization, not a source case, exactly as
in the finite layer.-/
@[expose] public noncomputable def miDistinguishabilityOn (μ : Measure U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [FiniteRange C₁.setup] [FiniteRange C₂.setup] : ℝ :=
  if setupEntropyOn μ C₁ + setupEntropyOn μ C₂ = 0 then 1
  else 1 - mutualInfoOn μ C₁.setup C₂.setup /
    (setupEntropyOn μ C₁ + setupEntropyOn μ C₂)

/--
**Definition 11.** *"the counting distinguishability of two devices is
`1 − [Σ_{x₁,x₂ : ∃u, X₁(u)=x₁, X₂(u)=x₂} 1] / (|X₁(U)| × |X₂(U)|)`."*

The printed formula names `P` in its preamble and then does not use it: the
displayed quantity counts jointly realized setup pairs. So this definition needs
**no measure at all**, only the source's countable — here finite — setup ranges.-/
@[expose] public noncomputable def countingDistinguishabilityOn
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [FiniteRange C₁.setup] [FiniteRange C₂.setup]
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] : ℝ :=
  1 - ((rangeFinset (fun u => (C₁.setup u, C₂.setup u))).card : ℝ) /
    (((rangeFinset C₁.setup).card : ℝ) * ((rangeFinset C₂.setup).card : ℝ))

/-! ## Proposition 6, step 1, over a general measure

The two probes of a `Bool`-valued target are the identity and the negation, so
Definition 9's sum is `max_x E(g∣x) + max_x E(−g∣x) = max − min = |difference|`.
Nothing here is finite except the two setup values the source stipulates. -/

/-- A fibre splits over the two values of a `Bool`-valued map.-/
public theorem massOn_bool_split (μ : Measure U) [IsProbabilityMeasure μ]
    {α : Type v} [MeasurableSpace α] [MeasurableSingletonClass α]
    (X : U → α) (h : U → Bool) (hX : Measurable X) (hh : Measurable h) (x : α) :
    massOn μ (fun u => (X u, h u)) (x, true) +
      massOn μ (fun u => (X u, h u)) (x, false) = massOn μ X x := by
  classical
  have hpair : Measurable (fun u => (X u, h u)) := hX.prodMk hh
  have hmeas : ∀ b ∈ ({true, false} : Finset Bool),
      MeasurableSet ((fun u => (X u, h u)) ⁻¹' {(x, b)}) :=
    fun b _ => hpair (measurableSet_singleton _)
  have hdisj : (({true, false} : Finset Bool) : Set Bool).PairwiseDisjoint
      (fun b => (fun u => (X u, h u)) ⁻¹' {(x, b)}) := by
    intro b₁ _ b₂ _ hb
    refine Set.disjoint_left.mpr (fun u h₁ h₂ => hb ?_)
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Prod.mk.injEq] at h₁ h₂
    exact h₁.2.symm.trans h₂.2
  have hcover : (⋃ b ∈ ({true, false} : Finset Bool),
      (fun u => (X u, h u)) ⁻¹' {(x, b)}) = X ⁻¹' {x} := by
    ext u
    simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff,
      Prod.mk.injEq, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨b, -, hu, -⟩; exact hu
    · intro hu; exact ⟨h u, by cases h u <;> simp, hu, rfl⟩
  have hsum := measure_biUnion_finset hdisj hmeas (μ := μ)
  rw [hcover] at hsum
  have hreal : (μ (X ⁻¹' {x})).toReal =
      (({true, false} : Finset Bool).sum
        (fun b => μ ((fun u => (X u, h u)) ⁻¹' {(x, b)}))).toReal := by rw [hsum]
  rw [ENNReal.toReal_sum (fun b _ => measure_ne_top μ _)] at hreal
  simp only [Finset.sum_insert (by simp : (true : Bool) ∉ ({false} : Finset Bool)),
    Finset.sum_singleton] at hreal
  simpa [massOn] using hreal.symm

/-! ### Bounds, and Definition 9's supremum form

The printed `max_x E_P(Y δ(Γ) | x)` is a maximum over setup values, and
`inferenceAccuracyOn` renders it as a `Finset.sup'` — which is why that
definition carries `[FiniteRange C.setup]` even though the print states no
finiteness on `X(U)`.

Under the acceptance rule the question is what the printed formula needs in
order to denote. Conditional expectations of a `±1`-valued quantity lie in
`[-1, 1]`, so a **supremum** denotes on any setup range whose positive-mass part
is nonempty; finiteness is not what makes the expression meaningful. Nonemptiness
*is*: under an arbitrary probability measure every fibre can be null — Lebesgue
measure with the identity setup — and then there is nothing to take a maximum
over and the printed formula denotes nothing. So the hypothesis below is forced
and the finite range is not.

`positiveMassSetupsOn_nonempty` derives nonemptiness from `[FiniteRange C.setup]`
by finite sub-additivity, and that argument does not survive an uncountable
range. It is replaced here by an explicit hypothesis, which `FiniteRange`
discharges.
-/

omit [MeasurableSpace U] in
private theorem probe_bool_true (b : Bool) : probe true b = b := by
  cases b <;> simp [probe]

omit [MeasurableSpace U] in
private theorem probe_bool_false (b : Bool) : probe false b = !b := by
  cases b <;> simp [probe]

omit [MeasurableSpace U] in
private theorem agree_probe_false (f g : U → Bool) (u : U) :
    (f u == probe false (g u)) = !(f u == g u) := by
  rw [probe_bool_false]
  cases f u <;> cases g u <;> simp

/-! ## Proposition 6, steps 2b and 3, over a general measure -/

/-- `P(the two conclusions agree ∣ X₁ = x₁, X₂ = x₂)`. The source's `zᵢ`.-/
@[expose] public noncomputable def cellAgreeProbOn (μ : Measure U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) : ℝ :=
  condAgreeOn μ (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂)
    (fun u => C₁.concl u == C₂.concl u)

public theorem condAgreeOn_mem (μ : Measure U) [IsFiniteMeasure μ]
    {α : Type v} (X : U → α) (x : α) (h : U → Bool) :
    0 ≤ condAgreeOn μ X x h ∧ condAgreeOn μ X x h ≤ 1 := by
  unfold condAgreeOn
  by_cases hx : massOn μ X x = 0
  · rw [ite_eq_left hx]; norm_num
  · rw [ite_eq_right hx]
    have hpos : 0 < massOn μ X x :=
      lt_of_le_of_ne (massOn_nonneg μ X x) (Ne.symm hx)
    have hle : massOn μ (fun u => (X u, h u)) (x, true) ≤ massOn μ X x :=
      massOn_joint_le_fst μ X h x true
    exact ⟨div_nonneg (massOn_nonneg μ _ _) (le_of_lt hpos), (div_le_one hpos).mpr hle⟩

public theorem cellAgreeProbOn_mem (μ : Measure U) [IsFiniteMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) :
    0 ≤ cellAgreeProbOn μ C₁ C₂ x₁ x₂ ∧ cellAgreeProbOn μ C₁ C₂ x₁ x₂ ≤ 1 :=
  condAgreeOn_mem μ _ _ _

/-- The source's `z⃗`, defined from the measure.-/
@[expose] public noncomputable def prop6QuadrupleOfOn (μ : Measure U) [IsFiniteMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    (a₁ b₁ : C₁.Setup) (a₂ b₂ : C₂.Setup) : Prop6Quadruple where
  z1 := cellAgreeProbOn μ C₁ C₂ a₁ a₂
  z2 := cellAgreeProbOn μ C₁ C₂ a₁ b₂
  z3 := cellAgreeProbOn μ C₁ C₂ b₁ a₂
  z4 := cellAgreeProbOn μ C₁ C₂ b₁ b₂
  z1_mem := cellAgreeProbOn_mem μ C₁ C₂ a₁ a₂
  z2_mem := cellAgreeProbOn_mem μ C₁ C₂ a₁ b₂
  z3_mem := cellAgreeProbOn_mem μ C₁ C₂ b₁ a₂
  z4_mem := cellAgreeProbOn_mem μ C₁ C₂ b₁ b₂

/-- The agreement mass of a joint cell is `zᵢ` times the cell's mass.-/
private theorem agreeMass_eq (μ : Measure U) [IsFiniteMeasure μ]
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) :
    massOn μ (fun u => ((C₁.setup u, C₂.setup u), C₁.concl u == C₂.concl u))
        ((x₁, x₂), true)
      = cellAgreeProbOn μ C₁ C₂ x₁ x₂ *
        massOn μ (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂) := by
  unfold cellAgreeProbOn condAgreeOn
  by_cases hx : massOn μ (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂) = 0
  · rw [ite_eq_left hx, hx, zero_mul]
    exact le_antisymm
      (hx ▸ massOn_joint_le_fst μ (fun u => (C₁.setup u, C₂.setup u))
        (fun u => C₁.concl u == C₂.concl u) (x₁, x₂) true)
      (massOn_nonneg μ _ _)
  · rw [ite_eq_right hx]
    field_simp

/-! ### A finite-range map partitions a measurable set

The workhorse for Proposition 8 at general measure. `FinPMF`'s version of this is
`Finset.sum_fiberwise`; here the fibres are measurable sets and the sum is over
`μ`, so it needs the partition to be genuinely disjoint and measurable. That
requirement is the whole reason the general-measure form of Propositions 8 and 11
carries measurability where the printed statement carries none.
-/

/-! ### Definition 9 and Proposition 8 without a finite setup range -/

/-- The positive-mass setup values, as a **set**: no finiteness.-/
@[expose] public def positiveMassSetOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) : Set C.Setup :=
  {x | 0 < massOn μ C.setup x}

/-- The printed `max_x` as a supremum over that set. Bounded because the
conditional expectations are, so this denotes whenever the set is nonempty.-/
@[expose] public noncomputable def accuracySupOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (h : U → Bool) : ℝ :=
  sSup ((fun x => condExpectPmOn μ C.setup x h) '' positiveMassSetOn μ C)

/-- **Definition 9's covariance accuracy over an arbitrary setup range.** The
`Finset.sup'` of `inferenceAccuracyOn` becomes an `sSup`; nothing else moves.-/
@[expose] public noncomputable def inferenceAccuracySupOn (μ : Measure U)
    (C : InferenceDevice.{u, v} U)
    {G : Type v'} [DecidableEq G] (Γ : U → G) [FiniteRange Γ] : ℝ :=
  if (rangeFinset Γ).card = 0 then 0
  else
    (rangeFinset Γ).sum (fun γ =>
      accuracySupOn μ C (fun u => C.concl u == probe γ (Γ u))) /
      ((rangeFinset Γ).card : ℝ)

/-- **The printed `max` and the `sSup` agree whenever the maximum exists**, on
any setup range. `accuracySupOn_eq_sup'` is the finite instance of this; an
infinite setup range can still attain its maximum, and then the supremum form is
the printed object rather than a normalization of it.-/
public theorem accuracySupOn_eq_of_isGreatest (μ : Measure U)
    (C : InferenceDevice.{u, v} U) (h : U → Bool) {m : ℝ}
    (hm : IsGreatest ((fun x => condExpectPmOn μ C.setup x h) ''
      positiveMassSetOn μ C) m) :
    accuracySupOn μ C h = m :=
  hm.csSup_eq

/-- On a finite setup range the two forms are the same object, so the widening
adds reach and changes nothing already proved. `positiveMassSetOn` and
`positiveMassSetupsOn` have the same members: a value of positive mass has a
nonempty fibre and is therefore realized.-/
public theorem accuracySupOn_eq_sup' (μ : Measure U) [IsProbabilityMeasure μ]
    (C : InferenceDevice.{u, v} U) [FiniteRange C.setup] [DecidableEq C.Setup]
    (h : U → Bool) :
    accuracySupOn μ C h
      = (positiveMassSetupsOn μ C).sup' (positiveMassSetupsOn_nonempty μ C)
          (fun x => condExpectPmOn μ C.setup x h) := by
  classical
  rw [Finset.sup'_eq_csSup_image]
  unfold accuracySupOn
  congr 1
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x, ?_, rfl⟩
    simp only [Finset.coe_filter, Set.mem_ofPred_eq, positiveMassSetupsOn]
    refine ⟨?_, hx⟩
    -- Positive mass forces a nonempty fibre, hence a realized value.
    by_contra hmem
    have hempty : C.setup ⁻¹' {x} = (∅ : Set U) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro hu
      exact hmem ((mem_rangeFinset C.setup x).mpr ⟨u, hu⟩)
    rw [positiveMassSetOn, Set.mem_ofPred_eq, massOn, hempty] at hx
    simp at hx
  · rintro ⟨x, hx, rfl⟩
    exact ⟨x, (Finset.mem_filter.mp hx).2, rfl⟩

/-! ### `cov = 1` and weak inference, over a general measure

2018 states after its Definition 6: *"Clearly `cov(D, Γ) ≤ 1.0`, and if `P` is
nowhere 0, then `cov(D, Γ) = 1.0` iff `D > Γ`."* Both halves were proved only
over a `FinPMF`, hence `[Fintype U]`, where the print says *"probability
measure"*. They are proved here at general measure.

**The nowhere-zero hypothesis is doing real work, and more of it than in the
finite case.** Over a general measure `cov = 1` forces the device to agree with
the probe *almost everywhere* on a fibre, not everywhere, while `WeaklyInfers`
quantifies over every point of the fibre. The gap is exactly a null set, so the
converse needs every nonempty set to be non-null. `hatom` below — every
singleton has positive measure — is the general form of the printed *"`P` is
nowhere 0"*, and it is what collapses "almost everywhere" back to "everywhere".
-/

/-! ## Definition 10 beyond a finite setup range

`entropyOn` sums over `rangeFinset X`, so Definition 10 carries
`[FiniteRange C.setup]` where the source states none. The printed
`1 − M/(H₁+H₂)` is a ratio, and on a range where an entropy diverges it is
`∞/∞` and denotes nothing — so **countably supported with finite entropy** is
the largest domain the printed formula reaches, not arbitrary support.

That is what the `tsum` form below expresses: the sum ranges over the whole
value type, the unrealized values contribute `0` because their mass is `0`, and
summability is the hypothesis that the entropy is finite. On a finite range the
two forms are literally the same number.
-/

/-- One term of the entropy sum, with the source's own convention at zero mass.-/
@[expose] public noncomputable def entropyTerm (μ : Measure U) {α : Type v}
    (X : U → α) (a : α) : ℝ :=
  if massOn μ X a = 0 then 0 else massOn μ X a * Real.log (massOn μ X a)

/-- **Entropy over an arbitrary value range.** A `tsum` over the whole type: the
unrealized values contribute nothing, so this is the printed sum over `X(U)`
wherever that sum denotes.-/
@[expose] public noncomputable def entropySum (μ : Measure U) {α : Type v}
    (X : U → α) : ℝ :=
  -∑' a : α, entropyTerm μ X a

/-- **Mutual information over arbitrary ranges**, from the same sums.-/
@[expose] public noncomputable def mutualInfoSum (μ : Measure U)
    {α : Type v} {β : Type v'} (X : U → α) (Y : U → β) : ℝ :=
  entropySum μ X + entropySum μ Y - entropySum μ (fun u => (X u, Y u))

/-- **Definition 10 with no finiteness on either setup range.**-/
@[expose] public noncomputable def miDistinguishabilitySum (μ : Measure U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U) : ℝ :=
  if entropySum μ C₁.setup + entropySum μ C₂.setup = 0 then 1
  else 1 - mutualInfoSum μ C₁.setup C₂.setup /
    (entropySum μ C₁.setup + entropySum μ C₂.setup)

end AISafetyAtlas.Inference
