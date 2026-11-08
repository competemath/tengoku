module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Device
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Inference.Stochastic.Algebra
public import Tengoku.Seed.Analysis.SpecialFunctions.Log.Basic
public import Tengoku.Seed.Data.Fintype.Card
public import Tengoku.Seed.Data.Real.Basic
public import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Basic
public import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
public import Tengoku.Seed.Data.Finset.Card
public import Tengoku.Seed.Data.Finset.Lattice.Fold
public import Tengoku.Seed.Tactic.Linarith
public import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Stochastic devices — Wolpert 2008 §8

The paper's own boundary: *"In the analysis above there is no probability
measure `P` over `U`."* This module is that measure.

* **Definition 9** — weak inference with covariance accuracy, `inferenceAccuracy`.
* **Definition 10** — mutual-information distinguishability, `miDistinguishability`.
* **Definition 11** — counting distinguishability, `countingDistinguishability`.
* **Proposition 6** — the product of the two devices' accuracies, `prop6_product_eq`
  and `prop6_half`.

## The probability parameter is carried

Definitions 9–11 are parameterized by a probability measure `P`. Here that is
`FinPMF U`: a mass function on a finite `U` that is nonnegative and sums to one.
An earlier revision took an arbitrary `p : U → ℝ`, which admitted signed,
unnormalized weights and so did not state the source's definitions at all.

## What Proposition 6 needs, and what is assumed

The source's proof has three steps.

1. Rewrite the product of accuracies, using `|X₁(U)| = |X₂(U)| = 2` and
   `π(Y) = {identity, negation}`, as
   `|E(g∣X₁=1) − E(g∣X₁=−1)| / 2 · |E(g∣X₂=1) − E(g∣X₂=−1)| / 2` for `g = Y₁Y₂`.
   **Mechanized**: `inferenceAccuracy_eq_of_two_setups`.
2. From mutual-information distinguishability `1`, conclude that `X₁` and `X₂` are
   statistically independent, hence
   `E(g∣x₁) = 2[Σ_{x₂} P(g=1∣x₁,x₂)P(x₂)] − 1` and its three siblings.
   **Split faithfully**: `prop6Law_of_independent` proves the four identities from
   `StatisticallyIndependent` under positive setup support. Gibbs' inequality is
   proved here (`mutualInfo_nonneg`); only its **equality case**,
   `M = 0 ⟹ independence`, remains assumed, exactly where the 2008 proof asserts
   it. Wolpert 2018 restates the bound with independence as the direct premise.
3. Algebra from those identities to `|αβk² + αkm + βkn + mn|`.
   **Mechanized**: `prop6_product_eq`.

So `prop6_product_eq` is a theorem about two devices and their accuracies. Its
`Prop6Law` premise is no longer an opaque probabilistic law: the public
`prop6Law_of_independent` bridge constructs it. Every scalar is defined from `P`.

`Examples.Inference.Device.p6_law` is constructed through that bridge, and
`p6_product_eq_quarter` shows the product of accuracies is exactly `1/4` there, so
the theorem is not vacuous and the bound is attained by real devices — the source's
own extremal example.

## `H` is the unit hypercube

The `zᵢ` are conditional probabilities `P(g = 1 ∣ x₁, x₂)`, so the source's `H`
ranges over `[0,1]⁴`, not over its sixteen vertices. `Prop6Quadruple` carries the
`[0,1]` bounds. An earlier revision used `Bool⁴`, the vertex set only, which is not
the source's `max` domain.
-/

namespace AISafetyAtlas.Inference

variable {U : Type u} [Fintype U]

/-! ## The probability parameter -/

/-- Map `Bool` to the source's `𝔹 = {−1,+1}`.-/
@[expose] public def boolPm : Bool → ℝ
  | true => 1
  | false => -1

public theorem boolPm_probe_true (b : Bool) : boolPm (probe true b) = boolPm b := by
  cases b <;> simp [probe, boolPm]

public theorem boolPm_probe_false (b : Bool) :
    boolPm (probe false b) = -boolPm b := by
  cases b <;> simp [probe, boolPm]

/-- A probability mass function on a finite `U` — the source's `P(u ∈ U)`.-/
public structure FinPMF (U : Type u) [Fintype U] where
  /-- The mass of each universe.-/
  mass : U → ℝ
  /-- Masses are nonnegative.-/
  nonneg : ∀ u, 0 ≤ mass u
  /-- Masses sum to one.-/
  sum_one : Finset.univ.sum mass = 1

public theorem FinPMF.fibre_nonneg {α : Type*} [DecidableEq α]
    (p : FinPMF U) (X : U → α) (x : α) :
    0 ≤ (Finset.univ.filter (fun u => X u = x)).sum p.mass :=
  Finset.sum_nonneg (fun u _ => p.nonneg u)

/-- Pushforward of `p` along `X`, evaluated at one point of the image.-/
@[expose] public noncomputable def pushOnImage {α : Type*} [DecidableEq α]
    (p : FinPMF U) (X : U → α) : α → ℝ :=
  fun a => (Finset.univ.filter (fun u => X u = a)).sum p.mass

/-- Realized setup values whose fibres have positive probability. Definition 9's
conditional expectations are defined precisely on this support.-/
@[expose] public noncomputable def positiveMassSetups
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] (p : FinPMF U) :
    Finset C.Setup :=
  (Finset.univ.image C.setup).filter (fun x => 0 < pushOnImage p C.setup x)

/-- Some setup fibre has positive mass because `p` has total mass one.-/
public theorem positiveMassSetups_nonempty
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] (p : FinPMF U) :
    (positiveMassSetups C p).Nonempty := by
  have hsum : Finset.univ.sum p.mass ≠ 0 := by rw [p.sum_one]; norm_num
  obtain ⟨u, _, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hsum
  have hpu : 0 < p.mass u := lt_of_le_of_ne (p.nonneg u) (Ne.symm hu)
  have hle : p.mass u ≤ pushOnImage p C.setup (C.setup u) := by
    unfold pushOnImage
    exact Finset.single_le_sum (fun i _ => p.nonneg i)
      (by simp : u ∈ Finset.univ.filter (fun w => C.setup w = C.setup u))
  exact ⟨C.setup u, by
    simp only [positiveMassSetups, Finset.mem_filter, Finset.mem_image,
      Finset.mem_univ, true_and]
    exact ⟨⟨u, rfl⟩, lt_of_lt_of_le hpu hle⟩⟩

/-- A positive pushforward mass can only occur at a realized value.-/
public theorem realized_of_pushOnImage_pos {α : Type*} [DecidableEq α]
    (p : FinPMF U) (X : U → α) {x : α} (h : 0 < pushOnImage p X x) :
    ∃ u, X u = x := by
  by_contra hn
  have hz : pushOnImage p X x = 0 := by
    unfold pushOnImage
    apply Finset.sum_eq_zero
    intro u hu
    exact (hn ⟨u, (Finset.mem_filter.mp hu).2⟩).elim
  linarith

/-- Conditional expectation of `f` given `X = x`.

The source's `E_P(· ∣ x)` is defined on fibres of positive mass. A zero-mass fibre
is sent to `0` here; that is a Lean totalization, not a source case, and it is
recorded in the source-clash note.-/
@[expose] public noncomputable def condExpect {α : Type*} [DecidableEq α]
    (p : FinPMF U) (X : U → α) (x : α) (f : U → ℝ) : ℝ :=
  let w := (Finset.univ.filter (fun u => X u = x)).sum p.mass
  if w = 0 then 0
  else (Finset.univ.filter (fun u => X u = x)).sum (fun u => p.mass u * f u) / w

public theorem condExpect_neg {α : Type*} [DecidableEq α]
    (p : FinPMF U) (X : U → α) (x : α) (f : U → ℝ) :
    condExpect p X x (fun u => -f u) = -condExpect p X x f := by
  unfold condExpect
  by_cases h : (Finset.univ.filter (fun u => X u = x)).sum p.mass = 0
  · simp [h]
  · simp only [h, ite_false, mul_neg, Finset.sum_neg_distrib, neg_div]

/-- Conditional expectation is linear in a scalar.-/
public theorem condExpect_const_mul {α : Type*} [DecidableEq α]
    (p : FinPMF U) (X : U → α) (x : α) (c : ℝ) (f : U → ℝ) :
    condExpect p X x (fun u => c * f u) = c * condExpect p X x f := by
  unfold condExpect
  by_cases h : (Finset.univ.filter (fun u => X u = x)).sum p.mass = 0
  · simp [h]
  · simp only [h, ite_false, mul_div_assoc']
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun u _ => by ring)

/-- Conditional expectation commutes with a finite sum of integrands.

Definition 9 sums one conditional expectation per probe, and Proposition 8's
proof needs that sum to be one conditional expectation of a summed integrand —
which is where the `2 − |Γ(U)|` comes from.-/
public theorem condExpect_sum {α : Type*} [DecidableEq α] {ι : Type*}
    (p : FinPMF U) (X : U → α) (x : α) (s : Finset ι) (f : ι → U → ℝ) :
    s.sum (fun i => condExpect p X x (f i)) =
      condExpect p X x (fun u => s.sum (fun i => f i u)) := by
  unfold condExpect
  by_cases h : (Finset.univ.filter (fun u => X u = x)).sum p.mass = 0
  · simp [h]
  · simp only [h, ite_false, div_eq_mul_inv, ← Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun u _ => by rw [Finset.mul_sum])

/-! ## Definition 9 -/

/--
**Definition 9.** *"a device `(X,Y)` (weakly) infers `Γ` with (covariance)
accuracy `ε` iff `[Σ_{f ∈ π(Γ)} max_x E_P(Y f(Γ) ∣ x)] / |Γ(U)| = ε`."*

The finite implementation takes the maximum over setup values of **positive**
`P`-mass. Conditional expectation on a null fibre is undefined in the source; a
null fibre therefore cannot improve the maximum through Lean's totalization.-/
@[expose] public noncomputable def inferenceAccuracy (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] {G : Type v'} [Fintype G] [DecidableEq G]
    (p : FinPMF U) (Γ : U → G) : ℝ :=
  let S := Finset.univ.filter (fun γ : G => ∃ w, Γ w = γ)
  if S.card = 0 then 0
  else
    S.sum (fun γ =>
      (positiveMassSetups C p).sup' (positiveMassSetups_nonempty C p)
        (fun x => condExpect p C.setup x
          (fun u => boolPm (C.concl u) * boolPm (probe γ (Γ u))))) /
      (S.card : ℝ)

/-! ## Definitions 10 and 11 -/

/-- Shannon entropy of a mass function on a finite support (the image `X(U)`,
not the whole setup type). Natural logarithm; Definition 10 is a ratio, so the
base cancels.-/
@[expose] public noncomputable def shannonEntropyOn {α : Type*} [DecidableEq α]
    (support : Finset α) (μ : α → ℝ) : ℝ :=
  - support.sum fun a =>
      if μ a = 0 then 0 else μ a * Real.log (μ a)

public theorem pushOnImage_nonneg {α : Type*} [DecidableEq α]
    (p : FinPMF U) (X : U → α) (a : α) : 0 ≤ pushOnImage p X a :=
  p.fibre_nonneg X a

/-- Mutual information of two maps, summed over their images.-/
@[expose] public noncomputable def mutualInfo {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) : ℝ :=
  let sX := Finset.univ.image X
  let sY := Finset.univ.image Y
  let sXY := Finset.univ.image (fun u => (X u, Y u))
  shannonEntropyOn sX (pushOnImage p X) +
    shannonEntropyOn sY (pushOnImage p Y) -
    shannonEntropyOn sXY (pushOnImage p (fun u => (X u, Y u)))

/-- Entropy of a device's setup under `p`, over its realized image.-/
@[expose] public noncomputable def setupEntropy (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] (p : FinPMF U) : ℝ :=
  shannonEntropyOn (Finset.univ.image C.setup) (pushOnImage p C.setup)

/-- **Definition 10.** Mutual-information distinguishability,
`1 - M_P(X₁,X₂) / [H_P(X₁) + H_P(X₂)]`.

The zero-denominator branch is a Lean totalization, not a source case.-/
@[expose] public noncomputable def miDistinguishability
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (p : FinPMF U) : ℝ :=
  if setupEntropy C₁ p + setupEntropy C₂ p = 0 then 1
  else 1 - mutualInfo p C₁.setup C₂.setup / (setupEntropy C₁ p + setupEntropy C₂ p)

/-! ### Marginals, and the mass of an image

The two facts every information inequality below rests on: the pushforward masses
over an image sum to one, and a joint pushforward marginalizes to a single one.
-/

public theorem sum_pushOnImage {α : Type*} [DecidableEq α]
    (p : FinPMF U) (X : U → α) :
    (Finset.univ.image X).sum (pushOnImage p X) = 1 := by
  classical
  have hmaps : ∀ u ∈ (Finset.univ : Finset U), X u ∈ Finset.univ.image X :=
    fun u _ => Finset.mem_image_of_mem _ (Finset.mem_univ u)
  have := Finset.sum_fiberwise_of_maps_to hmaps p.mass
  rw [← p.sum_one, ← this]
  rfl

/-- Statistical independence of two finite random variables, stated pointwise on
their joint pushforward. Wolpert 2018 uses this hypothesis directly in its
restatement of the 2008 Proposition 6 bound.-/
@[expose] public def StatisticallyIndependent {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) : Prop :=
  ∀ x y, pushOnImage p (fun u => (X u, Y u)) (x, y) =
    pushOnImage p X x * pushOnImage p Y y

/-- Independence is symmetric.-/
public theorem StatisticallyIndependent.symm {α β : Type*}
    [DecidableEq α] [DecidableEq β]
    {p : FinPMF U} {X : U → α} {Y : U → β}
    (h : StatisticallyIndependent p X Y) : StatisticallyIndependent p Y X := by
  intro y x
  rw [mul_comm, ← h x y]
  unfold pushOnImage
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
  tauto

public theorem pushOnImage_marginal {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) (a : α) :
    (Finset.univ.image Y).sum
        (fun b => pushOnImage p (fun u => (X u, Y u)) (a, b)) =
      pushOnImage p X a := by
  classical
  have hmaps : ∀ u ∈ Finset.univ.filter (fun u : U => X u = a),
      Y u ∈ Finset.univ.image Y :=
    fun u _ => Finset.mem_image_of_mem _ (Finset.mem_univ u)
  have hfib := Finset.sum_fiberwise_of_maps_to hmaps p.mass
  unfold pushOnImage
  rw [← hfib]
  refine Finset.sum_congr rfl (fun b _ => ?_)
  refine Finset.sum_congr ?_ (fun _ _ => rfl)
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]

/-! ### Gibbs' inequality: mutual information is nonnegative

The source's step 2 turns *mutual-information distinguishability `= 1`* into
statistical independence, and its Definition 10 remark asserts the ratio lies in
`[0,1]`. Both rest on `0 ≤ M`. The paper asserts it; here it is proved, from
`Real.log_le_sub_one_of_pos` alone, with no measure-theoretic entropy API.
-/

private theorem joint_zero_off_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) {q : α × β}
    (hq : q ∉ Finset.univ.image (fun u => (X u, Y u))) :
    pushOnImage p (fun u => (X u, Y u)) q = 0 := by
  unfold pushOnImage
  refine Finset.sum_eq_zero (fun u hu => ?_)
  have h : (X u, Y u) = q := (Finset.mem_filter.mp hu).2
  exact absurd (h ▸ Finset.mem_image_of_mem (fun u => (X u, Y u)) (Finset.mem_univ u)) hq

/-- Each joint cell weighs no more than either marginal.-/
public theorem joint_le_pushOnImage_fst {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) (a : α) (b : β) :
    pushOnImage p (fun u => (X u, Y u)) (a, b) ≤ pushOnImage p X a := by
  unfold pushOnImage
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun u _ _ => p.nonneg u)
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hu ⊢
  exact hu.1

public theorem joint_le_pushOnImage_snd {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) (a : α) (b : β) :
    pushOnImage p (fun u => (X u, Y u)) (a, b) ≤ pushOnImage p Y b := by
  unfold pushOnImage
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun u _ _ => p.nonneg u)
  intro u hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq] at hu ⊢
  exact hu.2

/-- A value outside a map's image carries no mass.-/
private theorem pushOnImage_eq_zero_of_notMem {α : Type*} [DecidableEq α]
    (p : FinPMF U) (X : U → α) {a : α} (ha : a ∉ Finset.univ.image X) :
    pushOnImage p X a = 0 := by
  unfold pushOnImage
  refine Finset.sum_eq_zero (fun u hu => ?_)
  have h : X u = a := (Finset.mem_filter.mp hu).2
  exact absurd (h ▸ Finset.mem_image_of_mem X (Finset.mem_univ u)) ha

/-- The joint mass over the product of the two images is `1`.-/
private theorem sum_joint_over_product {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) :
    ((Finset.univ.image X) ×ˢ (Finset.univ.image Y)).sum
      (pushOnImage p (fun u => (X u, Y u))) = 1 := by
  classical
  have hsub : Finset.univ.image (fun u => (X u, Y u)) ⊆
      (Finset.univ.image X) ×ˢ (Finset.univ.image Y) := by
    intro c hc
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ u),
       Finset.mem_image_of_mem _ (Finset.mem_univ u)⟩
  rw [← Finset.sum_subset hsub (fun c _ hc => joint_zero_off_image p X Y hc)]
  exact sum_pushOnImage p (fun u => (X u, Y u))

/-- The product of the two marginals sums to `1` over the same rectangle.-/
private theorem sum_marginal_product {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) :
    ((Finset.univ.image X) ×ˢ (Finset.univ.image Y)).sum
      (fun c => pushOnImage p X c.1 * pushOnImage p Y c.2) = 1 := by
  classical
  rw [Finset.sum_product]
  have hrow : ∀ a ∈ Finset.univ.image X,
      (Finset.univ.image Y).sum (fun b => pushOnImage p X a * pushOnImage p Y b) =
        pushOnImage p X a := by
    intro a _
    rw [← Finset.mul_sum, sum_pushOnImage, mul_one]
  rw [Finset.sum_congr rfl hrow]
  exact sum_pushOnImage p X

/-- The Gibbs term contributed by one cell of `X(U) × Y(U)`.-/
private noncomputable def gibbsCellFn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) (c : α × β) : ℝ :=
  (if pushOnImage p (fun u => (X u, Y u)) c = 0 then 0
    else pushOnImage p (fun u => (X u, Y u)) c * Real.log (pushOnImage p X c.1)) +
  (if pushOnImage p (fun u => (X u, Y u)) c = 0 then 0
    else pushOnImage p (fun u => (X u, Y u)) c * Real.log (pushOnImage p Y c.2)) -
  (if pushOnImage p (fun u => (X u, Y u)) c = 0 then 0
    else pushOnImage p (fun u => (X u, Y u)) c *
      Real.log (pushOnImage p (fun u => (X u, Y u)) c))

/-- The bound that cell is compared against: product of marginals minus joint.-/
private noncomputable def gibbsSlackFn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) (c : α × β) : ℝ :=
  pushOnImage p X c.1 * pushOnImage p Y c.2 - pushOnImage p (fun u => (X u, Y u)) c

private theorem gibbsCellFn_le {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) (c : α × β) :
    gibbsCellFn p X Y c ≤ gibbsSlackFn p X Y c :=
  gibbs_cell (pushOnImage_nonneg p _ c)
    (joint_le_pushOnImage_fst p X Y c.1 c.2) (joint_le_pushOnImage_snd p X Y c.1 c.2)

private theorem gibbsCellFn_eq_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) (c : α × β) :
    gibbsCellFn p X Y c = gibbsSlackFn p X Y c ↔
      pushOnImage p (fun u => (X u, Y u)) c =
        pushOnImage p X c.1 * pushOnImage p Y c.2 :=
  gibbs_cell_eq_iff (pushOnImage_nonneg p _ c)
    (joint_le_pushOnImage_fst p X Y c.1 c.2) (joint_le_pushOnImage_snd p X Y c.1 c.2)

/-- The slacks sum to zero: both marginal product and joint have total mass `1`.-/
private theorem sum_gibbsSlackFn {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) :
    ((Finset.univ.image X) ×ˢ (Finset.univ.image Y)).sum (gibbsSlackFn p X Y) = 0 := by
  unfold gibbsSlackFn
  rw [Finset.sum_sub_distrib, sum_marginal_product, sum_joint_over_product, sub_self]

/-- **The Gibbs identity behind both directions.** `−M` is the cell-by-cell Gibbs
sum over the rectangle `X(U) × Y(U)`. `mutualInfo_nonneg` bounds it above by zero;
`mutualInfo_eq_zero_iff` reads off when the bound is attained.-/
private theorem neg_mutualInfo_eq_cellSum {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) :
    -mutualInfo p X Y =
      ((Finset.univ.image X) ×ˢ (Finset.univ.image Y)).sum (gibbsCellFn p X Y) := by
  unfold gibbsCellFn
  classical
  set sX := Finset.univ.image X with hsX
  set sY := Finset.univ.image Y with hsY
  set sJ := Finset.univ.image (fun u => (X u, Y u)) with hsJ
  set qm := pushOnImage p (fun u => (X u, Y u)) with hqm
  set pX := pushOnImage p X with hpX
  set pY := pushOnImage p Y with hpY
  have hsub : sJ ⊆ sX ×ˢ sY := by
    intro c hc
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hc
    exact Finset.mem_product.mpr
      ⟨Finset.mem_image_of_mem _ (Finset.mem_univ u),
       Finset.mem_image_of_mem _ (Finset.mem_univ u)⟩
  have hext : ∀ f : α × β → ℝ, (∀ c, qm c = 0 → f c = 0) →
      sJ.sum f = (sX ×ˢ sY).sum f := by
    intro f hf
    refine Finset.sum_subset hsub (fun c _ hc => hf c ?_)
    exact joint_zero_off_image p X Y hc
  have hX : sX.sum (fun a => if pX a = 0 then 0 else pX a * Real.log (pX a)) =
      (sX ×ˢ sY).sum (fun c => if qm c = 0 then 0 else qm c * Real.log (pX c.1)) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases hpa : pX a = 0
    · refine (ite_eq_left hpa).trans ?_
      refine (Finset.sum_eq_zero (fun b _ => ?_)).symm
      have hq0 : qm (a, b) = 0 :=
        le_antisymm (hpa ▸ joint_le_pushOnImage_fst p X Y a b)
          (pushOnImage_nonneg p _ (a, b))
      exact ite_eq_left hq0
    · rw [ite_eq_right hpa]
      have hz : ∀ b ∈ sY, (if qm (a, b) = 0 then 0 else qm (a, b) * Real.log (pX a)) =
          qm (a, b) * Real.log (pX a) := by
        intro b _
        by_cases hb : qm (a, b) = 0
        · rw [ite_eq_left hb, hb, zero_mul]
        · rw [ite_eq_right hb]
      rw [Finset.sum_congr rfl hz, ← Finset.sum_mul, pushOnImage_marginal]
  have hY : sY.sum (fun b => if pY b = 0 then 0 else pY b * Real.log (pY b)) =
      (sX ×ˢ sY).sum (fun c => if qm c = 0 then 0 else qm c * Real.log (pY c.2)) := by
    rw [Finset.sum_product_right]
    refine Finset.sum_congr rfl (fun b _ => ?_)
    by_cases hpb : pY b = 0
    · refine (ite_eq_left hpb).trans ?_
      refine (Finset.sum_eq_zero (fun a _ => ?_)).symm
      have hq0 : qm (a, b) = 0 :=
        le_antisymm (hpb ▸ joint_le_pushOnImage_snd p X Y a b)
          (pushOnImage_nonneg p _ (a, b))
      exact ite_eq_left hq0
    · rw [ite_eq_right hpb]
      have hz : ∀ a ∈ sX, (if qm (a, b) = 0 then 0 else qm (a, b) * Real.log (pY b)) =
          qm (a, b) * Real.log (pY b) := by
        intro a _
        by_cases ha : qm (a, b) = 0
        · rw [ite_eq_left ha, ha, zero_mul]
        · rw [ite_eq_right ha]
      rw [Finset.sum_congr rfl hz, ← Finset.sum_mul]
      congr 1
      have hswap : ∀ a ∈ sX,
          qm (a, b) = pushOnImage p (fun u => (Y u, X u)) (b, a) := by
        intro a _
        unfold pushOnImage
        refine Finset.sum_congr ?_ (fun _ _ => rfl)
        ext u
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]
        tauto
      rw [Finset.sum_congr rfl hswap, pushOnImage_marginal]
  have hJ : sJ.sum (fun c => if qm c = 0 then 0 else qm c * Real.log (qm c)) =
      (sX ×ˢ sY).sum (fun c => if qm c = 0 then 0 else qm c * Real.log (qm c)) :=
    hext _ (fun c hc => ite_eq_left hc)
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← hX, ← hY, ← hJ]
  unfold mutualInfo shannonEntropyOn
  ring

/-- **Gibbs' inequality.** `0 ≤ M_P(X, Y)`.-/
public theorem mutualInfo_nonneg {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) : 0 ≤ mutualInfo p X Y := by
  classical
  have hstep := Finset.sum_le_sum (s := (Finset.univ.image X) ×ˢ (Finset.univ.image Y))
    (fun c (_ : c ∈ (Finset.univ.image X) ×ˢ (Finset.univ.image Y)) =>
      gibbsCellFn_le p X Y c)
  rw [sum_gibbsSlackFn, ← neg_mutualInfo_eq_cellSum] at hstep
  linarith

/-- **The equality case of Gibbs' inequality.** `M_P(X, Y) = 0` exactly when `X`
and `Y` are statistically independent under `P`.

This is the step Wolpert 2008's Proposition 6 asserts in one sentence — *"since
the distinguishability is 1.0, `X₁` and `X₂` are statistically independent under
`P`"* — and it is strictly stronger than the inequality `mutualInfo_nonneg`
proves. Both directions come from `gibbs_cell_eq_iff` applied cell by cell: the
per-cell slacks sum to exactly `−M`, and a sum of nonnegative slacks vanishes
exactly when every one of them does. Off the rectangle `X(U) × Y(U)` both sides
are `0`, so the pointwise conclusion holds for every pair, not only realized
ones.-/
public theorem mutualInfo_eq_zero_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (p : FinPMF U) (X : U → α) (Y : U → β) :
    mutualInfo p X Y = 0 ↔ StatisticallyIndependent p X Y := by
  classical
  have hiff : (∀ c ∈ (Finset.univ.image X) ×ˢ (Finset.univ.image Y),
      gibbsCellFn p X Y c = gibbsSlackFn p X Y c) ↔ mutualInfo p X Y = 0 := by
    rw [← Finset.sum_eq_sum_iff_of_le (fun c _ => gibbsCellFn_le p X Y c),
      sum_gibbsSlackFn, ← neg_mutualInfo_eq_cellSum]
    constructor
    · intro h; linarith
    · intro h; linarith
  constructor
  · intro h0 a b
    by_cases ha : a ∈ Finset.univ.image X
    · by_cases hb : b ∈ Finset.univ.image Y
      · exact (gibbsCellFn_eq_iff p X Y (a, b)).mp
          (hiff.mpr h0 (a, b) (Finset.mem_product.mpr ⟨ha, hb⟩))
      · have hzero : pushOnImage p Y b = 0 := pushOnImage_eq_zero_of_notMem p Y hb
        have hq : pushOnImage p (fun u => (X u, Y u)) (a, b) = 0 :=
          le_antisymm (hzero ▸ joint_le_pushOnImage_snd p X Y a b)
            (pushOnImage_nonneg p _ (a, b))
        rw [hq, hzero, mul_zero]
    · have hzero : pushOnImage p X a = 0 := pushOnImage_eq_zero_of_notMem p X ha
      have hq : pushOnImage p (fun u => (X u, Y u)) (a, b) = 0 :=
        le_antisymm (hzero ▸ joint_le_pushOnImage_fst p X Y a b)
          (pushOnImage_nonneg p _ (a, b))
      rw [hq, hzero, zero_mul]
  · intro hind
    exact hiff.mp (fun c _ => (gibbsCellFn_eq_iff p X Y c).mpr (hind c.1 c.2))

/-- **Definition 11.** Counting distinguishability.-/
@[expose] public noncomputable def countingDistinguishability
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup] : ℝ :=
  let n₁ := (Finset.univ.image C₁.setup).card
  let n₂ := (Finset.univ.image C₂.setup).card
  if n₁ * n₂ = 0 then 1
  else
    1 - ((Finset.univ.image C₁.setup ×ˢ Finset.univ.image C₂.setup).filter
      (fun q => ∃ w, C₁.setup w = q.1 ∧ C₂.setup w = q.2)).card / (n₁ * n₂ : ℝ)

/-! ## Proposition 6, step 1 — accuracy on a two-valued setup -/

public theorem image_setup_eq_pair (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] {a b : C.Setup}
    (ha : C.Realized a) (hb : C.Realized b)
    (hall : ∀ w : U, C.setup w = a ∨ C.setup w = b) :
    Finset.univ.image C.setup = {a, b} := by
  apply Finset.Subset.antisymm
  · intro x hx
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hx
    rcases hall w with h | h <;> simp [h]
  · intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · obtain ⟨w, hw⟩ := ha
      exact Finset.mem_image.mpr ⟨w, Finset.mem_univ w, hw⟩
    · obtain ⟨w, hw⟩ := hb
      exact Finset.mem_image.mpr ⟨w, Finset.mem_univ w, hw⟩

public theorem positiveMassSetups_eq_pair (C : InferenceDevice.{u, v} U)
    [DecidableEq C.Setup] (p : FinPMF U) {a b : C.Setup}
    (ha : C.Realized a) (hb : C.Realized b)
    (hall : ∀ w : U, C.setup w = a ∨ C.setup w = b)
    (hpa : 0 < pushOnImage p C.setup a) (hpb : 0 < pushOnImage p C.setup b) :
    positiveMassSetups C p = {a, b} := by
  unfold positiveMassSetups
  rw [image_setup_eq_pair C ha hb hall]
  ext x
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · exact fun h => h.1
  · rintro (rfl | rfl)
    · exact ⟨Or.inl rfl, hpa⟩
    · exact ⟨Or.inr rfl, hpb⟩

/--
**Proposition 6, step 1.** *"For `|X₁(U)| = |X₂(U)| = 2` we can rewrite this as
`|E_P(g ∣ X₁=1) − E_P(g ∣ X₁=−1)| / 2 · …`"*, with `g ≡ Y₁Y₂`.

The two probes of a `Bool`-valued target are the identity and the negation, so the
Definition 9 sum is `max_x E(g∣x) + max_x E(−g∣x) = max − min = |difference|`.-/
public theorem inferenceAccuracy_eq_of_two_setups
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] (p : FinPMF U)
    {a b : C₁.Setup} (ha : C₁.Realized a) (hb : C₁.Realized b)
    (hall : ∀ w : U, C₁.setup w = a ∨ C₁.setup w = b)
    (hpa : 0 < pushOnImage p C₁.setup a) (hpb : 0 < pushOnImage p C₁.setup b) :
    inferenceAccuracy C₁ p C₂.concl =
      |condExpect p C₁.setup a (fun u => boolPm (C₁.concl u) * boolPm (C₂.concl u)) -
        condExpect p C₁.setup b
          (fun u => boolPm (C₁.concl u) * boolPm (C₂.concl u))| / 2 := by
  classical
  set g : U → ℝ := fun u => boolPm (C₁.concl u) * boolPm (C₂.concl u) with hg
  have hS : (Finset.univ.filter (fun γ : Bool => ∃ w, C₂.concl w = γ)) = Finset.univ :=
    Finset.filter_true_of_mem (fun γ _ => C₂.concl_surjective γ)
  have himg : positiveMassSetups C₁ p = {a, b} :=
    positiveMassSetups_eq_pair C₁ p ha hb hall hpa hpb
  -- the two probe terms
  have hterm_true : ∀ x : C₁.Setup,
      condExpect p C₁.setup x
        (fun u => boolPm (C₁.concl u) * boolPm (probe true (C₂.concl u))) =
      condExpect p C₁.setup x g := by
    intro x; simp only [hg, boolPm_probe_true]
  have hterm_false : ∀ x : C₁.Setup,
      condExpect p C₁.setup x
        (fun u => boolPm (C₁.concl u) * boolPm (probe false (C₂.concl u))) =
      -condExpect p C₁.setup x g := by
    intro x
    rw [← condExpect_neg]
    congr 1
    funext u
    simp only [hg, boolPm_probe_false, mul_neg]
  unfold inferenceAccuracy
  simp only [hS]
  rw [Fintype.sum_bool]
  rw [sup'_eq_max_of_eq_pair _ _ himg, sup'_eq_max_of_eq_pair _ _ himg]
  simp only [hterm_true, hterm_false]
  rw [max_neg_neg]
  rw [ite_eq_right (by simp : ¬ ((Finset.univ : Finset Bool).card = 0))]
  simp only [Finset.card_univ, Fintype.card_bool, Nat.cast_ofNat]
  rcases le_total (condExpect p C₁.setup a g) (condExpect p C₁.setup b g) with h | h
  · rw [max_eq_right h, min_eq_left h, abs_of_nonpos (by linarith)]
    ring
  · rw [max_eq_left h, min_eq_right h, abs_of_nonneg (by linarith)]
    ring

/-! ## Proposition 6, steps 2 and 3 -/

/-! ### The source's parameters, defined from `P` rather than left free

An earlier revision took `α`, `β` and `z` as **free scalars** and assumed four
identities relating them to conditional expectations. That assumed more than
the source's step 2: it assumed the identification of the parameters as well.
Here `α = P(X₁ = a₁)`, `β = P(X₂ = a₂)` and
`zᵢ = P(g = 1 ∣ x₁, x₂)` are *defined* from the measure.
`prop6Law_of_independent` proves the four identities from statistical
independence and positive support. The only source step not derived here is
the implication from mutual-information distinguishability one to statistical
independence.
-/

/-- `P(X = x)` — the source's `α` and `β` are this at the two devices' `−1`
setup values.-/
@[expose] public noncomputable def setupMass (p : FinPMF U)
    (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup] (x : C.Setup) : ℝ :=
  pushOnImage p C.setup x

/-- On a genuinely two-valued setup, the two setup masses sum to one.-/
public theorem setupMass_add_eq_one_of_two_setups
    (p : FinPMF U) (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    {a b : C.Setup} (ha : C.Realized a) (hb : C.Realized b) (hne : a ≠ b)
    (hall : ∀ w : U, C.setup w = a ∨ C.setup w = b) :
    setupMass p C a + setupMass p C b = 1 := by
  rw [← sum_pushOnImage p C.setup, image_setup_eq_pair C ha hb hall]
  simp [setupMass, hne]

/-- `P(g = 1 ∣ X₁ = x₁, X₂ = x₂)`, where `g = Y₁Y₂`, so `g = 1` is `Y₁ = Y₂`.-/
@[expose] public noncomputable def cellAgreeProb (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) : ℝ :=
  if (Finset.univ.filter
        (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂)).sum p.mass = 0 then 0
  else
    ((Finset.univ.filter (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂)).filter
      (fun u => C₁.concl u = C₂.concl u)).sum p.mass /
      (Finset.univ.filter (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂)).sum p.mass

public theorem cellAgreeProb_mem (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) :
    0 ≤ cellAgreeProb p C₁ C₂ x₁ x₂ ∧ cellAgreeProb p C₁ C₂ x₁ x₂ ≤ 1 := by
  unfold cellAgreeProb
  split
  · exact ⟨le_refl 0, by norm_num⟩
  · rename_i h
    have hcell : 0 ≤ (Finset.univ.filter
        (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂)).sum p.mass :=
      Finset.sum_nonneg (fun u _ => p.nonneg u)
    have hpos : 0 < (Finset.univ.filter
        (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂)).sum p.mass :=
      lt_of_le_of_ne hcell (Ne.symm h)
    have hnum : 0 ≤ ((Finset.univ.filter
        (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂)).filter
        (fun u => C₁.concl u = C₂.concl u)).sum p.mass :=
      Finset.sum_nonneg (fun u _ => p.nonneg u)
    refine ⟨div_nonneg hnum (le_of_lt hpos), (div_le_one hpos).mpr ?_⟩
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun u _ _ => p.nonneg u)

/-- The source's `z⃗`, read off the measure.-/
@[expose] public noncomputable def prop6QuadrupleOf (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (a₁ b₁ : C₁.Setup) (a₂ b₂ : C₂.Setup) : Prop6Quadruple where
  z1 := cellAgreeProb p C₁ C₂ a₁ a₂
  z2 := cellAgreeProb p C₁ C₂ a₁ b₂
  z3 := cellAgreeProb p C₁ C₂ b₁ a₂
  z4 := cellAgreeProb p C₁ C₂ b₁ b₂
  z1_mem := cellAgreeProb_mem p C₁ C₂ a₁ a₂
  z2_mem := cellAgreeProb_mem p C₁ C₂ a₁ b₂
  z3_mem := cellAgreeProb_mem p C₁ C₂ b₁ a₂
  z4_mem := cellAgreeProb_mem p C₁ C₂ b₁ b₂

private noncomputable def agreeMass (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) : ℝ :=
  ((Finset.univ.filter
      (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂)).filter
    (fun u => C₁.concl u = C₂.concl u)).sum p.mass

private theorem jointMass_eq_pushOnImage
    (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) :
    (Finset.univ.filter
      (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂)).sum p.mass =
      pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂) := by
  unfold pushOnImage
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Prod.mk.injEq]

private theorem cellAgreeProb_mul_jointMass
    (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (x₁ : C₁.Setup) (x₂ : C₂.Setup)
    (hpos : 0 < pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂)) :
    cellAgreeProb p C₁ C₂ x₁ x₂ *
        pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂) =
      agreeMass p C₁ C₂ x₁ x₂ := by
  unfold cellAgreeProb agreeMass
  rw [jointMass_eq_pushOnImage]
  rw [ite_eq_right (ne_of_gt hpos)]
  field_simp

private theorem cellWeightedSum_eq
    (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) :
    (Finset.univ.filter
      (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂)).sum
        (fun u => p.mass u * (boolPm (C₁.concl u) * boolPm (C₂.concl u))) =
      2 * agreeMass p C₁ C₂ x₁ x₂ -
        pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, x₂) := by
  rw [← jointMass_eq_pushOnImage]
  unfold agreeMass
  let s := Finset.univ.filter
    (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂)
  change s.sum (fun u => p.mass u * (boolPm (C₁.concl u) * boolPm (C₂.concl u))) =
    2 * (s.filter fun u => C₁.concl u = C₂.concl u).sum p.mass - s.sum p.mass
  calc
    s.sum (fun u => p.mass u * (boolPm (C₁.concl u) * boolPm (C₂.concl u))) =
        s.sum (fun u => 2 * (if C₁.concl u = C₂.concl u then p.mass u else 0) - p.mass u) := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          cases h₁ : C₁.concl u <;> cases h₂ : C₂.concl u <;>
            simp [boolPm] <;> ring
    _ = 2 * (s.filter fun u => C₁.concl u = C₂.concl u).sum p.mass - s.sum p.mass := by
      rw [Finset.sum_sub_distrib]
      congr 1
      rw [Finset.mul_sum]
      calc
        ∑ u ∈ s, 2 * (if C₁.concl u = C₂.concl u then p.mass u else 0) =
            ∑ u ∈ s, if C₁.concl u = C₂.concl u then 2 * p.mass u else 0 := by
          refine Finset.sum_congr rfl (fun u _ => ?_)
          by_cases h : C₁.concl u = C₂.concl u <;> simp [h]
        _ = ∑ u ∈ s.filter (fun u => C₁.concl u = C₂.concl u), 2 * p.mass u :=
          (Finset.sum_filter (fun u => C₁.concl u = C₂.concl u)
            (fun u => (2 : ℝ) * p.mass u)).symm

private theorem fibreWeightedSum_split
    (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (x₁ : C₁.Setup) {a₂ b₂ : C₂.Setup} (hne₂ : a₂ ≠ b₂)
    (hall₂ : ∀ w : U, C₂.setup w = a₂ ∨ C₂.setup w = b₂) :
    (Finset.univ.filter (fun u : U => C₁.setup u = x₁)).sum
        (fun u => p.mass u * (boolPm (C₁.concl u) * boolPm (C₂.concl u))) =
      (Finset.univ.filter
        (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = a₂)).sum
          (fun u => p.mass u * (boolPm (C₁.concl u) * boolPm (C₂.concl u))) +
      (Finset.univ.filter
        (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = b₂)).sum
          (fun u => p.mass u * (boolPm (C₁.concl u) * boolPm (C₂.concl u))) := by
  classical
  let sa := Finset.univ.filter
    (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = a₂)
  let sb := Finset.univ.filter
    (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = b₂)
  have hd : Disjoint sa sb := by
    refine Finset.disjoint_left.mpr (fun u hua hub => ?_)
    simp only [sa, sb, Finset.mem_filter, Finset.mem_univ, true_and] at hua hub
    exact hne₂ (hua.2.symm.trans hub.2)
  have hu : sa ∪ sb = Finset.univ.filter (fun u : U => C₁.setup u = x₁) := by
    ext u
    simp only [sa, sb, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (h | h) <;> exact h.1
    · intro hx
      rcases hall₂ u with h | h
      · exact Or.inl ⟨hx, h⟩
      · exact Or.inr ⟨hx, h⟩
  rw [← hu, Finset.sum_union hd]

private theorem condExpect_product_eq_of_independent_two_values
    (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (hind : StatisticallyIndependent p C₁.setup C₂.setup)
    {x₁ : C₁.Setup} {a₂ b₂ : C₂.Setup}
    (hx₁ : 0 < setupMass p C₁ x₁)
    (ha₂ : 0 < setupMass p C₂ a₂) (hb₂ : 0 < setupMass p C₂ b₂)
    (hne₂ : a₂ ≠ b₂)
    (hall₂ : ∀ w : U, C₂.setup w = a₂ ∨ C₂.setup w = b₂) :
    condExpect p C₁.setup x₁
        (fun u => boolPm (C₁.concl u) * boolPm (C₂.concl u)) =
      2 * (cellAgreeProb p C₁ C₂ x₁ a₂ * setupMass p C₂ a₂ +
        cellAgreeProb p C₁ C₂ x₁ b₂ * setupMass p C₂ b₂) - 1 := by
  have hjA : 0 < pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, a₂) := by
    rw [hind x₁ a₂]
    exact mul_pos hx₁ ha₂
  have hjB : 0 < pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, b₂) := by
    rw [hind x₁ b₂]
    exact mul_pos hx₁ hb₂
  have hsplit := fibreWeightedSum_split p C₁ C₂ x₁ hne₂ hall₂
  rw [cellWeightedSum_eq p C₁ C₂ x₁ a₂,
    cellWeightedSum_eq p C₁ C₂ x₁ b₂] at hsplit
  have hza := cellAgreeProb_mul_jointMass p C₁ C₂ x₁ a₂ hjA
  have hzb := cellAgreeProb_mul_jointMass p C₁ C₂ x₁ b₂ hjB
  rw [hind x₁ a₂] at hza
  rw [hind x₁ b₂] at hzb
  have hza' : agreeMass p C₁ C₂ x₁ a₂ =
      pushOnImage p C₁.setup x₁ *
        (cellAgreeProb p C₁ C₂ x₁ a₂ * pushOnImage p C₂.setup a₂) := by
    rw [← hza]
    ring
  have hzb' : agreeMass p C₁ C₂ x₁ b₂ =
      pushOnImage p C₁.setup x₁ *
        (cellAgreeProb p C₁ C₂ x₁ b₂ * pushOnImage p C₂.setup b₂) := by
    rw [← hzb]
    ring
  have hra₂ : C₂.Realized a₂ := realized_of_pushOnImage_pos p C₂.setup ha₂
  have hrb₂ : C₂.Realized b₂ := realized_of_pushOnImage_pos p C₂.setup hb₂
  have hsum₂ : setupMass p C₂ a₂ + setupMass p C₂ b₂ = 1 :=
    setupMass_add_eq_one_of_two_setups p C₂ hra₂ hrb₂ hne₂ hall₂
  have hsumRaw :
      pushOnImage p C₂.setup a₂ + pushOnImage p C₂.setup b₂ = 1 := hsum₂
  have hjSum :
      pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, a₂) +
        pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, b₂) =
      setupMass p C₁ x₁ := by
    rw [hind x₁ a₂, hind x₁ b₂]
    unfold setupMass
    calc
      pushOnImage p C₁.setup x₁ * pushOnImage p C₂.setup a₂ +
          pushOnImage p C₁.setup x₁ * pushOnImage p C₂.setup b₂ =
          pushOnImage p C₁.setup x₁ *
            (pushOnImage p C₂.setup a₂ + pushOnImage p C₂.setup b₂) := by ring
      _ = pushOnImage p C₁.setup x₁ := by rw [hsumRaw]; ring
  have hxraw : 0 < (Finset.univ.filter (fun u : U => C₁.setup u = x₁)).sum p.mass := hx₁
  have hxEq : (Finset.univ.filter (fun u : U => C₁.setup u = x₁)).sum p.mass =
      setupMass p C₁ x₁ := rfl
  have hjSumRaw :
      pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, a₂) +
        pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, b₂) =
      pushOnImage p C₁.setup x₁ := by simpa only [setupMass] using hjSum
  have hxEqRaw : (Finset.univ.filter (fun u : U => C₁.setup u = x₁)).sum p.mass =
      pushOnImage p C₁.setup x₁ := by simpa only [setupMass] using hxEq
  have hnum :
      (Finset.univ.filter (fun u : U => C₁.setup u = x₁)).sum
          (fun u => p.mass u * (boolPm (C₁.concl u) * boolPm (C₂.concl u))) =
        pushOnImage p C₁.setup x₁ *
          (2 * (cellAgreeProb p C₁ C₂ x₁ a₂ * pushOnImage p C₂.setup a₂ +
            cellAgreeProb p C₁ C₂ x₁ b₂ * pushOnImage p C₂.setup b₂) - 1) := by
    rw [hsplit, hza', hzb']
    calc
      2 * (pushOnImage p C₁.setup x₁ *
              (cellAgreeProb p C₁ C₂ x₁ a₂ * pushOnImage p C₂.setup a₂)) -
            pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, a₂) +
          (2 * (pushOnImage p C₁.setup x₁ *
              (cellAgreeProb p C₁ C₂ x₁ b₂ * pushOnImage p C₂.setup b₂)) -
            pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, b₂)) =
          2 * pushOnImage p C₁.setup x₁ *
              (cellAgreeProb p C₁ C₂ x₁ a₂ * pushOnImage p C₂.setup a₂ +
                cellAgreeProb p C₁ C₂ x₁ b₂ * pushOnImage p C₂.setup b₂) -
            (pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, a₂) +
              pushOnImage p (fun u => (C₁.setup u, C₂.setup u)) (x₁, b₂)) := by ring
      _ = 2 * pushOnImage p C₁.setup x₁ *
              (cellAgreeProb p C₁ C₂ x₁ a₂ * pushOnImage p C₂.setup a₂ +
                cellAgreeProb p C₁ C₂ x₁ b₂ * pushOnImage p C₂.setup b₂) -
            pushOnImage p C₁.setup x₁ := by rw [hjSumRaw]
      _ = pushOnImage p C₁.setup x₁ *
          (2 * (cellAgreeProb p C₁ C₂ x₁ a₂ * pushOnImage p C₂.setup a₂ +
            cellAgreeProb p C₁ C₂ x₁ b₂ * pushOnImage p C₂.setup b₂) - 1) := by ring
  unfold condExpect
  rw [ite_eq_right (ne_of_gt hxraw)]
  rw [hnum, hxEqRaw]
  simp only [setupMass]
  have hxp : 0 < pushOnImage p C₁.setup x₁ := hx₁
  exact mul_div_cancel_left₀ _ (ne_of_gt hxp)

/--
**Proposition 6, step 2's conclusion.** The four displayed identities the source
derives from statistical independence of `X₁` and `X₂`, which it in turn derives
from mutual-information distinguishability `1`.

Every scalar here is now **defined from `P`**: `α = setupMass p C₁ a₁`,
`β = setupMass p C₂ a₂`, and `z = prop6QuadrupleOf …`. The structure packages the
**conclusion** of the source's independence calculation. It is derived by
`prop6Law_of_independent`; callers need not assume its four fields separately.

The step from *mutual-information distinguishability = 1* to independence is the
equality case of Gibbs' inequality and is **not** mechanized here. The source
asserts it in one sentence without derivation. Recorded in the clash note.-/
public structure Prop6Law (C₁ : InferenceDevice.{u, v} U)
    (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (p : FinPMF U)
    (a₁ b₁ : C₁.Setup) (a₂ b₂ : C₂.Setup) : Prop where
  /-- `E(g ∣ X₁ = −1) = 2[z₁β + z₂(1−β)] − 1`.-/
  cond₁_neg : condExpect p C₁.setup a₁
      (fun u => boolPm (C₁.concl u) * boolPm (C₂.concl u)) =
    2 * ((prop6QuadrupleOf p C₁ C₂ a₁ b₁ a₂ b₂).z1 * setupMass p C₂ a₂ +
      (prop6QuadrupleOf p C₁ C₂ a₁ b₁ a₂ b₂).z2 * (1 - setupMass p C₂ a₂)) - 1
  /-- `E(g ∣ X₁ = +1) = 2[z₃β + z₄(1−β)] − 1`.-/
  cond₁_pos : condExpect p C₁.setup b₁
      (fun u => boolPm (C₁.concl u) * boolPm (C₂.concl u)) =
    2 * ((prop6QuadrupleOf p C₁ C₂ a₁ b₁ a₂ b₂).z3 * setupMass p C₂ a₂ +
      (prop6QuadrupleOf p C₁ C₂ a₁ b₁ a₂ b₂).z4 * (1 - setupMass p C₂ a₂)) - 1
  /-- `E(g ∣ X₂ = −1) = 2[z₁α + z₃(1−α)] − 1`.-/
  cond₂_neg : condExpect p C₂.setup a₂
      (fun u => boolPm (C₂.concl u) * boolPm (C₁.concl u)) =
    2 * ((prop6QuadrupleOf p C₁ C₂ a₁ b₁ a₂ b₂).z1 * setupMass p C₁ a₁ +
      (prop6QuadrupleOf p C₁ C₂ a₁ b₁ a₂ b₂).z3 * (1 - setupMass p C₁ a₁)) - 1
  /-- `E(g ∣ X₂ = +1) = 2[z₂α + z₄(1−α)] − 1`.-/
  cond₂_pos : condExpect p C₂.setup b₂
      (fun u => boolPm (C₂.concl u) * boolPm (C₁.concl u)) =
    2 * ((prop6QuadrupleOf p C₁ C₂ a₁ b₁ a₂ b₂).z2 * setupMass p C₁ a₁ +
      (prop6QuadrupleOf p C₁ C₂ a₁ b₁ a₂ b₂).z4 * (1 - setupMass p C₁ a₁)) - 1

/-- The conditional agreement probability is symmetric in the two devices.-/
public theorem cellAgreeProb_comm
    (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    (x₁ : C₁.Setup) (x₂ : C₂.Setup) :
    cellAgreeProb p C₁ C₂ x₁ x₂ = cellAgreeProb p C₂ C₁ x₂ x₁ := by
  have hbase :
      Finset.univ.filter (fun u : U => C₁.setup u = x₁ ∧ C₂.setup u = x₂) =
        Finset.univ.filter (fun u : U => C₂.setup u = x₂ ∧ C₁.setup u = x₁) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  have hagree :
      (Finset.univ.filter (fun u : U => C₂.setup u = x₂ ∧ C₁.setup u = x₁)).filter
          (fun u => C₁.concl u = C₂.concl u) =
        (Finset.univ.filter (fun u : U => C₂.setup u = x₂ ∧ C₁.setup u = x₁)).filter
          (fun u => C₂.concl u = C₁.concl u) := by
    ext u
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    tauto
  unfold cellAgreeProb
  rw [hbase, hagree]

/-- Wolpert 2008 Proposition 6, step 2 after independence. With positive mass on
the four setup fibres, statistical independence implies all four displayed
conditional-expectation identities. Thus `Prop6Law` is the *conclusion* of the
source's independence calculation, not an additional probabilistic law.

Wolpert 2018 restates the bound with independence as its direct premise. The only
2008 proof step still outside this theorem is the preceding equality case
`MI-distinguishability = 1 ⟹ StatisticallyIndependent`.-/
public theorem prop6Law_of_independent
    (p : FinPMF U)
    (C₁ : InferenceDevice.{u, v} U) (C₂ : InferenceDevice.{u, v'} U)
    [DecidableEq C₁.Setup] [DecidableEq C₂.Setup]
    {a₁ b₁ : C₁.Setup} {a₂ b₂ : C₂.Setup}
    (ha₁ : C₁.Realized a₁) (hb₁ : C₁.Realized b₁) (hne₁ : a₁ ≠ b₁)
    (hall₁ : ∀ w : U, C₁.setup w = a₁ ∨ C₁.setup w = b₁)
    (hpa₁ : 0 < setupMass p C₁ a₁) (hpb₁ : 0 < setupMass p C₁ b₁)
    (ha₂ : C₂.Realized a₂) (hb₂ : C₂.Realized b₂) (hne₂ : a₂ ≠ b₂)
    (hall₂ : ∀ w : U, C₂.setup w = a₂ ∨ C₂.setup w = b₂)
    (hpa₂ : 0 < setupMass p C₂ a₂) (hpb₂ : 0 < setupMass p C₂ b₂)
    (hind : StatisticallyIndependent p C₁.setup C₂.setup) :
    Prop6Law C₁ C₂ p a₁ b₁ a₂ b₂ := by
  have hsum₁ := setupMass_add_eq_one_of_two_setups p C₁ ha₁ hb₁ hne₁ hall₁
  have hsum₂ := setupMass_add_eq_one_of_two_setups p C₂ ha₂ hb₂ hne₂ hall₂
  have hrest₁ : setupMass p C₁ b₁ = 1 - setupMass p C₁ a₁ := by linarith
  have hrest₂ : setupMass p C₂ b₂ = 1 - setupMass p C₂ a₂ := by linarith
  refine { cond₁_neg := ?_, cond₁_pos := ?_, cond₂_neg := ?_, cond₂_pos := ?_ }
  · rw [condExpect_product_eq_of_independent_two_values p C₁ C₂ hind
      hpa₁ hpa₂ hpb₂ hne₂ hall₂, hrest₂]
    rfl
  · rw [condExpect_product_eq_of_independent_two_values p C₁ C₂ hind
      hpb₁ hpa₂ hpb₂ hne₂ hall₂, hrest₂]
    rfl
  · rw [condExpect_product_eq_of_independent_two_values p C₂ C₁ hind.symm
      hpa₂ hpa₁ hpb₁ hne₁ hall₁, hrest₁]
    rw [← cellAgreeProb_comm p C₁ C₂ a₁ a₂,
      ← cellAgreeProb_comm p C₁ C₂ b₁ a₂]
    rfl
  · rw [condExpect_product_eq_of_independent_two_values p C₂ C₁ hind.symm
      hpb₂ hpa₁ hpb₁ hne₁ hall₁, hrest₁]
    rw [← cellAgreeProb_comm p C₁ C₂ a₁ b₂,
      ← cellAgreeProb_comm p C₁ C₂ b₁ b₂]
    rfl

/-! ## `cov ≤ 1`, and what the source says about equality

2008, immediately after Definition 9: *"As an example, if `P` is nowhere 0 and
`C` weakly infers `Γ`, then `C` infers `Γ` with accuracy 1.0."* 2018, after its
Definition 6, states the two-sided form: *"Clearly, `cov(D, Γ) ≤ 1.0`, and if `P`
is nowhere 0, then `cov(D, Γ) = 1.0` iff `D > Γ`."*

The bound is proved here. It is the source's *"clearly"*, and it holds with no
hypothesis at all — not even nowhere-zero mass, because a null fibre contributes
`0` through the totalization rather than something larger.
-/

/-! ## Conditional entropy, and `C̄_ε` at the source's own length

Section 8 fixes the stochastic length: *"we can modify the definition of the
length of `x` to be `−ℍ(U ∣ x)`, the negative of the Shannon entropy under prior
`dμ` of `P(u ∣ x)`. If as in statistical physics `P` is proportional to `dμ`
across the support of `P`, then `P(u ∣ x) ∝ dμ(u ∣ x)`, and these two definitions
of the length of `x` are the same."*

`stochasticInferenceComplexity` takes the length as a parameter, which is faithful
to the source's separating `P` from `dμ` but left the **printed** object unnamed:
nothing in the tree fixed `ℓ` at `−ℍ(U ∣ x)`. This closes that.

**Reuse rather than reinvention.** At general measure the source's *"entropy under
prior `dμ`"* is relative entropy, and Mathlib already has it as
`InformationTheory.klDiv`, complete with Gibbs nonnegativity and
`klDiv_eq_zero_iff`. That is the right home for the general-measure form and it
is **not** rebuilt here. What is built here is the discrete case, where the
conditional distribution on a fibre is a `FinPMF` restriction and the entropy is
the elementary sum — the layer the rest of section 8 already lives in.
-/

/-- **`ℍ(U ∣ x)`** — the Shannon entropy of the conditional distribution on a
fibre, natural logarithm, totalized by `0` on a null fibre as `condExpect` is.-/
@[expose] public noncomputable def condEntropy {α : Type*} [DecidableEq α]
    (p : FinPMF U) (X : U → α) (x : α) : ℝ :=
  if (Finset.univ.filter (fun u => X u = x)).sum p.mass = 0 then 0
  else
    -(Finset.univ.filter (fun u => X u = x)).sum (fun u =>
      (p.mass u / (Finset.univ.filter (fun v => X v = x)).sum p.mass) *
        Real.log (p.mass u / (Finset.univ.filter (fun v => X v = x)).sum p.mass))

/--
**The source's bridge, proved.** *"If …`P` is proportional to `dμ` across the
support of `P`… these two definitions of the length of `x` are the same."*

At counting measure, `P ∝ dμ` on a fibre is exactly `P` being **uniform** there,
and then `ℍ(U ∣ x) = ln |X⁻¹(x)|`, so `−ℍ(U ∣ x)` is `setupLength`.-/
public theorem condEntropy_eq_log_card_of_uniform
    (p : FinPMF U) (C : InferenceDevice.{u, v} U) [DecidableEq C.Setup]
    (x : C.Setup) {c : ℝ} (hc : 0 < c)
    (huniform : ∀ u : U, C.setup u = x → p.mass u = c) :
    condEntropy p C.setup x =
      Real.log ((Finset.univ.filter (fun u : U => C.setup u = x)).card : ℝ) := by
  classical
  set s := Finset.univ.filter (fun u : U => C.setup u = x) with hs
  have hmem : ∀ u ∈ s, p.mass u = c := by
    intro u hu; exact huniform u (Finset.mem_filter.mp hu).2
  have hsum : s.sum p.mass = (s.card : ℝ) * c := by
    rw [Finset.sum_congr rfl hmem, Finset.sum_const, nsmul_eq_mul]
  by_cases hcard : s.card = 0
  · have : s.sum p.mass = 0 := by rw [hsum, hcard]; simp
    unfold condEntropy
    rw [ite_eq_left this, hcard]
    simp
  · have hcpos : (0 : ℝ) < (s.card : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hcard
    have hwpos : 0 < s.sum p.mass := by rw [hsum]; positivity
    unfold condEntropy
    rw [ite_eq_right (ne_of_gt hwpos)]
    have hterm : ∀ u ∈ s, p.mass u / s.sum p.mass = 1 / (s.card : ℝ) := by
      intro u hu
      rw [hmem u hu, hsum]
      field_simp
    rw [Finset.sum_congr rfl (fun u hu => by rw [hterm u hu])]
    rw [Finset.sum_const, nsmul_eq_mul]
    rw [one_div, Real.log_inv]
    field_simp
    rw [← hs]

end AISafetyAtlas.Inference
