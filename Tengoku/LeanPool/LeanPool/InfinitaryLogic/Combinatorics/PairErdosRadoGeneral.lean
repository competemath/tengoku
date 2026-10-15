/-
Copyright (c) 2026 Cameron Freer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cameron Freer
-/
module

public import Tengoku

/-!
# Pair Erdős–Rado, parameterized by the color bound `κ`

The color-parameterized pair Erdős–Rado theorem: for any infinite cardinal `κ` and any
color type `C` with `#C ≤ κ`, every pair coloring `cR : (Fin 2 ↪o Source κ) → C` of the
source order `Source κ = (Order.succ (2 ^ κ)).ord.ToType` (the initial well-order of the
successor of `2 ^ κ`) admits a `(Order.succ κ).ord`-indexed strict-mono suborder on which
`cR` is constant. In partition-calculus notation: `(2 ^ κ)⁺ → (κ⁺)²_κ`.

This file develops the canonical partition tree and extracts a live node of length at least
`(Order.succ κ).ord`. The end-homogenization engine in
`EndHomogeneousErdosRado.lean` consumes that node.

## Structure

- **`CardinalHelpers`**: all cardinal arithmetic isolated — source cardinality,
  the level-count bound `#(β.ToType → C) ≤ 2 ^ κ` for `β < (succ κ).ord`, the
  counting-core product `succ κ * 2 ^ κ = 2 ^ κ`, and the subset order-iso lemma.
- **EHMR canonical partition tree**: nodes are
  recorded-color sequences `β.ToType → C`, reps are chosen minima of successor sets,
  the coverage `y`-path shows every source element is some node's chosen rep, counting
  forces a live node of length `≥ (succ κ).ord`.
- **Consumer interface**: `exists_live_node_ge`.
-/

@[expose] public section

universe u

namespace FirstOrder.Combinatorics.PairERGen

/-! ### Generic toolbox (no `κ`): `pairEmbed`, pigeonhole, embeddings, order isos -/

section Toolbox

/-- Pair embedding: from an ordered pair `a < b` in a linearly-ordered
type, produce the canonical `Fin 2 ↪o α`. -/
noncomputable def pairEmbed {α : Type*} [LinearOrder α]
    {a b : α} (h : a < b) : Fin 2 ↪o α :=
  OrderEmbedding.ofStrictMono ![a, b] (by
    intro p q hpq
    match p, q, hpq with
    | ⟨0, _⟩, ⟨1, _⟩, _ => simpa using h
    | ⟨0, _⟩, ⟨0, _⟩, hp => exact absurd hp (lt_irrefl _)
    | ⟨1, _⟩, ⟨1, _⟩, hp => exact absurd hp (lt_irrefl _)
    | ⟨1, _⟩, ⟨0, _⟩, hp =>
      have hval : (1 : ℕ) < 0 := hp
      exact absurd hval (by omega))

/-- Path-counting pigeonhole. A function out of a set of cardinality `≥ succ μ` into a
codomain of cardinality `≤ μ` (with `μ ≥ ℵ_0`) has some fiber of cardinality `≥ succ μ`.

Routes through `Cardinal.infinite_pigeonhole_card` with parameter `θ := succ μ`. The
regularity of `succ μ` (successor cardinals are regular) supplies the cofinality
hypothesis.
@isnad1 id=ex.3h4v.s6.97825dcd458a from=translated src=- shape=448bb839 vocab=3e2504c3
-/
theorem exists_large_fiber_of_small_codomain
    {α β : Type u} {μ : Cardinal.{u}}
    (hμ : Cardinal.aleph0 ≤ μ)
    (hα : Cardinal.mk α ≥ Order.succ μ)
    (hβ : Cardinal.mk β ≤ μ)
    (f : α → β) :
    ∃ b : β, Order.succ μ ≤ Cardinal.mk (f ⁻¹' {b}) := by
  have hReg : (Order.succ μ).IsRegular := Cardinal.isRegular_succ hμ
  have hθ_le_α : Order.succ μ ≤ Cardinal.mk α := hα
  have hθ_ge_aleph0 : Cardinal.aleph0 ≤ Order.succ μ :=
    hμ.trans (Order.le_succ μ)
  -- `#β ≤ μ < succ μ = (succ μ).ord.cof`.
  have hcof : Cardinal.mk β < (Order.succ μ).ord.cof := by
    rw [hReg.cof_ord]
    exact hβ.trans_lt (Order.lt_succ_of_le le_rfl)
  exact Cardinal.infinite_pigeonhole_card f (Order.succ μ)
    hθ_le_α hθ_ge_aleph0 hcof

/-- Project-local replacement for the deprecated `Ordinal.initialSegToType` (deprecated in
favor of `Ordinal.type_le_iff`, from which this is extracted): the initial segment
embedding of `α.ToType` into `β.ToType` from `α ≤ β`. -/
noncomputable def initialSegOfLe {α β : Ordinal.{u}} (h : α ≤ β) : α.ToType ≤i β.ToType := by
  apply Classical.choice (Ordinal.type_le_iff.mp _)
  rwa [Ordinal.type_toType, Ordinal.type_toType]

/-- A well-ordered source of cardinality at least `c` admits an order-embedding from the
initial-ordinal well-order of cardinality `c`. Used by the abstract-source wrapper
`pairErdosRado_general_of_large` to pull the coloring back to `Source κ`.
@isnad1 id=nonempty.1h2v.s6.9fdeafb4bfaf from=translated src=- shape=bdb9bc2f vocab=44b1042b
-/
theorem exists_ordToType_embedding_of_card_ge
    {I : Type} [LinearOrder I] [WellFoundedLT I]
    {c : Cardinal} (hI : Cardinal.mk I ≥ c) :
    Nonempty (c.ord.ToType ↪o I) := by
  -- `β := type (<_I) : Ordinal`.  `β.card = #I ≥ c`, hence `c.ord ≤ β`.
  set β : Ordinal := Ordinal.type (· < · : I → I → Prop) with hβ
  have hβ_card : β.card = Cardinal.mk I := Ordinal.card_type (· < ·)
  have hord_le : c.ord ≤ β := by
    rw [Cardinal.ord_le, hβ_card]; exact hI
  -- Initial-segment embedding `c.ord.ToType ≤i β.ToType`.
  have seg : c.ord.ToType ≤i β.ToType := initialSegOfLe hord_le
  -- `β.ToType` ≃o `I` via `type_toType β = β = type (<_I)`.
  have htype : @Ordinal.type β.ToType (· < ·) _ =
      @Ordinal.type I (· < ·) _ := by
    rw [Ordinal.type_toType]
  have hiso : Nonempty
      ((· < · : β.ToType → β.ToType → Prop) ≃r (· < · : I → I → Prop)) :=
    Ordinal.type_eq.mp htype
  obtain ⟨r⟩ := hiso
  exact ⟨seg.toOrderEmbedding.trans (OrderIso.ofRelIsoLT r).toOrderEmbedding⟩

/-- Composition of `initialSegOfLe` via `InitialSeg.eq` uniqueness on well-orders.
Two initial segments from `α.ToType` to `γ.ToType` (both well-ordered) agree
pointwise.  (Shared with `EndHomogER`, which previously carried a private copy.)
@isnad1 id=eq.2h4v.s8.8ee4a6eee6d8 from=translated src=- shape=a29dc44c vocab=d544ac78
-/
lemma initialSegOfLe_compose
    {α β γ : Ordinal.{0}} (h_αβ : α ≤ β) (h_βγ : β ≤ γ) (x : α.ToType) :
    haveI : IsWellOrder α.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    (initialSegOfLe h_βγ).toOrderEmbedding
        ((initialSegOfLe h_αβ).toOrderEmbedding x) =
      (initialSegOfLe (h_αβ.trans h_βγ)).toOrderEmbedding x := by
  have : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
  rw [InitialSeg.toOrderEmbedding_apply, InitialSeg.toOrderEmbedding_apply,
      InitialSeg.toOrderEmbedding_apply,
      ← InitialSeg.trans_apply (initialSegOfLe h_αβ)
        (initialSegOfLe h_βγ) x]
  exact ((initialSegOfLe h_αβ).trans
    (initialSegOfLe h_βγ)).eq
    (initialSegOfLe (h_αβ.trans h_βγ)) x

end Toolbox

/-! ### Cardinal helpers: all the `κ`-arithmetic the EHMR port consumes -/

section CardinalHelpers

/-- **Pair-ER source at color bound `κ`.** The initial ordinal of the regular successor
cardinal `succ (2 ^ κ)`, viewed as a linearly-ordered `Type`. All pair-Erdős–Rado
recursion happens inside `Source κ`; the specialization `κ = ℵ₀` recovers the legacy
`PairERSource` (since `2 ^ ℵ₀ = ℶ_1`). -/
abbrev Source (κ : Cardinal.{0}) : Type :=
  (Order.succ ((2 : Cardinal.{0}) ^ κ)).ord.ToType

/-- Cardinality of the source: `#(Source κ) = succ (2 ^ κ)`. -/
private lemma mk_source (κ : Cardinal.{0}) :
    Cardinal.mk (Source κ) = Order.succ ((2 : Cardinal.{0}) ^ κ) :=
  Cardinal.mk_ord_toType _

instance (κ : Cardinal.{0}) : Nonempty (Source κ) :=
  Ordinal.nonempty_toType_iff.mpr fun h =>
    Cardinal.succ_ne_zero _ (Cardinal.ord_eq_zero.mp h)

/-- `2 ^ κ ≠ 0` (needed for `power_le_power_left` monotonicity).
@isnad1 id=ne.0h1v.s4.a6c164535511 from=translated src=- shape=8c4189b2 vocab=50a2fb69
-/
lemma two_power_ne_zero (κ : Cardinal.{0}) : (2 : Cardinal.{0}) ^ κ ≠ 0 :=
  Cardinal.power_ne_zero κ two_ne_zero

/-- `succ κ ≤ 2 ^ κ` — Cantor plus successor minimality; holds for every `κ`.
@isnad1 id=le.0h1v.s4.6b0f8726abbb from=translated src=- shape=76b2d254 vocab=eb17e001
-/
lemma succ_le_two_power (κ : Cardinal.{0}) :
    Order.succ κ ≤ 2 ^ κ :=
  Order.succ_le_of_lt (Cardinal.cantor κ)

variable {κ : Cardinal.{0}}

/-- `ℵ_0 ≤ 2 ^ κ` for infinite `κ` (via Cantor). -/
private lemma aleph0_le_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ (2 : Cardinal.{0}) ^ κ :=
  hκ.trans (Cardinal.cantor κ).le

/-- `ℵ_0 ≤ succ (2 ^ κ)` for infinite `κ`.
@isnad1 id=le.1h1v.s5.cd7fe2cff703 from=translated src=- shape=f7613962 vocab=6402d9b3
-/
lemma aleph0_le_succ_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ Order.succ ((2 : Cardinal.{0}) ^ κ) :=
  (aleph0_le_two_power hκ).trans (Order.le_succ _)

/-- `ℵ_0 ≤ succ κ` for infinite `κ`. -/
private lemma aleph0_le_succ_self (hκ : Cardinal.aleph0 ≤ κ) :
    Cardinal.aleph0 ≤ Order.succ κ :=
  hκ.trans (Order.le_succ κ)

/-- Ordinals below `(succ κ).ord` have `ToType` of cardinality `≤ κ` (the generalization
of "ordinals below `ω_1` are countable").
@isnad1 id=le.1h2v.s4.e1d9080ac854 from=translated src=- shape=dcb07b76 vocab=a0b24c6c
-/
theorem toType_card_le_of_lt_succ_ord {α : Ordinal.{0}}
    (hα : α < (Order.succ κ).ord) :
    Cardinal.mk α.ToType ≤ κ := by
  rw [Cardinal.mk_toType]
  exact Order.lt_succ_iff.mp (Cardinal.lt_ord.mp hα)

/-- `(succ κ).ord` is closed under ordinal successor for infinite `κ` (it is a limit
ordinal, being the initial ordinal of an uncountable-cofinality cardinal).
@isnad1 id=lt.2h2v.s5.86336522d6f6 from=translated src=- shape=7168551f vocab=517e9858
-/
theorem succ_lt_ord_of_lt (hκ : Cardinal.aleph0 ≤ κ) {δ : Ordinal.{0}}
    (hδ : δ < (Order.succ κ).ord) :
    Order.succ δ < (Order.succ κ).ord :=
  (Cardinal.isSuccLimit_ord (aleph0_le_succ_self hκ)).succ_lt hδ

/-- **Counting-core product.** `succ κ * 2 ^ κ = 2 ^ κ` for infinite `κ`
(the generalization of `ℵ_1 * ℶ_1 = ℶ_1`).
@isnad1 id=eq.1h1v.s5.151fb2c8d2f0 from=translated src=- shape=58b3c59e vocab=a038a3c9
-/
theorem succ_mul_two_power (hκ : Cardinal.aleph0 ≤ κ) :
    Order.succ κ * (2 : Cardinal.{0}) ^ κ = 2 ^ κ := by
  rw [Cardinal.mul_eq_max (aleph0_le_succ_self hκ) (aleph0_le_two_power hκ)]
  exact max_eq_right (succ_le_two_power κ)

end CardinalHelpers

/-! ### EHMR canonical-tree skeleton

Nodes are recorded-color sequences `β.ToType → C` (Type 0, so the counting stays in
`Cardinal.{0}`); reps `s(h↾γ) = min S(h↾γ)` are derived by well-founded recursion on
length; live = nonempty successor set. -/

section TreeSkeleton

/-- A node at level `β`: the recorded colors at the positions `β.ToType`. The eventual
branch is a cofinal chain through these of length `< (succ κ).ord`. -/
abbrev EHMRNodeAt (C : Type) (β : Ordinal.{0}) : Type := β.ToType → C

/-- Restrict a node to a shorter length `δ ≤ β`, via the initial-segment embedding. -/
noncomputable def EHMRNodeAt.restrict {C : Type} {β : Ordinal.{0}} (h : EHMRNodeAt C β)
    {δ : Ordinal.{0}} (hδβ : δ ≤ β) : EHMRNodeAt C δ :=
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  haveI : IsWellOrder δ.ToType (· < ·) := isWellOrder_lt
  fun x => h ((initialSegOfLe hδβ).toOrderEmbedding x)

variable {κ : Cardinal.{0}} {C : Type}

/-- **[EHMR §14, Lemma 14.2 + |E| counting — coverage/counting engine]** If the
"used-up" sets `R i` cover `Source κ` and each is a subsingleton, then the node index
set has cardinality `≥ succ (2 ^ κ) = #(Source κ)`. This is the counting feeding the
branch-length theorem.
@isnad1 id=le.2h3v.s6.5ec4353582f8 from=translated src=- shape=600553de vocab=fa607875
-/
theorem ehmr_partitionTree_card_lower
    {ι : Type} (R : ι → Set (Source κ))
    (hcover : ∀ y : Source κ, ∃ i : ι, y ∈ R i)
    (hsub : ∀ i : ι, (R i).Subsingleton) :
    Order.succ ((2 : Cardinal.{0}) ^ κ) ≤ Cardinal.mk ι := by
  classical
  -- The choice function `y ↦ (some i with y ∈ R i)` is injective: subsingleton fibers.
  have hf : ∀ y : Source κ, y ∈ R (hcover y).choose := fun y => (hcover y).choose_spec
  have hinj : Function.Injective (fun y : Source κ => (hcover y).choose) := by
    intro y₁ y₂ h
    change (hcover y₁).choose = (hcover y₂).choose at h
    have h2 : y₂ ∈ R (hcover y₁).choose := by rw [h]; exact hf y₂
    exact hsub _ (hf y₁) h2
  calc Order.succ ((2 : Cardinal.{0}) ^ κ) = Cardinal.mk (Source κ) := (mk_source κ).symm
    _ ≤ Cardinal.mk ι := Cardinal.mk_le_of_injective hinj

/-- The successor set `S(h)`: points above all the reps respecting the recorded
colors. (`β.ToType`-indexed `validFiber` shape, with a plain-function `rep`.) -/
def ehmrFiber (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (rep : β.ToType → Source κ) (col : EHMRNodeAt C β) : Set (Source κ) :=
  { y | ∀ x : β.ToType, ∃ h : rep x < y, cR (pairEmbed h) = col x }

/-- **Chosen representative** `s(h) = min S(h)` — the `<`-least element of the successor
set (via `Source κ`'s well-order), by well-founded recursion on the node length: the rep
at position `x : β.ToType` is the chosen rep of the restriction to `typein x`. Junk
default on dead (empty-fiber) nodes. -/
noncomputable def ehmrChosen (cR : (Fin 2 ↪o Source κ) → C)
    (β : Ordinal.{0}) (h : EHMRNodeAt C β) : Source κ := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact
    if hne : (ehmrFiber cR
        (fun x => ehmrChosen cR (Ordinal.typein (· < ·) x)
          (h.restrict (le_of_lt (by
            have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
            rwa [Ordinal.type_toType] at hh)))) h).Nonempty then
      (wellFounded_lt : WellFounded (· < · : Source κ → Source κ → Prop)).min _ hne
    else
      Classical.arbitrary (Source κ)
termination_by β
decreasing_by
  all_goals
    have : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
    have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
    rwa [Ordinal.type_toType] at hh

/-- The reps along a node: the chosen rep of the restriction to each position. -/
noncomputable def ehmrRep (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) : β.ToType → Source κ := by
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact fun x => ehmrChosen cR (Ordinal.typein (· < ·) x)
    (h.restrict (le_of_lt (by
      have hh := Ordinal.typein_lt_type (· < · : β.ToType → β.ToType → Prop) x
      rwa [Ordinal.type_toType] at hh)))

/-- `S(h)` as a set, via `ehmrRep`. -/
def ehmrS (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}} (h : EHMRNodeAt C β) :
    Set (Source κ) := ehmrFiber cR (ehmrRep cR h) h

/-- A node is **live** iff its successor set is nonempty. -/
def ehmrLive (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) : Prop := (ehmrS cR h).Nonempty

/-- The used/remainder set `R(h)`: `{s(h)}` on live nodes, else `∅`. -/
noncomputable def ehmrR (cR : (Fin 2 ↪o Source κ) → C) {β : Ordinal.{0}}
    (h : EHMRNodeAt C β) : Set (Source κ) := by
  classical
  exact if ehmrLive cR h then {ehmrChosen cR β h} else ∅

end TreeSkeleton

/-! ### Coverage (EHMR Lemma 14.2) — the canonical `y`-path

Rather than build the `y`-path by transfinite recursion with an explicit limit step, we
define the whole path at once: `yNode cR y β` is the length-`β` node recording, at each
position `x`, the pair-color of `y` against the chosen rep of the path so far — or junk
(an arbitrary color) once that rep is no longer `< y`. Restriction-coherence then
becomes a lemma, and the stopping argument is pure well-foundedness. -/

section YPath

variable {κ : Cardinal.{0}} {C : Type} [Nonempty C]

/-- The chosen rep of the canonical `y`-path at level `γ`, defined by well-founded
recursion: it is the chosen min of the node whose recorded color at each position `x` is
`cR({yRep(typein x), y})` (or junk once that rep is `≥ y`). Because the recursion lands
in `Source κ` (non-dependent), restriction-coherence later needs only `congrArg`, not a
heterogeneous transport. -/
noncomputable def yRep (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ)
    (γ : Ordinal.{0}) : Source κ := by
  classical
  haveI : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
  exact ehmrChosen cR γ (fun x =>
    if hlt : yRep cR y (Ordinal.typein (· < ·) x) < y then cR (pairEmbed hlt)
    else Classical.arbitrary C)
termination_by γ
decreasing_by
  all_goals
    have : IsWellOrder γ.ToType (· < ·) := isWellOrder_lt
    exact lt_of_lt_of_eq (Ordinal.typein_lt_type _ _) (Ordinal.type_toType γ)

/-- The canonical `y`-path node of length `β` (a *plain* def over `yRep`): at position
`x` it records the pair-color of `y` against `yRep (typein x)` (junk once that rep is
`≥ y`). -/
noncomputable def yNode (cR : (Fin 2 ↪o Source κ) → C) (y : Source κ)
    (β : Ordinal.{0}) : EHMRNodeAt C β := by
  classical
  haveI : IsWellOrder β.ToType (· < ·) := isWellOrder_lt
  exact fun x =>
    if hlt : yRep cR y (Ordinal.typein (· < ·) x) < y then cR (pairEmbed hlt)
    else Classical.arbitrary C

end YPath

/-! ### End-homogeneity of live nodes (EHMR fact (8)) -/

section EndHomogeneity

variable {κ : Cardinal.{0}} {C : Type}

end EndHomogeneity

/-! ### Branch extraction from a high live node

EHMR Theorem 13.1 realized concretely: the `succ (2 ^ κ)`-many live nodes (coverage)
cannot all sit at levels `< (succ κ).ord` (each such level has `≤ 2 ^ κ` nodes, and
there are only `succ κ` of them), so some live node has length `≥ (succ κ).ord`;
reading it off at the first `(succ κ).ord` positions yields an `EHMRBranch`. -/

section BranchExtraction

variable {κ : Cardinal.{0}} {C : Type}

end BranchExtraction

end FirstOrder.Combinatorics.PairERGen
