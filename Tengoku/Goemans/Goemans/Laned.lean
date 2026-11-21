/-
Copyright (c) 2026 TJC L.P.
SPDX-License-Identifier: MIT
Author: A. Richard Caputo III.
AI assistance: GPT-5.6 Sol (formalization).
-/
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Finset.Card
import Tengoku.Seed.Data.Finset.Max
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Data.Fintype.EquivFin
import Tengoku.Seed.Data.Real.Basic
import Tengoku.Seed.Tactic.DeriveFintype
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Push
import Tengoku.Seed.Tactic.SplitIfs
import Tengoku.Goemans.Goemans.Chain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Laned instances and the packing characterization

This file formalizes Definition 7.1 and Lemma 7.2 of the paper. Between each
successive pair of stage vertices there is a nonempty finite set of parallel
lane arcs, and all lanes reconverge before the next stage. A routing therefore
chooses a lane independently at every stage traversed by every terminal.

The complete arc type also contains the private cheap and expensive exits.
`Admissible` is defined on routing loads over that complete type. It is not
defined in terms of packing. A `StagePacking` is a separate bin assignment at
one stage, and `exists_admissibleRouting_iff_forall_stageCanPack` proves the
two notions equivalent for a fixed set of cheap exit choices.

The numerical search and Conjecture D from Section 7 are not proof statements
and do not belong in this module.
-/

namespace Goemans
namespace Laned

/-- Complete arcs of a finite laned instance: parallel stage lanes and the
two private exits of every terminal.-/
inductive Arc (k m : ℕ) (lanes : Fin m → ℕ) : Type
  | lane (t : Fin m) (l : Fin (lanes t))
  | cheapExit (i : Fin k)
  | expensiveExit (i : Fin k)
  deriving DecidableEq, Fintype

private def arcEquiv (k m : ℕ) (lanes : Fin m → ℕ) :
    Arc k m lanes ≃ (Sigma fun t : Fin m => Fin (lanes t)) ⊕
      (Fin k ⊕ Fin k) where
  toFun
    | .lane t l => .inl ⟨t, l⟩
    | .cheapExit i => .inr (.inl i)
    | .expensiveExit i => .inr (.inr i)
  invFun
    | .inl ⟨t, l⟩ => .lane t l
    | .inr (.inl i) => .cheapExit i
    | .inr (.inr i) => .expensiveExit i
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with ⟨t, l⟩ | i | i <;> rfl

/-- A `k`-terminal, `m`-stage instance in the laned exit-cost model.

`f i` units of terminal `i` use its cheap exit in the fractional flow, and
`d i - f i` use its expensive exit. The aggregate fractional loads on the
parallel lanes at a stage are nonnegative and sum to the total fractional
mass that traverses that stage.-/
structure Instance (k m : ℕ) where
  /-- There is at least one terminal.-/
  terminal_nonempty : 0 < k
  /-- Number of parallel lanes at each stage.-/
  lanes : Fin m → ℕ
  /-- Every stage has at least one lane.-/
  lane_nonempty : ∀ t, 0 < lanes t
  /-- Positive terminal demands.-/
  d : Fin k → ℝ
  /-- Cheap-exit amounts in the fractional flow.-/
  f : Fin k → ℝ
  /-- Expensive exit positions.-/
  e : Fin k → Fin (m + 1)
  /-- Cheap exit positions.-/
  p : Fin k → Fin (m + 1)
  /-- Per-unit costs of the private expensive exits.-/
  c : Fin k → ℝ
  /-- Fractional aggregate load on a lane.-/
  laneX : (t : Fin m) → Fin (lanes t) → ℝ
  d_pos : ∀ i, 0 < d i
  f_nonneg : ∀ i, 0 ≤ f i
  f_le_d : ∀ i, f i ≤ d i
  e_lt_p : ∀ i, e i < p i
  c_nonneg : ∀ i, 0 ≤ c i
  laneX_nonneg : ∀ t l, 0 ≤ laneX t l
  laneX_sum : ∀ t,
    (∑ l, laneX t l) =
      ∑ i, ((if t.val < (p i).val then f i else 0) +
        (if t.val < (e i).val then d i - f i else 0))

namespace Instance

variable {k m : ℕ}
variable (I : Instance k m)

/-- The complete arc type belonging to `I`.-/
abbrev CompleteArc := Arc k m I.lanes

private theorem sum_arc (g : I.CompleteArc → ℝ) :
    (∑ a, g a) =
      (∑ t, ∑ l, g (.lane t l)) +
        ((∑ i, g (.cheapExit i)) + ∑ i, g (.expensiveExit i)) := by
  calc
    (∑ a, g a) =
        ∑ a : (Sigma fun t : Fin m => Fin (I.lanes t)) ⊕ (Fin k ⊕ Fin k),
          g ((arcEquiv k m I.lanes).symm a) :=
      Fintype.sum_equiv (arcEquiv k m I.lanes) g
        (fun a => g ((arcEquiv k m I.lanes).symm a)) (fun a => by simp)
    _ = (∑ t, ∑ l, g (.lane t l)) +
          ((∑ i, g (.cheapExit i)) + ∑ i, g (.expensiveExit i)) := by
      rw [Fintype.sum_sum_type, Fintype.sum_sigma, Fintype.sum_sum_type]
      rfl

/-- A concrete lane choice for every terminal at every stage. Choices made
after a terminal exits are ignored. Together with an exit-choice set, this is
exactly a family of paths because all lanes reconverge after each stage.-/
structure Routing where
  /-- The lane chosen by terminal `i` at stage `t`.-/
  lane : (t : Fin m) → Fin k → Fin (I.lanes t)

/-- The exit position selected by routing terminals in `S` cheaply and all
other terminals expensively.-/
def exitPos (S : Finset (Fin k)) (i : Fin k) : Fin (m + 1) :=
  if i ∈ S then I.p i else I.e i

/-- Terminal `i` traverses stage `t` under exit-choice set `S`. With zero-based
stage indices this is `t < p i` for a cheap exit and `t < e i` for an
expensive exit.-/
def Transits (S : Finset (Fin k)) (i : Fin k) (t : Fin m) : Prop :=
  t.val < (I.exitPos S i).val

instance decidableTransits (S : Finset (Fin k)) (i : Fin k) (t : Fin m) :
    Decidable (I.Transits S i t) :=
  by
    unfold Transits exitPos
    infer_instance

/-- Arc incidence of the path selected for terminal `i`. This is independent
of capacities and packing: a path uses the selected lane at each stage before
its chosen exit, followed by the corresponding private exit.-/
def UsesArc (S : Finset (Fin k)) (R : I.Routing) (i : Fin k) :
    I.CompleteArc → Prop
  | .lane t l => I.Transits S i t ∧ R.lane t i = l
  | .cheapExit j => i = j ∧ i ∈ S
  | .expensiveExit j => i = j ∧ i ∉ S

instance decidableUsesArc (S : Finset (Fin k)) (R : I.Routing) (i : Fin k)
    (a : I.CompleteArc) : Decidable (I.UsesArc S R i a) :=
  by
    cases a <;> unfold UsesArc <;> infer_instance

/-- Maximum terminal demand.-/
def dmax : ℝ :=
  Finset.univ.sup'
    ⟨⟨0, I.terminal_nonempty⟩, Finset.mem_univ _⟩ I.d

/-- Every demand is at most `dmax`.
@isnad1 id=le.0h4v.s4.c875fb35c645 from=translated src=- shape=eb4eea45 vocab=72770205
-/
theorem d_le_dmax (i : Fin k) : I.d i ≤ I.dmax :=
  Finset.le_sup' I.d (Finset.mem_univ i)

/-- The maximum demand is positive.
@isnad1 id=lt.0h3v.s4.01f87903d212 from=translated src=- shape=d11c6b12 vocab=9db7bc3f
-/
theorem dmax_pos : 0 < I.dmax := by
  let i : Fin k := ⟨0, I.terminal_nonempty⟩
  exact lt_of_lt_of_le (I.d_pos i) (I.d_le_dmax i)

/-- Aggregate unsplittable load on a complete arc, obtained from the
independently defined path-incidence relation.-/
def load (S : Finset (Fin k)) (R : I.Routing) (a : I.CompleteArc) : ℝ :=
  ∑ i, if I.UsesArc S R i a then I.d i else 0

/-- Fractional load on a complete arc.-/
def x : I.CompleteArc → ℝ
  | .lane t l => I.laneX t l
  | .cheapExit i => I.f i
  | .expensiveExit i => I.d i - I.f i

/-- Per-unit cost on a complete arc. Only private expensive exits carry cost.-/
def arcCost : I.CompleteArc → ℝ
  | .lane _ _ => 0
  | .cheapExit _ => 0
  | .expensiveExit i => I.c i

/-- Fractional cost in the exit-cost model.-/
def fractionalCost : ℝ :=
  ∑ i, I.c i * (I.d i - I.f i)

/-- Cost of routing exactly the terminals in `S` cheaply.-/
def routingCost (S : Finset (Fin k)) : ℝ :=
  ∑ i, if i ∈ S then 0 else I.c i * I.d i

/-- Every complete arc has nonnegative cost.
@isnad1 id=le.0h4v.s4.a5545ac90553 from=translated src=- shape=d337d439 vocab=b0b8a08c
-/
theorem arcCost_nonneg (a : I.CompleteArc) : 0 ≤ I.arcCost a := by
  cases a with
  | lane _ _ => simp [arcCost]
  | cheapExit _ => simp [arcCost]
  | expensiveExit i => simpa [arcCost] using I.c_nonneg i

/-- The shorthand fractional cost is exactly the cost obtained by summing
`arcCost * x` over the complete arc type.
@isnad1 id=eq.0h3v.s5.c781c73e2b45 from=translated src=- shape=70e7ae25 vocab=ea89910f
-/
theorem fractionalCost_eq_sum_arc :
    I.fractionalCost = ∑ a, I.arcCost a * I.x a := by
  rw [sum_arc]
  simp [fractionalCost, arcCost, x]

/-- Full-graph Dinitz--Garg--Goemans admissibility.-/
def Admissible (S : Finset (Fin k)) (R : I.Routing) : Prop :=
  ∀ a, I.load S R a ≤ I.x a + I.dmax

/-- The bin load induced by `R` on lane `l` of stage `t`.-/
def laneLoad (S : Finset (Fin k)) (R : I.Routing)
    (t : Fin m) (l : Fin (I.lanes t)) : ℝ :=
  ∑ i, if I.Transits S i t ∧ R.lane t i = l then I.d i else 0

/--
@isnad1 id=eq.0h7v.s5.32f319e9386a from=translated src=- shape=37753210 vocab=d9265569
-/
@[simp] theorem load_lane (S : Finset (Fin k)) (R : I.Routing)
    (t : Fin m) (l : Fin (I.lanes t)) :
    I.load S R (.lane t l) = I.laneLoad S R t l := by
  rw [load, laneLoad]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : I.Transits S i t ∧ R.lane t i = l <;>
    simp [UsesArc, h]

/--
@isnad1 id=eq.0h6v.s6.70c969020683 from=translated src=- shape=7284f0be vocab=1edc56ec
-/
@[simp] theorem load_cheapExit (S : Finset (Fin k)) (R : I.Routing)
    (i : Fin k) :
    I.load S R (.cheapExit i) = if i ∈ S then I.d i else 0 := by
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    rw [load]
    calc
      (∑ j, if I.UsesArc S R j (.cheapExit i) then I.d j else 0) =
          (if I.UsesArc S R i (.cheapExit i) then I.d i else 0) := by
            apply Finset.sum_eq_single i
            · intro j _ hji
              simp [UsesArc, hji]
            · simp
      _ = I.d i := by simp [UsesArc, hi]
  · rw [ite_eq_right hi]
    rw [load]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i
    · subst j
      simp [UsesArc, hi]
    · simp [UsesArc, hji]

/--
@isnad1 id=eq.0h6v.s6.717862ccc0da from=translated src=- shape=61814a5d vocab=2660b5b3
-/
@[simp] theorem load_expensiveExit (S : Finset (Fin k)) (R : I.Routing)
    (i : Fin k) :
    I.load S R (.expensiveExit i) = if i ∈ S then 0 else I.d i := by
  by_cases hi : i ∈ S
  · rw [ite_eq_left hi]
    rw [load]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hji : j = i
    · subst j
      simp [UsesArc, hi]
    · simp [UsesArc, hji]
  · rw [ite_eq_right hi]
    rw [load]
    calc
      (∑ j, if I.UsesArc S R j (.expensiveExit i) then I.d j else 0) =
          (if I.UsesArc S R i (.expensiveExit i) then I.d i else 0) := by
            apply Finset.sum_eq_single i
            · intro j _ hji
              simp [UsesArc, hji]
            · simp
      _ = I.d i := by simp [UsesArc, hi]

/-- The shorthand routing cost is exactly the cost obtained by summing
`arcCost * load` over the complete arc type.
@isnad1 id=eq.0h5v.s6.223dbee6cf1e from=translated src=- shape=078d7347 vocab=0244b684
-/
theorem routingCost_eq_sum_arc
    (S : Finset (Fin k)) (R : I.Routing) :
    I.routingCost S = ∑ a, I.arcCost a * I.load S R a := by
  rw [sum_arc]
  simp [routingCost, arcCost]

/--
@isnad1 id=eq.0h5v.s5.f744199e5d96 from=translated src=- shape=9c6250fb vocab=5589b187
-/
@[simp] theorem x_lane (t : Fin m) (l : Fin (I.lanes t)) :
    I.x (.lane t l) = I.laneX t l :=
  rfl

/--
@isnad1 id=eq.0h4v.s4.c4dc91eca2ac from=translated src=- shape=beea4298 vocab=76cc9784
-/
@[simp] theorem x_cheapExit (i : Fin k) :
    I.x (.cheapExit i) = I.f i :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.57af603e0175 from=translated src=- shape=b93e147d vocab=14bca851
-/
@[simp] theorem x_expensiveExit (i : Fin k) :
    I.x (.expensiveExit i) = I.d i - I.f i :=
  rfl

/-- Fractional load is nonnegative on every complete arc.
@isnad1 id=le.0h4v.s4.4f180ddfedc7 from=translated src=- shape=d337d439 vocab=fe6e4256
-/
theorem x_nonneg (a : I.CompleteArc) : 0 ≤ I.x a := by
  cases a with
  | lane t l => exact I.laneX_nonneg t l
  | cheapExit i => exact I.f_nonneg i
  | expensiveExit i => exact sub_nonneg.mpr (I.f_le_d i)

/-- Routing load is nonnegative on every complete arc.
@isnad1 id=le.0h6v.s5.a5220f4ea3f5 from=translated src=- shape=fdbd8eda vocab=616bc116
-/
theorem load_nonneg (S : Finset (Fin k)) (R : I.Routing) (a : I.CompleteArc) :
    0 ≤ I.load S R a := by
  rw [load]
  exact Finset.sum_nonneg fun i _ => by
    split <;> simp [(I.d_pos i).le]

/-- Private cheap exits can never violate the capacity allowance.
@isnad1 id=le.0h6v.s5.1c5cc446d31b from=translated src=- shape=1a88c7de vocab=6848cbed
-/
theorem cheapExit_safe (S : Finset (Fin k)) (R : I.Routing) (i : Fin k) :
    I.load S R (.cheapExit i) ≤ I.x (.cheapExit i) + I.dmax := by
  rw [load_cheapExit, x_cheapExit]
  split_ifs
  · linarith [I.f_nonneg i, I.d_le_dmax i]
  · linarith [I.f_nonneg i, I.dmax_pos]

/-- Private expensive exits can never violate the capacity allowance.
@isnad1 id=le.0h6v.s5.fdc886b482e1 from=translated src=- shape=1a88c7de vocab=c15af345
-/
theorem expensiveExit_safe (S : Finset (Fin k)) (R : I.Routing) (i : Fin k) :
    I.load S R (.expensiveExit i) ≤ I.x (.expensiveExit i) + I.dmax := by
  rw [load_expensiveExit, x_expensiveExit]
  split_ifs
  · linarith [I.f_le_d i, I.dmax_pos]
  · linarith [I.f_le_d i, I.d_le_dmax i]

/-- Full admissibility is equivalent to the capacity inequalities on the
parallel lane arcs; private exits are automatically safe.
@isnad1 id=iff.0h5v.s5.66c74509a4dd from=translated src=- shape=b9e8e4f6 vocab=9bdb9464
-/
theorem admissible_iff_lanes (S : Finset (Fin k)) (R : I.Routing) :
    I.Admissible S R ↔
      ∀ t l, I.laneLoad S R t l ≤ I.laneX t l + I.dmax := by
  constructor
  · intro h t l
    simpa using h (.lane t l)
  · intro h a
    cases a with
    | lane t l => simpa using h t l
    | cheapExit i => exact I.cheapExit_safe S R i
    | expensiveExit i => exact I.expensiveExit_safe S R i

/-! ## Independent stage packings -/

/-- A packing of the demands that transit one stage into that stage's lanes.
This is a separate object from a routing.-/
structure StagePacking (S : Finset (Fin k)) (t : Fin m) where
  /-- Bin assigned to every terminal; assignments of nontransiting terminals
  are ignored.-/
  lane : Fin k → Fin (I.lanes t)
  /-- Every bin respects its fractional-load-plus-`dmax` capacity.-/
  capacity : ∀ l,
    (∑ i, if I.Transits S i t ∧ lane i = l then I.d i else 0) ≤
      I.laneX t l + I.dmax

/-- The transit demands at stage `t` can be packed into its lane capacities.-/
def StageCanPack (S : Finset (Fin k)) (t : Fin m) : Prop :=
  Nonempty (I.StagePacking S t)

/-- **Lemma 7.2 (packing characterization).** For a fixed cheap-exit set `S`,
an admissible unsplittable routing exists exactly when the transit demands can
be packed into capacities `laneX t l + dmax` independently at every stage.

The reverse implication uses the full-reconvergence property encoded by
`Routing`: stage assignments may be selected independently and concatenate
without a consistency condition.
@isnad1 id=iff.0h4v.s5.d8acfe21e153 from=translated src=- shape=b98c098f vocab=af3015af
-/
theorem exists_admissibleRouting_iff_forall_stageCanPack
    (S : Finset (Fin k)) :
    (∃ R : I.Routing, I.Admissible S R) ↔
      ∀ t, I.StageCanPack S t := by
  constructor
  · rintro ⟨R, hR⟩ t
    refine ⟨{ lane := R.lane t, capacity := ?_ }⟩
    intro l
    exact (I.admissible_iff_lanes S R).1 hR t l
  · intro hpack
    classical
    let P : ∀ t, I.StagePacking S t := fun t => Classical.choice (hpack t)
    let R : I.Routing := ⟨fun t => (P t).lane⟩
    refine ⟨R, (I.admissible_iff_lanes S R).2 ?_⟩
    intro t l
    exact (P t).capacity l

/-! ## Chains as the one-lane special case -/

/-- A chain is the special case of a laned instance with one lane at every
stage.-/
def ofChain [Nonempty (Fin k)] (C : Chain.Instance (Fin k) m) :
    Laned.Instance k m where
  terminal_nonempty := by
    rcases (inferInstance : Nonempty (Fin k)) with ⟨i⟩
    exact Nat.zero_lt_of_lt i.isLt
  lanes := fun _ => 1
  lane_nonempty := fun _ => by simp
  d := C.d
  f := C.f
  e := C.e
  p := C.p
  c := C.c
  laneX := fun t _ => C.stageX t
  d_pos := C.d_pos
  f_nonneg := C.f_nonneg
  f_le_d := C.f_le_d
  e_lt_p := C.e_lt_p
  c_nonneg := C.c_nonneg
  laneX_nonneg := fun t _ => by
    rw [Chain.Instance.stageX]
    exact Finset.sum_nonneg fun i _ => by
      split_ifs <;> linarith [C.f_nonneg i, C.f_le_d i]
  laneX_sum := fun t => by
    simp [Chain.Instance.stageX]

/--
@isnad1 id=eq.0h4v.s5.80483a1ed4f0 from=translated src=- shape=1cee4455 vocab=d7179f2b
-/
@[simp] theorem ofChain_lanes [Nonempty (Fin k)]
    (C : Chain.Instance (Fin k) m) (t : Fin m) :
    (ofChain C).lanes t = 1 :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.bbd7525c5e00 from=translated src=- shape=494a8e23 vocab=2f94a81d
-/
@[simp] theorem ofChain_laneX [Nonempty (Fin k)]
    (C : Chain.Instance (Fin k) m) (t : Fin m)
    (l : Fin ((ofChain C).lanes t)) :
    (ofChain C).laneX t l = C.stageX t :=
  rfl

/--
@isnad1 id=eq.0h3v.s4.fd8ce527f7f4 from=translated src=- shape=39b46a6a vocab=f7a4f831
-/
@[simp] theorem ofChain_dmax [Nonempty (Fin k)]
    (C : Chain.Instance (Fin k) m) :
    (ofChain C).dmax = C.dmax :=
  rfl

/--
@isnad1 id=eq.0h7v.s6.32e5bf57d0c7 from=translated src=- shape=b9d7f860 vocab=e8ef847f
-/
@[simp] theorem ofChain_laneLoad [Nonempty (Fin k)]
    (C : Chain.Instance (Fin k) m)
    (S : Finset (Fin k)) (R : (ofChain C).Routing)
    (t : Fin m) (l : Fin ((ofChain C).lanes t)) :
    (ofChain C).laneLoad S R t l = C.stageLoad S t := by
  rw [laneLoad, Chain.Instance.stageLoad]
  apply Finset.sum_congr rfl
  intro i _
  have hline : R.lane t i = l := by
    apply Fin.ext
    have hR := (R.lane t i).isLt
    change (R.lane t i).val < 1 at hR
    have hl := l.isLt
    change l.val < 1 at hl
    exact (Nat.lt_one_iff.mp hR).trans (Nat.lt_one_iff.mp hl).symm
  by_cases hi : i ∈ S
  · simp [Transits, exitPos, ofChain, hi, hline]
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)
  · simp [Transits, exitPos, ofChain, hi, hline]
    first
      | (all_goals grind; done)
      | (all_goals simp_all; done)
      | (all_goals aesop; done)
      | (all_goals omega; done)
      | (all_goals norm_num; done)
      | (all_goals positivity; done)
      | (all_goals linarith; done)
      | (all_goals decide; done)
      | (all_goals tauto; done)

/-! ## The unit-demand, one-stage specialization -/

variable {k : ℕ}
variable (I : Instance k 1)

/-- In the one-stage unit-demand specialization with expensive exits before
the stage and cheap exits after it, the terminals transiting the unique stage
are exactly the cheap-exit set.
@isnad1 id=iff.2h4v.s7.ddb1f95e05f4 from=translated src=- shape=ddd20e01 vocab=0bfa6d43
-/
theorem transits_zero_iff_mem
    (he : ∀ i, I.e i = (0 : Fin 2))
    (hp : ∀ i, I.p i = (1 : Fin 2))
    (S : Finset (Fin k)) (i : Fin k) :
    I.Transits S i (0 : Fin 1) ↔ i ∈ S := by
  by_cases hi : i ∈ S <;>
    simp [Transits, exitPos, he i, hp i, hi]

end Instance
end Laned
end Goemans
