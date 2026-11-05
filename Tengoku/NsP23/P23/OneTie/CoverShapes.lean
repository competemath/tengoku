import Tengoku.NsP23.P23.OneTie.CoverGeometry
import Tengoku.NsP23.P23.OneTie.NonDominantRows
import Tengoku.NsP23.P23.OneTie.MixedCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 1: exact H5 cover shapes

Every family constructor below fixes an exact unordered root finset.  Hence
root relabelling is represented honestly by finset equality.  Mixed y/z
reflection is a separate wrapper using the frozen `swapYZFinset` map.
-/

namespace P23.OneTie

variable {a b c : ℕ} [NeZero a]

private theorem coverShape_a_pos : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)

private def optionSingleton {α : Type} [DecidableEq α] : Option α → Finset α
  | none => ∅
  | some x => {x}

/-- The set of all existing immediate variable predecessors of `T`.-/
def predecessorRootFinset (T : Normal a b c) : Finset (Normal a b c) :=
  optionSingleton (Normal.predecessor .x T) ∪
    optionSingleton (Normal.predecessor .y T) ∪
      optionSingleton (Normal.predecessor .z T)

private theorem mem_optionSingleton_iff {q : Normal a b c}
    {o : Option (Normal a b c)} :
    q ∈ optionSingleton o ↔ o = some q := by
  cases o with
  | none => simp [optionSingleton]
  | some r => simp [optionSingleton, eq_comm]

theorem mem_predecessorRootFinset_iff (T q : Normal a b c) :
    q ∈ predecessorRootFinset T ↔
      Normal.predecessor .x T = some q ∨
      Normal.predecessor .y T = some q ∨
      Normal.predecessor .z T = some q := by
  simp [predecessorRootFinset, mem_optionSingleton_iff]

/-- The roots formed by all existing immediate predecessors of `T` generate
exactly the proper-divisor downset of `T`.-/
theorem standardSet_predecessorRootFinset (T : Normal a b c)
    (hproper : ∀ q ∈ predecessorRootFinset T, ¬T ∣ q) :
    standardSet (predecessorRootFinset T) = Normal.divisorDownset T \ {T} := by
  have predDvd : ∀ {e : Direction} {q : Normal a b c},
      Normal.predecessor e T = some q → q ∣ T := by
    intro e q hpred
    exact ⟨e.generator,
      ((Normal.predecessor_eq_some_iff_mul e T q).1 hpred).symm⟩
  ext p
  constructor
  · intro hp
    rcases (mem_standardSet_iff _ _).1 hp with ⟨q, hq, hpq⟩
    rcases (mem_predecessorRootFinset_iff T q).1 hq with hpred | hpred | hpred
    all_goals
      have hqT : q ∣ T := predDvd hpred
      have hpT := dvd_trans hpq hqT
      refine ⟨hpT, ?_⟩
      intro hpEq
      subst p
      exact hproper q hq hpq
  · rintro ⟨hpT, hpne⟩
    rcases properDivisor_factors_through_predecessor hpT (by simpa using hpne) with
      ⟨e, q, hpred, hpq⟩
    apply (mem_standardSet_iff _ _).2
    refine ⟨q, (mem_predecessorRootFinset_iff T q).2 ?_, hpq⟩
    cases e <;> simp_all

/-- The type-three top-deletion shape, without any border count.-/
def IsTopDeletion (S : Finset (Normal a b c)) : Prop :=
  ∃ T, S.card = 3 ∧ S = predecessorRootFinset T ∧
    standardSet S = Normal.divisorDownset T \ {T}

/-- The pure fibre-product combinatorial shape, up to root permutation.-/
def IsPureFibreProduct (S : Finset (Normal a b c)) : Prop :=
  c = 0 ∧ ∃ k, 1 ≤ k ∧
    let Z : Normal a b c := ⟨0, 0, k, coverShape_a_pos⟩
    Z ∈ S ∧ ∀ R ∈ S, R ≠ Z → R.z = 0

/-! Exact two-root core finsets. -/

def m2Socles (ha : 2 ≤ a) (r u v : ℕ) (hr : r ≤ a - 2) :
    Finset (Normal a 1 1) :=
  {m2Core ha r u v hr, m2Partner ha r u v hr}

def m3Socles (v : ℕ) : Finset (Normal a b c) :=
  {m3KCore v, m3KPartner v}

def m4Socles (ha : 2 ≤ a) (u v : ℕ) : Finset (Normal a 1 1) :=
  {m4YCore ha u v, m4YPartner u v}

def m5Socles (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b c) :=
  {m5Core ha v, m5Partner v c}

def p3Socles (v : ℕ) : Finset (Normal a b 0) :=
  {(⟨0, b, v, coverShape_a_pos⟩ : Normal a b 0),
    (⟨0, b - 1, v + 1, coverShape_a_pos⟩ : Normal a b 0)}

def p4Socles (V : ℕ) : Finset (Normal a b 0) :=
  {(⟨0, b, 0, coverShape_a_pos⟩ : Normal a b 0),
    (⟨0, b - 1, V, coverShape_a_pos⟩ : Normal a b 0)}

def p5Socles (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b 0) :=
  {(⟨a - 1, 0, v, by omega⟩ : Normal a b 0),
    (⟨0, b, 0, coverShape_a_pos⟩ : Normal a b 0)}

def p6Socles (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b 0) :=
  {(⟨a - 1, 0, v, by omega⟩ : Normal a b 0),
    (⟨0, b, v - 1, coverShape_a_pos⟩ : Normal a b 0)}

/-- Direct H5 shapes. Each constructor fixes the exact root finset and its
human-source parameter hypotheses.-/
inductive BaseCoverShape {a : ℕ} [NeZero a] :
    {b c : ℕ} → Finset (Normal a b c) → Prop
  | topDeletion {b c : ℕ} {S : Finset (Normal a b c)}
      (h : IsTopDeletion S) : BaseCoverShape (b := b) (c := c) S
  | pureFibreProduct {b : ℕ} {S : Finset (Normal a b 0)}
      (h : IsPureFibreProduct S) : BaseCoverShape (b := b) (c := 0) S
  | m2 {r u v} (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
      (hr : r ≤ a - 2) : BaseCoverShape (b := 1) (c := 1) (m2Socles ha r u v hr)
  | m2K {r u v} (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
      (hr : r ≤ a - 2) : BaseCoverShape (b := 1) (c := 1) (m2KSocles ha r u v hr)
  | m2Z {r u v} (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
      (hr : r ≤ a - 2) : BaseCoverShape (b := 1) (c := 1) (m2ZSocles ha r u v hr)
  | m3 {b c v} (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
      (hv : c ≤ v) : BaseCoverShape (b := b) (c := c) (m3Socles (a := a) (b := b) (c := c) v)
  | m3K {b c v} (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
      (hv : c ≤ v) : BaseCoverShape (b := b) (c := c) (m3KSocles ha v)
  | m4 {u v} (ha : 2 ≤ a) (hu : 1 ≤ u) :
      BaseCoverShape (b := 1) (c := 1) (m4Socles ha u v)
  | m4Y {u v} (ha : 2 ≤ a) (hu : 1 ≤ u) :
      BaseCoverShape (b := 1) (c := 1) (m4YSocles ha u v)
  | m5 {b c v} (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
      (hv : 1 ≤ v) : BaseCoverShape (b := b) (c := c) (m5Socles (a := a) (b := b) (c := c) ha v)
  | m5Y {b c v} (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
      (hv : 1 ≤ v) : BaseCoverShape (b := b) (c := c) (m5YSocles ha v)
  | m5Z {b c v} (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
      (hv : 1 ≤ v) : BaseCoverShape (b := b) (c := c) (m5ZSocles ha v)
  | p3 {b v} (ha : 2 ≤ a) (hb : 2 ≤ b) :
      BaseCoverShape (b := b) (c := 0) (p3Socles (a := a) (b := b) v)
  | p4 {b V} (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
      BaseCoverShape (b := b) (c := 0) (p4Socles (a := a) (b := b) V)
  | p4Z {b V} (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
      BaseCoverShape (b := b) (c := 0) (p4ZSocles (a := a) (b := b) ha V)
  | p5 {b v} (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
      BaseCoverShape (b := b) (c := 0) (p5Socles (a := a) (b := b) ha v)
  | p5Z {b v} (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
      BaseCoverShape (b := b) (c := 0) (p5ZSocles (a := a) (b := b) ha v)
  | p6 {b v} (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
      BaseCoverShape (b := b) (c := 0) (p6Socles (a := a) (b := b) ha v)

/-- Direct or explicitly y/z-reflected H5 shape. Reflection is permitted only
when both mixed tie exponents are positive.-/
inductive CoverShape {a b c : ℕ} [NeZero a]
    (S : Finset (Normal a b c)) : Prop
  | direct (h : BaseCoverShape S) : CoverShape S
  | reflected (hb : 1 ≤ b) (hc : 1 ≤ c)
      (h : BaseCoverShape (swapYZFinset S)) : CoverShape S

/-- Direct type-three shapes retained after removing the two-root cores.-/
inductive TypeThreeBaseShape {a : ℕ} [NeZero a] :
    {b c : ℕ} → Finset (Normal a b c) → Prop
  | topDeletion {b c : ℕ} {S : Finset (Normal a b c)}
      (h : IsTopDeletion S) : TypeThreeBaseShape (b := b) (c := c) S
  | pureFibreProduct {b : ℕ} {S : Finset (Normal a b 0)}
      (h : IsPureFibreProduct S) : TypeThreeBaseShape (b := b) (c := 0) S
  | m2K {r u v} (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
      (hr : r ≤ a - 2) : TypeThreeBaseShape (b := 1) (c := 1) (m2KSocles ha r u v hr)
  | m2Z {r u v} (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
      (hr : r ≤ a - 2) : TypeThreeBaseShape (b := 1) (c := 1) (m2ZSocles ha r u v hr)
  | m3K {b c v} (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
      (hv : c ≤ v) : TypeThreeBaseShape (b := b) (c := c) (m3KSocles ha v)
  | m4Y {u v} (ha : 2 ≤ a) (hu : 1 ≤ u) :
      TypeThreeBaseShape (b := 1) (c := 1) (m4YSocles ha u v)
  | m5Y {b c v} (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
      (hv : 1 ≤ v) : TypeThreeBaseShape (b := b) (c := c) (m5YSocles ha v)
  | m5Z {b c v} (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
      (hv : 1 ≤ v) : TypeThreeBaseShape (b := b) (c := c) (m5ZSocles ha v)
  | p4Z {b V} (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
      TypeThreeBaseShape (b := b) (c := 0) (p4ZSocles (a := a) (b := b) ha V)
  | p5Z {b v} (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
      TypeThreeBaseShape (b := b) (c := 0) (p5ZSocles (a := a) (b := b) ha v)

inductive TypeThreeCoverShape {a b c : ℕ} [NeZero a]
    (S : Finset (Normal a b c)) : Prop
  | direct (h : TypeThreeBaseShape S) : TypeThreeCoverShape S
  | reflected (hb : 1 ≤ b) (hc : 1 ≤ c)
      (h : TypeThreeBaseShape (swapYZFinset S)) : TypeThreeCoverShape S

end P23.OneTie
