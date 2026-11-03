import Tengoku.Seed.Data.Fintype.Powerset
import Tengoku.Seed.Tactic
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.ConvexGeometry.BottomLevels

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generic combinatorics for the first four levels

This file contains only generic finite deductions: the cardinality of the five
formal level-three shape families, finite joint-fiber stratification over a
possibly infinite ambient index type, minimal faithful-core consequences, and
the simultaneous induction pattern for the annihilator recurrence.

It does not classify module supports, construct Gabriel arrows or faithful
cores, or prove the manuscript’s bottom-three or bottom-four propositions.
-/

noncomputable section

namespace QuotientSubmoduleEquidistribution.BottomLevels

/-! ## Pure combinatorics of the five level-three families -/

namespace BottomThreeShape

variable {V E U : Type*}
  [Fintype V]
  [Fintype E]
  [Fintype U]

/-- The arrows with prescribed source.-/
abbrev OutFiber (source : E → V) (x : V) :=
  {e : E // source e = x}

/-- The arrows with prescribed target.-/
abbrev InFiber (target : E → V) (x : V) :=
  {e : E // target e = x}

/-- The cardinality of one source fiber.-/
def outDegree (source : E → V) (x : V) : ℕ :=
  Nat.card (OutFiber source x)

/-- The cardinality of one target fiber.-/
def inDegree (target : E → V) (x : V) : ℕ :=
  Nat.card (InFiber target x)

/--
The five purely formal families occurring in the proposed level-three
classification:

1. three vertices;
2. an edge and a further vertex different from its source;
3. two edges with a common source;
4. one element of the supplied fourth family `U`;
5. two edges with a common target.

No assertion is made here that actual quotient-closed supports are classified
by this type.-/
def Shape (source target : E → V) :=
  {s : Finset V // s.card = 3} ⊕
    (Σ e : E, {x : V // x ≠ source e}) ⊕
      (Σ x : V, {s : Finset (OutFiber source x) // s.card = 2}) ⊕
        U ⊕
          (Σ x : V, {s : Finset (InFiber target x) // s.card = 2})

/-- The numerical expression obtained by counting the five formal families.-/
def formula (source target : E → V) : ℕ :=
  Nat.choose (Fintype.card V) 3 +
    Fintype.card E * (Fintype.card V - 1) +
      (∑ x : V, Nat.choose (outDegree source x) 2) +
        Fintype.card U +
          ∑ x : V, Nat.choose (inDegree target x) 2

/-- The five formal families have the displayed cardinality.
@isnad1 id=eq.0h5v.s5.7c4c0963c4ed from=translated src=- shape=1f807722 vocab=bf367196
-/
theorem card (source target : E → V) :
    Nat.card (Shape (U := U) source target) =
      formula (U := U) source target := by
  classical
  simp [Shape, formula, Nat.card_eq_fintype_card,
    Fintype.card_finset_len, outDegree, inDegree]
  ac_rfl

/-- Swapping source and target leaves the formal counting expression fixed.
@isnad1 id=eq.0h5v.s5.fcd7f1f854a6 from=translated src=- shape=dc8cd711 vocab=a437480f
-/
theorem formula_swap (source target : E → V) :
    formula (U := U) source target =
      formula (U := U) target source := by
  unfold formula outDegree inDegree
  simp only [OutFiber, InFiber]
  ac_rfl

/-- The two source/target-swapped formal shape types have equal cardinality.
@isnad1 id=eq.0h5v.s5.8c6b2de7487a from=translated src=- shape=c984a071 vocab=e1e3d0db
-/
theorem card_swap (source target : E → V) :
    Nat.card (Shape (U := U) source target) =
      Nat.card (Shape (U := U) target source) := by
  rw [card, card, formula_swap]

end BottomThreeShape

/-! ## Minimal faithful cores inside an actual closure system -/

namespace MinimalFaithfulCore

open Set

variable {E : Type*} [Finite E]

/-- Faithful closed sets at one cardinality level.-/
def faithfulLevel
    (c : QuotientSubmoduleEquidistribution.SetClosure E)
    (Faithful : Set E → Prop) (n : ℕ) :
    Set c.Closeds :=
  {C | Faithful (C : Set E) ∧ (C : Set E).ncard = n}

/-- The number of faithful closed sets at one level.-/
def faithfulLevelCount
    (c : QuotientSubmoduleEquidistribution.SetClosure E)
    (Faithful : Set E → Prop) (n : ℕ) : ℕ :=
  (faithfulLevel c Faithful n).ncard

/--
A supplied minimal faithful closed core.  The core is already an element of
`c.Closeds`; `core_le` is its containment in every faithful closed set.-/
structure Data
    (c : QuotientSubmoduleEquidistribution.SetClosure E)
    (Faithful : Set E → Prop) where
  core : c.Closeds
  core_faithful : Faithful (core : Set E)
  core_le :
    ∀ C : c.Closeds, Faithful (C : Set E) →
      (core : Set E) ⊆ (C : Set E)

/--
If faithfulness of closed sets is exactly containment of a fixed seed set,
then the closure of those seeds is the minimal faithful core.-/
def Data.of_closed_iff_contains
    (c : QuotientSubmoduleEquidistribution.SetClosure E)
    (Faithful : Set E → Prop)
    (Seeds : Set E)
    (hFaithful :
      ∀ C : c.Closeds,
        Faithful (C : Set E) ↔ Seeds ⊆ (C : Set E)) :
    Data c Faithful where
  core := ⟨c Seeds, c.isClosed_closure Seeds⟩
  core_faithful :=
    (hFaithful ⟨c Seeds, c.isClosed_closure Seeds⟩).2
      (c.le_closure Seeds)
  core_le := by
    intro C hC
    exact c.closure_min ((hFaithful C).1 hC) C.property

/-- The special case in which faithfulness is defined as containing seeds.-/
def Data.of_contains
    (c : QuotientSubmoduleEquidistribution.SetClosure E)
    (Seeds : Set E) :
    Data c (fun C ↦ Seeds ⊆ C) :=
  Data.of_closed_iff_contains c (fun C ↦ Seeds ⊆ C) Seeds
    (fun _ ↦ Iff.rfl)

omit [Finite E] in
/--
For an upward-closed faithfulness predicate, a closed set is faithful exactly
when it contains the supplied minimal faithful core.
@isnad1 id=iff.1h5v.s7.ce28bf0a8a48 from=translated src=- shape=c5b92aeb vocab=a7bb31ee
-/
theorem Data.faithful_iff_core_subset
    {c : QuotientSubmoduleEquidistribution.SetClosure E}
    {Faithful : Set E → Prop}
    (D : Data c Faithful)
    (hFaithful : Monotone Faithful)
    (C : c.Closeds) :
    Faithful (C : Set E) ↔
      (D.core : Set E) ⊆ (C : Set E) := by
  constructor
  · exact D.core_le C
  · exact fun h ↦ hFaithful h D.core_faithful

/-- The faithful count is bounded by the full closure-system level count.
@isnad1 id=le.0h4v.s4.282d01573236 from=translated src=- shape=bfe5abfa vocab=2c7ab41f
-/
theorem faithfulLevelCount_le_levelCount
    (c : QuotientSubmoduleEquidistribution.SetClosure E)
    (Faithful : Set E → Prop) (n : ℕ) :
    faithfulLevelCount c Faithful n ≤ c.levelCount n := by
  classical
  letI : Fintype c.Closeds := Fintype.ofFinite c.Closeds
  unfold faithfulLevelCount faithfulLevel
  unfold QuotientSubmoduleEquidistribution.SetClosure.levelCount
  exact Set.ncard_le_ncard
    (fun _ hC ↦ hC.2)
    (Set.toFinite _)

/-- No faithful closed set lies below the cardinality of its minimal core.
@isnad1 id=eq.1h5v.s6.0a5539bb556a from=translated src=- shape=5dc24c23 vocab=95b82f18
-/
theorem faithfulLevelCount_eq_zero_of_lt_core
    {c : QuotientSubmoduleEquidistribution.SetClosure E}
    {Faithful : Set E → Prop}
    (D : Data c Faithful) {n : ℕ}
    (hn : n < (D.core : Set E).ncard) :
    faithfulLevelCount c Faithful n = 0 := by
  classical
  have hlevel : faithfulLevel c Faithful n = ∅ := by
    ext C
    constructor
    · intro hC
      change
        Faithful (C : Set E) ∧ (C : Set E).ncard = n
        at hC
      have hle :
          (D.core : Set E).ncard ≤ (C : Set E).ncard :=
        Set.ncard_le_ncard (D.core_le C hC.1)
      omega
    · simp
  rw [faithfulLevelCount, hlevel]
  simp

/-- At the core's cardinality, the core is the unique faithful closed set.
@isnad1 id=eq.1h5v.s6.04aaa938f954 from=translated src=- shape=66ff9060 vocab=7d51d00e
-/
theorem faithfulLevelCount_eq_one_of_eq_core
    {c : QuotientSubmoduleEquidistribution.SetClosure E}
    {Faithful : Set E → Prop}
    (D : Data c Faithful) {n : ℕ}
    (hn : n = (D.core : Set E).ncard) :
    faithfulLevelCount c Faithful n = 1 := by
  classical
  have hlevel : faithfulLevel c Faithful n = {D.core} := by
    ext C
    constructor
    · intro hC
      change
        Faithful (C : Set E) ∧ (C : Set E).ncard = n
        at hC
      have hsets :
          (D.core : Set E) = (C : Set E) :=
        Set.eq_of_subset_of_ncard_le
          (D.core_le C hC.1)
          (by rw [hC.2, hn])
      exact Set.mem_singleton_iff.mpr (Subtype.ext hsets.symm)
    · intro hC
      have hCeq : C = D.core := Set.mem_singleton_iff.mp hC
      subst C
      exact ⟨D.core_faithful, hn.symm⟩
  rw [faithfulLevelCount, hlevel]
  simp

/--
Equal core cardinalities force equality of faithful level counts at and below
the two cores.  Taking `n = 4` gives precisely the formal `d > 4` and `d = 4`
deduction, once the two module-theoretic cores have been constructed.
@isnad1 id=eq.2h8v.s7.855799643121 from=translated src=- shape=3f31d8ee vocab=c184cd98
-/
theorem faithfulLevelCount_eq_of_core_ncard_eq_of_level_le
    {cQ cS : QuotientSubmoduleEquidistribution.SetClosure E}
    {FaithfulQ FaithfulS : Set E → Prop}
    (Q : Data cQ FaithfulQ) (S : Data cS FaithfulS)
    (hcard :
      (Q.core : Set E).ncard = (S.core : Set E).ncard)
    {n : ℕ} (hn : n ≤ (Q.core : Set E).ncard) :
    faithfulLevelCount cQ FaithfulQ n =
      faithfulLevelCount cS FaithfulS n := by
  rcases hn.eq_or_lt with hn | hn
  · rw [faithfulLevelCount_eq_one_of_eq_core Q hn,
      faithfulLevelCount_eq_one_of_eq_core S (hn.trans hcard)]
  · rw [faithfulLevelCount_eq_zero_of_lt_core Q hn,
      faithfulLevelCount_eq_zero_of_lt_core S (hcard ▸ hn)]

end MinimalFaithfulCore

/-! ## Finite support for a joint stratification -/

namespace FiniteJointStratification

variable {L R I : Type*} [Fintype L] [Fintype R]

/--
The finite union of the values actually realized by two finite types.  The
ambient index type `I` need not be finite.-/
def JointRange (left : L → I) (right : R → I) :=
  {i : I // i ∈ Set.range left ∪ Set.range right}

/--
@isnad1 id=finite.0h5v.s4.a92299227f31 from=translated src=- shape=82bdeb26 vocab=92496c37
-/
instance jointRangeFinite (left : L → I) (right : R → I) :
    Finite (JointRange left right) :=
  ((Set.finite_range left).union (Set.finite_range right)).to_subtype

noncomputable instance jointRangeFintype
    (left : L → I) (right : R → I) :
    Fintype (JointRange left right) :=
  Fintype.ofFinite (JointRange left right)

/-- Lift the left indexing map to the finite joint range.-/
def toJointLeft
    (left : L → I) (right : R → I) (x : L) :
    JointRange left right :=
  ⟨left x, Set.mem_union_left _ ⟨x, rfl⟩⟩

/-- Lift the right indexing map to the finite joint range.-/
def toJointRight
    (left : L → I) (right : R → I) (x : R) :
    JointRange left right :=
  ⟨right x, Set.mem_union_right _ ⟨x, rfl⟩⟩

/-- One left fiber over the finite joint range.-/
def LeftFiber
    (left : L → I) (right : R → I)
    (i : JointRange left right) :=
  {x : L // toJointLeft left right x = i}

/--
@isnad1 id=finite.0h6v.s5.67900407bf38 from=translated src=- shape=02ee1000 vocab=27f4cb25
-/
instance leftFiberFinite
    (left : L → I) (right : R → I)
    (i : JointRange left right) :
    Finite (LeftFiber left right i) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- One right fiber over the finite joint range.-/
def RightFiber
    (left : L → I) (right : R → I)
    (i : JointRange left right) :=
  {x : R // toJointRight left right x = i}

/--
@isnad1 id=finite.0h6v.s5.49e046906253 from=translated src=- shape=c9a8e108 vocab=28deb450
-/
instance rightFiberFinite
    (left : L → I) (right : R → I)
    (i : JointRange left right) :
    Finite (RightFiber left right i) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/-- Exact finite partition of the left type by its realized index.
@isnad1 id=eq.0h5v.s6.ebc1ce2e20d3 from=translated src=- shape=aeeabd22 vocab=49370455
-/
theorem card_eq_sum_leftFibers
    (left : L → I) (right : R → I) :
    Fintype.card L =
      ∑ i : JointRange left right,
        Nat.card (LeftFiber left right i) := by
  classical
  calc
    Fintype.card L = Nat.card L :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card
        (Σ i : JointRange left right, LeftFiber left right i) :=
      Nat.card_congr
        (Equiv.sigmaFiberEquiv (toJointLeft left right)).symm
    _ = ∑ i : JointRange left right,
        Nat.card (LeftFiber left right i) :=
      Nat.card_sigma

/-- Exact finite partition of the right type by its realized index.
@isnad1 id=eq.0h5v.s6.dc6076c5e990 from=translated src=- shape=37ea4885 vocab=0e396dda
-/
theorem card_eq_sum_rightFibers
    (left : L → I) (right : R → I) :
    Fintype.card R =
      ∑ i : JointRange left right,
        Nat.card (RightFiber left right i) := by
  classical
  calc
    Fintype.card R = Nat.card R :=
      Nat.card_eq_fintype_card.symm
    _ = Nat.card
        (Σ i : JointRange left right, RightFiber left right i) :=
      Nat.card_congr
        (Equiv.sigmaFiberEquiv (toJointRight left right)).symm
    _ = ∑ i : JointRange left right,
        Nat.card (RightFiber left right i) :=
      Nat.card_sigma

/-- Fiberwise equality on the joint range implies equality of total sizes.
@isnad1 id=eq.1h5v.s5.217d67e2a019 from=translated src=- shape=7d58977c vocab=6ab1277b
-/
theorem card_eq_of_fiber_card_eq
    (left : L → I) (right : R → I)
    (h : ∀ i : JointRange left right,
      Nat.card (LeftFiber left right i) =
        Nat.card (RightFiber left right i)) :
    Fintype.card L = Fintype.card R := by
  rw [card_eq_sum_leftFibers left right,
    card_eq_sum_rightFibers left right]
  exact Finset.sum_congr rfl fun i _ ↦ h i

end FiniteJointStratification

/-! ## Simultaneous total/faithful induction for annihilator strata -/

namespace AnnihilatorInduction

variable {B : Type*}
  (measure : B → ℕ)
  (totalQ totalS faithfulQ faithfulS : B → ℕ)
  (ProperFactor : B → Type*)
  [∀ b : B, Fintype (ProperFactor b)]
  (factor : ∀ b : B, ProperFactor b → B)
  (Connected : B → Prop)

/--
The simultaneous induction pattern matching the manuscript's annihilator
decomposition.

The recurrences use the faithful counts of proper factors:

`total(b) = faithful(b) + sum_I faithful(factor(b,I))`.

At a connected object, the representation-theoretic branch supplies equality
of the current faithful counts.  At a disconnected object, product
decomposition supplies equality of the current total counts from smaller
total equalities.  The recurrence and the smaller faithful equalities recover
the other equality in either branch.
@isnad1 id=and.5h10v.s7.942a5a6dabd1 from=translated src=- shape=19741155 vocab=aef64c1d
-/
theorem total_and_faithful_eq_of_recurrence
    (hsmaller :
      ∀ (b : B) (I : ProperFactor b),
        measure (factor b I) < measure b)
    (hQ :
      ∀ b : B,
        totalQ b =
          faithfulQ b +
            ∑ I : ProperFactor b, faithfulQ (factor b I))
    (hS :
      ∀ b : B,
        totalS b =
          faithfulS b +
            ∑ I : ProperFactor b, faithfulS (factor b I))
    (hconnected :
      ∀ b : B, Connected b →
        (∀ b' : B, measure b' < measure b →
          totalQ b' = totalS b' ∧
            faithfulQ b' = faithfulS b') →
        faithfulQ b = faithfulS b)
    (hdisconnected :
      ∀ b : B, ¬ Connected b →
        (∀ b' : B, measure b' < measure b →
          totalQ b' = totalS b') →
        totalQ b = totalS b)
    (b : B) :
    totalQ b = totalS b ∧
      faithfulQ b = faithfulS b := by
  classical
  induction hμ : measure b using Nat.strong_induction_on generalizing b with
  | h n ih =>
      have ihPair :
          ∀ b' : B, measure b' < measure b →
            totalQ b' = totalS b' ∧
              faithfulQ b' = faithfulS b' := by
        intro b' hb'
        exact ih (measure b') (by simpa [hμ] using hb') b' rfl
      have hfactor :
          ∀ I : ProperFactor b,
            faithfulQ (factor b I) =
              faithfulS (factor b I) := by
        intro I
        exact (ihPair (factor b I) (hsmaller b I)).2
      have hsum :
          (∑ I : ProperFactor b, faithfulQ (factor b I)) =
            ∑ I : ProperFactor b, faithfulS (factor b I) := by
        apply Finset.sum_congr rfl
        intro I _
        exact hfactor I
      by_cases hb : Connected b
      · have hf : faithfulQ b = faithfulS b :=
          hconnected b hb ihPair
        have ht : totalQ b = totalS b := by
          rw [hQ b, hS b, hf, hsum]
        exact ⟨ht, hf⟩
      · have ht : totalQ b = totalS b :=
          hdisconnected b hb fun b' hb' ↦ (ihPair b' hb').1
        have hadd :
            faithfulQ b +
                ∑ I : ProperFactor b, faithfulQ (factor b I) =
              faithfulS b +
                ∑ I : ProperFactor b, faithfulS (factor b I) := by
          rw [← hQ b, ← hS b, ht]
        rw [hsum] at hadd
        exact ⟨ht, Nat.add_right_cancel hadd⟩

/-- In a simultaneous annihilator induction, either equality of the
current faithful counts or equality of the current total counts is enough;
the recurrence and smaller faithful equalities recover the other one.
@isnad1 id=and.4h9v.s7.aab965fb158d from=translated src=- shape=a3edf48f vocab=aef64c1d
-/
theorem total_and_faithful_eq_of_recurrence_of_local_either
    (hsmaller :
      ∀ (b : B) (I : ProperFactor b),
        measure (factor b I) < measure b)
    (hQ :
      ∀ b : B,
        totalQ b =
          faithfulQ b +
            ∑ I : ProperFactor b, faithfulQ (factor b I))
    (hS :
      ∀ b : B,
        totalS b =
          faithfulS b +
            ∑ I : ProperFactor b, faithfulS (factor b I))
    (hlocal :
      ∀ b : B,
        (∀ b' : B, measure b' < measure b →
          totalQ b' = totalS b' ∧
            faithfulQ b' = faithfulS b') →
        faithfulQ b = faithfulS b ∨ totalQ b = totalS b)
    (b : B) :
    totalQ b = totalS b ∧ faithfulQ b = faithfulS b := by
  classical
  induction hμ : measure b using Nat.strong_induction_on generalizing b with
  | h n ih =>
      have ihPair :
          ∀ b' : B, measure b' < measure b →
            totalQ b' = totalS b' ∧
              faithfulQ b' = faithfulS b' := by
        intro b' hb'
        exact ih (measure b') (by simpa [hμ] using hb') b' rfl
      have hsum :
          (∑ I : ProperFactor b, faithfulQ (factor b I)) =
            ∑ I : ProperFactor b, faithfulS (factor b I) := by
        apply Finset.sum_congr rfl
        intro I _
        exact (ihPair (factor b I) (hsmaller b I)).2
      rcases hlocal b ihPair with hf | ht
      · have ht : totalQ b = totalS b := by
          rw [hQ b, hS b, hf, hsum]
        exact ⟨ht, hf⟩
      · have hadd :
            faithfulQ b +
                ∑ I : ProperFactor b, faithfulQ (factor b I) =
              faithfulS b +
                ∑ I : ProperFactor b, faithfulS (factor b I) := by
          rw [← hQ b, ← hS b, ht]
        rw [hsum] at hadd
        exact ⟨ht, Nat.add_right_cancel hadd⟩

end AnnihilatorInduction

end QuotientSubmoduleEquidistribution.BottomLevels
