import Tengoku.Seed.Data.Finset.Card
import Tengoku.Seed.Data.Finset.Powerset
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.ConvexGeometry.CofiniteTwo
import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.ConvexGeometry.LevelPolynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# From two-point deletions to the `(N - 2)` level

The inverse complement construction needs `2 ≤ Nat.card E`.  Without this
hypothesis, natural-number subtraction truncates and a set of cardinality
`Nat.card E - 2` need not have a two-element complement.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.SetClosure

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]
  (c : SetClosure E)

/-- All deletion sets of a fixed cardinality.-/
def deletionsOfCard (j : ℕ) : Finset (Finset E) :=
  Finset.univ.powersetCard j

omit [DecidableEq E] in
/--
@isnad1 id=iff.0h3v.s5.247d45753b01 from=translated src=- shape=4a89cf16 vocab=5deb61f5
-/
@[simp]
theorem mem_deletionsOfCard {j : ℕ} {D : Finset E} :
    D ∈ deletionsOfCard (E := E) j ↔ D.card = j := by
  simp [deletionsOfCard]

/-- Deletion sets of size `j` whose complements are closed.-/
def cofiniteDeletions (j : ℕ) : Finset (Finset E) :=
  by
    classical
    exact
      (deletionsOfCard (E := E) j).filter fun D ↦
        c.IsClosed ((D : Set E)ᶜ)

omit [DecidableEq E] in
/--
@isnad1 id=iff.0h4v.s6.93d6a170cafe from=translated src=- shape=1a73c9e5 vocab=15937483
-/
@[simp]
theorem mem_cofiniteDeletions
    {j : ℕ} {D : Finset E} :
    D ∈ c.cofiniteDeletions j ↔
      D.card = j ∧ c.IsClosed ((D : Set E)ᶜ) := by
  simp [cofiniteDeletions]

/-- Complement identifies legal size-`j` deletions with closed sets on
level `|E| - j`. The bound on `j` is essential because natural-number
subtraction is truncated.-/
def cofiniteDeletionLevelEquiv
    (j : ℕ) (hj : j ≤ Nat.card E) :
    {D : Finset E // D ∈ c.cofiniteDeletions j} ≃
      {C : c.Closeds //
        (C : Set E).ncard = Nat.card E - j} where
  toFun D := by
    have hD :=
      (mem_cofiniteDeletions (c := c)).1 D.property
    refine ⟨⟨((D.1 : Set E)ᶜ), hD.2⟩, ?_⟩
    rw [Set.ncard_compl, Set.ncard_coe_finset, hD.1]
  invFun C := by
    classical
    let D : Finset E :=
      Finset.univ.filter fun x ↦
        x ∉ (C.1.1 : Set E)
    have hDcoe :
        (D : Set E) = (C.1.1 : Set E)ᶜ := by
      ext x
      simp [D]
    have hDcard : D.card = j := by
      calc
        D.card = (D : Set E).ncard := by
          rw [Set.ncard_coe_finset]
        _ = ((C.1.1 : Set E)ᶜ).ncard := by
          rw [hDcoe]
        _ = Nat.card E - (C.1.1 : Set E).ncard :=
          Set.ncard_compl _
        _ = Nat.card E - (Nat.card E - j) := by
          rw [C.2]
        _ = j := by omega
    refine
      ⟨D, (mem_cofiniteDeletions (c := c)).2
        ⟨hDcard, ?_⟩⟩
    have heq :
        ((D : Set E)ᶜ) = (C.1.1 : Set E) := by
      rw [hDcoe, compl_compl]
    rw [heq]
    exact C.1.2
  left_inv D := by
    apply Subtype.ext
    ext x
    simp
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    simp

/-- The cardinality of legal size-`j` deletions is the colevel
`|E| - j` count.
@isnad1 id=eq.1h3v.s5.2d3a10dacd7b from=translated src=- shape=c1910849 vocab=dbcf5427
-/
theorem cofiniteDeletions_card_eq_levelCount_card_sub
    (j : ℕ) (hj : j ≤ Nat.card E) :
    (c.cofiniteDeletions j).card =
      c.levelCount (Nat.card E - j) := by
  unfold SetClosure.levelCount
  calc
    (c.cofiniteDeletions j).card =
        Nat.card {D : Finset E //
          D ∈ c.cofiniteDeletions j} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card {C : c.Closeds //
          (C : Set E).ncard = Nat.card E - j} :=
      Nat.card_congr
        (cofiniteDeletionLevelEquiv c j hj)
    _ = {C : c.Closeds |
          (C : Set E).ncard = Nat.card E - j}.ncard :=
      Nat.card_coe_set_eq _

/-- The unique element of a one-point legal deletion.-/
noncomputable def cofiniteOneElement
    (D : {D : Finset E // D ∈ c.cofiniteDeletions 1}) : E :=
  Classical.choose <|
    Finset.card_eq_one.mp
      ((mem_cofiniteDeletions (c := c)).1 D.property).1

omit [DecidableEq E] in
/-- A legal deletion of cardinality one is the singleton of its chosen
element.
@isnad1 id=eq.0h3v.s6.5b100e5a4c3d from=translated src=- shape=d7077b73 vocab=165ff3c8
-/
theorem cofiniteOne_eq_singleton_element
    (D : {D : Finset E // D ∈ c.cofiniteDeletions 1}) :
    D.1 = {c.cofiniteOneElement D} :=
  Classical.choose_spec <|
    Finset.card_eq_one.mp
      ((mem_cofiniteDeletions (c := c)).1 D.property).1

/-- Top extreme points are equivalent to legal one-point deletions.-/
noncomputable def topExtremeCofiniteOneEquiv :
    {x : E // c.IsTopExtreme x} ≃
      {D : Finset E // D ∈ c.cofiniteDeletions 1} where
  toFun x := ⟨{x.1}, by
    rw [mem_cofiniteDeletions]
    refine ⟨Finset.card_singleton x.1, ?_⟩
    simpa only [Finset.coe_singleton] using
      (c.isTopExtreme_iff_isClosed_compl_singleton x.1).1 x.2⟩
  invFun D := ⟨c.cofiniteOneElement D, by
    apply (c.isTopExtreme_iff_isClosed_compl_singleton _).2
    have hclosed :=
      ((mem_cofiniteDeletions (c := c)).1 D.property).2
    rw [c.cofiniteOne_eq_singleton_element D] at hclosed
    simpa only [Finset.coe_singleton] using hclosed⟩
  left_inv x := by
    apply Subtype.ext
    have hsingleton :=
      c.cofiniteOne_eq_singleton_element
        (⟨{x.1}, by
          rw [mem_cofiniteDeletions]
          refine ⟨Finset.card_singleton x.1, ?_⟩
          simpa only [Finset.coe_singleton] using
            (c.isTopExtreme_iff_isClosed_compl_singleton x.1).1 x.2⟩ :
          {D : Finset E // D ∈ c.cofiniteDeletions 1})
    exact (Finset.singleton_inj.mp hsingleton).symm
  right_inv D := by
    apply Subtype.ext
    exact (c.cofiniteOne_eq_singleton_element D).symm

omit [DecidableEq E] in
/-- The subtype of top extreme points has the cardinality recorded by the
finite top-boundary set.
@isnad1 id=eq.0h2v.s4.927c9ce4fb4b from=translated src=- shape=a07e3c26 vocab=085317a5
-/
theorem natCard_topExtreme_eq_topExtremeFinset_card :
    Nat.card {x : E // c.IsTopExtreme x} =
      c.topExtremeFinset.card := by
  calc
    Nat.card {x : E // c.IsTopExtreme x} =
        Nat.card {x : E // x ∈ c.topExtremeFinset} :=
      Nat.card_congr <|
        Equiv.subtypeEquivRight fun x ↦
          (mem_topExtremeFinset (c := c)).symm
    _ = c.topExtremeFinset.card := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]

/-- Every closure operator on a finite ground type has one closed set at the
top level: the whole ground set.
@isnad1 id=eq.0h2v.s4.6cf54e183013 from=translated src=- shape=46c8c14f vocab=7ab7f593
-/
theorem levelCount_card_eq_one :
    c.levelCount (Nat.card E) = 1 := by
  have hzero : 0 ≤ Nat.card E := Nat.zero_le _
  have hdeletions : c.cofiniteDeletions 0 = {∅} := by
    ext D
    rw [mem_cofiniteDeletions]
    simp only [Finset.mem_singleton]
    constructor
    · exact fun h ↦ Finset.card_eq_zero.mp h.1
    · intro hD
      subst D
      exact ⟨Finset.card_empty, by simpa using c.isClosed_top⟩
  calc
    c.levelCount (Nat.card E) =
        c.levelCount (Nat.card E - 0) := by rw [Nat.sub_zero]
    _ = (c.cofiniteDeletions 0).card :=
      (cofiniteDeletions_card_eq_levelCount_card_sub c 0 hzero).symm
    _ = 1 := by rw [hdeletions]; simp

/-- The colevel-one count is the number of top extreme points.
@isnad1 id=eq.1h2v.s5.c216ca5a05b4 from=translated src=- shape=831092bb vocab=28494b92
-/
theorem levelCount_card_sub_one_eq_natCard_topExtreme
    (hcard : 1 ≤ Nat.card E) :
    c.levelCount (Nat.card E - 1) =
      Nat.card {x : E // c.IsTopExtreme x} := by
  rw [← cofiniteDeletions_card_eq_levelCount_card_sub c 1 hcard]
  calc
    (c.cofiniteDeletions 1).card =
        Nat.card {D : Finset E // D ∈ c.cofiniteDeletions 1} := by
      rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ = Nat.card {x : E // c.IsTopExtreme x} :=
      Nat.card_congr c.topExtremeCofiniteOneEquiv.symm

omit [DecidableEq E] in
/-- The generic cofinite-deletion family specializes to the existing
two-point deletion family.
@isnad1 id=eq.0h2v.s4.0bddd10761bb from=translated src=- shape=6b074847 vocab=4028b7ba
-/
theorem cofiniteDeletions_two_eq :
    c.cofiniteDeletions 2 = c.cofiniteTwoDeletions := by
  ext D
  rw [mem_cofiniteDeletions, mem_cofiniteTwoDeletions]

/-- Complement gives an equivalence between allowed two-point deletions
and closed sets at level `Nat.card E - 2`.-/
def cofiniteTwoDeletionLevelEquiv
    (hcard : 2 ≤ Nat.card E) :
    {D : Finset E // D ∈ c.cofiniteTwoDeletions} ≃
      {C : c.Closeds //
        (C : Set E).ncard = Nat.card E - 2} where
  toFun D := by
    have hD :=
      (mem_cofiniteTwoDeletions (c := c)).1 D.property
    refine
      ⟨⟨((D.1 : Set E)ᶜ), hD.2⟩, ?_⟩
    rw [Set.ncard_compl, Set.ncard_coe_finset, hD.1]
  invFun C := by
    classical
    let D : Finset E :=
      Finset.univ.filter fun x ↦
        x ∉ (C.1.1 : Set E)
    have hDcoe :
        (D : Set E) = (C.1.1 : Set E)ᶜ := by
      ext x
      simp [D]
    have hDcard : D.card = 2 := by
      calc
        D.card = (D : Set E).ncard := by
          rw [Set.ncard_coe_finset]
        _ = ((C.1.1 : Set E)ᶜ).ncard := by
          rw [hDcoe]
        _ = Nat.card E - (C.1.1 : Set E).ncard :=
          Set.ncard_compl _
        _ = Nat.card E - (Nat.card E - 2) := by
          rw [C.2]
        _ = 2 := by omega
    refine
      ⟨D, (mem_cofiniteTwoDeletions (c := c)).2
        ⟨hDcard, ?_⟩⟩
    have heq :
        ((D : Set E)ᶜ) = (C.1.1 : Set E) := by
      rw [hDcoe, compl_compl]
    rw [heq]
    exact C.1.2
  left_inv D := by
    apply Subtype.ext
    ext x
    simp
  right_inv C := by
    apply Subtype.ext
    apply Subtype.ext
    ext x
    simp

/-- The finite complement-count bridge.  The explicit lower bound is
essential because `Nat.card E - 2` uses truncated subtraction.
@isnad1 id=eq.1h2v.s5.8ba8c8247531 from=translated src=- shape=d3c2d022 vocab=ef386e09
-/
theorem cofiniteTwoCount_eq_levelCount_card_sub_two
    (hcard : 2 ≤ Nat.card E) :
    c.cofiniteTwoCount =
      c.levelCount (Nat.card E - 2) := by
  unfold cofiniteTwoCount
  rw [← cofiniteDeletions_two_eq c]
  exact cofiniteDeletions_card_eq_levelCount_card_sub c 2 hcard

end QuotientSubmoduleEquidistribution.SetClosure
