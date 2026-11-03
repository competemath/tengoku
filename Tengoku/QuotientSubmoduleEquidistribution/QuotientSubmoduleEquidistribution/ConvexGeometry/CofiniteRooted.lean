import Tengoku.QuotientSubmoduleEquidistribution.QuotientSubmoduleEquidistribution.ConvexGeometry.CofiniteLevel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Rooted and bad-rooted cofinite counting

This file is the finite counting endpoint used by the top-level argument.
For a fixed deletion size, closed complements are identified with rooted
deletions for which a designated bad event does not occur. Equality of the
rooted counts and of the bad-rooted counts then gives equality of the
corresponding colevels.

The representation-theoretic work is deliberately outside this module. In
particular, the eventual bad predicate should mean failure of a factor ladder
to reach its boundary; identifying that event with premature vanishing
requires a separate no-revival argument.
-/

noncomputable section

open Set

namespace QuotientSubmoduleEquidistribution.SetClosure

universe u

variable {E : Type u} [Fintype E] [DecidableEq E]

/-- Rooted deletion sets of size `j`.-/
def rootedDeletions
    (Rooted : Finset E → Prop) (j : ℕ) : Finset (Finset E) :=
  by
    classical
    exact (deletionsOfCard (E := E) j).filter Rooted

omit [DecidableEq E] in
/--
@isnad1 id=iff.0h4v.s5.66bdd012cc91 from=translated src=- shape=763691c7 vocab=12d8cd93
-/
@[simp]
theorem mem_rootedDeletions
    {Rooted : Finset E → Prop} {j : ℕ} {D : Finset E} :
    D ∈ rootedDeletions Rooted j ↔ D.card = j ∧ Rooted D := by
  simp [rootedDeletions]

/-- The bad rooted deletion sets. This filters the rooted family, rather
than counting all sets satisfying `Bad`.-/
def badRootedDeletions
    (Rooted Bad : Finset E → Prop) (j : ℕ) : Finset (Finset E) :=
  by
    classical
    exact (rootedDeletions Rooted j).filter Bad

omit [DecidableEq E] in
/--
@isnad1 id=iff.0h5v.s5.9ffc4b2c8f07 from=translated src=- shape=7961852f vocab=a40f9391
-/
@[simp]
theorem mem_badRootedDeletions
    {Rooted Bad : Finset E → Prop} {j : ℕ} {D : Finset E} :
    D ∈ badRootedDeletions Rooted Bad j ↔
      D.card = j ∧ Rooted D ∧ Bad D := by
  simp [badRootedDeletions, and_assoc]

/-- Rooted deletion sets on which no bad event occurs.-/
def goodRootedDeletions
    (Rooted Bad : Finset E → Prop) (j : ℕ) : Finset (Finset E) :=
  by
    classical
    exact (rootedDeletions Rooted j).filter fun D ↦ ¬ Bad D

omit [DecidableEq E] in
/--
@isnad1 id=iff.0h5v.s5.af2eb3516837 from=translated src=- shape=a755b070 vocab=876d764a
-/
@[simp]
theorem mem_goodRootedDeletions
    {Rooted Bad : Finset E → Prop} {j : ℕ} {D : Finset E} :
    D ∈ goodRootedDeletions Rooted Bad j ↔
      D.card = j ∧ Rooted D ∧ ¬ Bad D := by
  simp [goodRootedDeletions, and_assoc]

omit [DecidableEq E] in
/-- A closure characterization identifies legal cofinite deletions exactly
with good rooted deletions.
@isnad1 id=eq.1h5v.s6.9044b5404ebe from=translated src=- shape=5d311a42 vocab=d0bc8b57
-/
theorem cofiniteDeletions_eq_goodRootedDeletions
    (c : SetClosure E) (j : ℕ)
    (Rooted Bad : Finset E → Prop)
    (hcharacterize : ∀ {D : Finset E}, D.card = j →
      (c.IsClosed ((D : Set E)ᶜ) ↔ Rooted D ∧ ¬ Bad D)) :
    c.cofiniteDeletions j =
      goodRootedDeletions Rooted Bad j := by
  ext D
  rw [mem_cofiniteDeletions, mem_goodRootedDeletions]
  constructor
  · rintro ⟨hcard, hclosed⟩
    exact ⟨hcard, (hcharacterize hcard).1 hclosed⟩
  · rintro ⟨hcard, hrooted, hgood⟩
    exact ⟨hcard, (hcharacterize hcard).2
      ⟨hrooted, hgood⟩⟩

omit [DecidableEq E] in
/-- Equal rooted counts and equal bad-rooted counts force equal
good-rooted counts.
@isnad1 id=eq.2h6v.s6.be2d3d612f18 from=translated src=- shape=9a06d260 vocab=fe74ea84
-/
theorem goodRootedDeletions_card_eq_of_rooted_bad_eq
    (j : ℕ)
    (qRooted qBad sRooted sBad : Finset E → Prop)
    (hrooted :
      (rootedDeletions qRooted j).card =
        (rootedDeletions sRooted j).card)
    (hbad :
      (badRootedDeletions qRooted qBad j).card =
        (badRootedDeletions sRooted sBad j).card) :
    (goodRootedDeletions qRooted qBad j).card =
      (goodRootedDeletions sRooted sBad j).card := by
  classical
  have hq :=
    Finset.card_filter_add_card_filter_not
      (s := rootedDeletions qRooted j) qBad
  have hs :=
    Finset.card_filter_add_card_filter_not
      (s := rootedDeletions sRooted j) sBad
  have hq' :
      (badRootedDeletions qRooted qBad j).card +
          (goodRootedDeletions qRooted qBad j).card =
        (rootedDeletions qRooted j).card := by
    simpa only [badRootedDeletions, goodRootedDeletions]
      using hq
  have hs' :
      (badRootedDeletions sRooted sBad j).card +
          (goodRootedDeletions sRooted sBad j).card =
        (rootedDeletions sRooted j).card := by
    simpa only [badRootedDeletions, goodRootedDeletions]
      using hs
  omega

/-- Exact representation-theoretic data needed at one colevel. The two
cardinality equalities are the rooted-balance and bad-ladder-balance inputs
from the manuscript.-/
structure RootedBadCofiniteInput
    (qClosure sClosure : SetClosure E) (j : ℕ) where
  qRooted : Finset E → Prop
  sRooted : Finset E → Prop
  qBad : Finset E → Prop
  sBad : Finset E → Prop
  qClosedComplement_iff :
    ∀ {D : Finset E}, D.card = j →
      (qClosure.IsClosed ((D : Set E)ᶜ) ↔
        qRooted D ∧ ¬ qBad D)
  sClosedComplement_iff :
    ∀ {D : Finset E}, D.card = j →
      (sClosure.IsClosed ((D : Set E)ᶜ) ↔
        sRooted D ∧ ¬ sBad D)
  rooted_card_eq :
    (rootedDeletions qRooted j).card =
      (rootedDeletions sRooted j).card
  bad_rooted_card_eq :
    (badRootedDeletions qRooted qBad j).card =
      (badRootedDeletions sRooted sBad j).card

/-- The arbitrary-`j` finite endpoint: rooted balance, bad-rooted balance,
and the factor-ladder characterization imply equality at level `|E| - j`.
@isnad1 id=eq.1h5v.s5.e4f4c2c0839c from=translated src=- shape=760778b6 vocab=721ee30d
-/
theorem levelCount_card_sub_eq_of_rootedBadCofiniteInput
    (qClosure sClosure : SetClosure E) (j : ℕ)
    (hj : j ≤ Nat.card E)
    (input : RootedBadCofiniteInput qClosure sClosure j) :
    qClosure.levelCount (Nat.card E - j) =
      sClosure.levelCount (Nat.card E - j) := by
  rw [← cofiniteDeletions_card_eq_levelCount_card_sub
      qClosure j hj,
    ← cofiniteDeletions_card_eq_levelCount_card_sub
      sClosure j hj,
    cofiniteDeletions_eq_goodRootedDeletions
      qClosure j input.qRooted input.qBad
        input.qClosedComplement_iff,
    cofiniteDeletions_eq_goodRootedDeletions
      sClosure j input.sRooted input.sBad
        input.sClosedComplement_iff]
  exact
    goodRootedDeletions_card_eq_of_rooted_bad_eq
      j input.qRooted input.qBad input.sRooted input.sBad
        input.rooted_card_eq input.bad_rooted_card_eq

end QuotientSubmoduleEquidistribution.SetClosure
