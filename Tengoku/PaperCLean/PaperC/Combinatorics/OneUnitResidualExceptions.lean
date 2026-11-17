import Tengoku.PaperCLean.PaperC.Combinatorics.ResidualCertificates
import Tengoku.PaperCLean.PaperC.Combinatorics.ResidualComponentCounts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1200000

/-!
# Residual exceptions for a channel with one exact unit

This module isolates part (v) of Lemma 6.5.  When a channel contains exactly
one exact unit, that unit is chosen canonically (uniqueness makes the
noncomputable choice immaterial).  Inside any prescribed finite family of
nontrivial unpinned components, only the components meeting one of its two
occurrences can support an exact extracted certificate.  There are at most
two such components.
-/

namespace PaperC
namespace OneUnitResidualExceptions

open Affine
open Affine.RationalChannelCode
open LargePrimeOccurrences
open LargePrimeGraph
open LargePrimeGraphResolution
open PinnedGraphResolution
open ResidualCertificates
open ResidualComponentCounts

noncomputable section

noncomputable local instance instDecidableLargePrimeAdj
    (x y L : ℕ) :
    DecidableRel (largePrimeGraph x y L).Adj :=
  Classical.decRel _

/-- A channel of unit count one has a unique channel unit.-/
private theorem exists_unique_channelUnit
    {L a b : ℕ} {h : ℤ}
    (hm : channelUnitCount L a b h = 1) :
    ∃ unit : ChannelUnit L a b h,
      ∀ other : ChannelUnit L a b h, other = unit := by
  change Fintype.card (ChannelUnit L a b h) = 1 at hm
  rw [Fintype.card_eq_one_iff] at hm
  exact hm

/--
The unique exact unit of a channel of multiplicity one.  Although the
definition uses a choice, its value is propositionally forced by `hm`.-/
noncomputable def uniqueChannelUnit
    {L a b : ℕ} {h : ℤ}
    (hm : channelUnitCount L a b h = 1) :
    ChannelUnit L a b h :=
  (exists_unique_channelUnit hm).choose

/-- Every exact unit equals the canonical unit in the one-unit branch.
@isnad1 id=eq.1h5v.s5.4b967eaf83ae from=translated src=- shape=0f101a26 vocab=3abd4392
-/
theorem channelUnit_eq_uniqueChannelUnit
    {L a b : ℕ} {h : ℤ}
    (hm : channelUnitCount L a b h = 1)
    (unit : ChannelUnit L a b h) :
    unit = uniqueChannelUnit hm :=
  (exists_unique_channelUnit hm).choose_spec unit

/--
Finset-level form of uniqueness: every cell belonging to
`rationalChannelUnits` is the underlying cell of the canonical unit.
@isnad1 id=eq.2h5v.s8.1b63e0fbd8a1 from=translated src=- shape=97c6cdd8 vocab=35addd85
-/
theorem channelCell_eq_uniqueChannelUnit
    {L a b : ℕ} {h : ℤ}
    (hm : channelUnitCount L a b h = 1)
    {cell : Fin (L + 1) × Fin (L + 1)}
    (hcell : cell ∈ rationalChannelUnits L a b h) :
    cell = (uniqueChannelUnit hm).1 := by
  let unit : ChannelUnit L a b h := ⟨cell, hcell⟩
  exact congrArg Subtype.val
    (channelUnit_eq_uniqueChannelUnit hm unit)

/--
Components in the prescribed family which meet one of the two occurrences
of the unique exact unit.-/
noncomputable def oneUnitExceptionalComponents
    {x y L a b : ℕ} {h : ℤ}
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hm : channelUnitCount L a b h = 1) :
    Finset (largePrimeGraph x y L).ConnectedComponent :=
  componentsMeetingPair components
    (Sum.inl (uniqueChannelUnit hm).1.1)
    (Sum.inr (uniqueChannelUnit hm).1.2)

/--
@isnad1 id=iff.1h8v.s9.fc21bbed8a82 from=translated src=- shape=de0fcde7 vocab=dd2d6ed7
-/
@[simp]
theorem mem_oneUnitExceptionalComponents
    {x y L a b : ℕ} {h : ℤ}
    {components :
      Finset (largePrimeGraph x y L).ConnectedComponent}
    {hm : channelUnitCount L a b h = 1}
    {C : (largePrimeGraph x y L).ConnectedComponent} :
    C ∈ oneUnitExceptionalComponents components hm ↔
      C ∈ components ∧
        ((largePrimeGraph x y L).connectedComponentMk
              (Sum.inl (uniqueChannelUnit hm).1.1) = C ∨
          (largePrimeGraph x y L).connectedComponentMk
              (Sum.inr (uniqueChannelUnit hm).1.2) = C) := by
  exact mem_componentsMeetingPair

/-- At most two components can meet the unique exact unit.
@isnad1 id=le.1h7v.s5.11e2bde7265a from=translated src=- shape=4afa1237 vocab=ec6c0047
-/
theorem card_oneUnitExceptionalComponents_le_two
    {x y L a b : ℕ} {h : ℤ}
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hm : channelUnitCount L a b h = 1) :
    (oneUnitExceptionalComponents components hm).card ≤ 2 := by
  exact card_componentsMeetingPair_le_two
    components
    (Sum.inl (uniqueChannelUnit hm).1.1)
    (Sum.inr (uniqueChannelUnit hm).1.2)

/--
If a canonical certificate lies on a channel containing exactly one unit,
its component belongs to the exceptional family meeting that unit.

Positivity of `(a,b)` is not needed for this conclusion: cardinal-one
uniqueness of `rationalChannelUnits` is already stronger.
@isnad1 id=mem.5h8v.s8.99cf4969a0f4 from=translated src=- shape=b0b84e5a vocab=11c3bb90
-/
theorem canonicalCertificate_mem_oneUnitExceptionalComponents_of_onChannel
    {x y L a b : ℕ} {h : ℤ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (components :
      Finset (largePrimeGraph x y L).ConnectedComponent)
    (hcomponents :
      ∀ C ∈ components,
        IsNontrivialUnpinnedComponent
          (largePrimeGraph x y L)
          (pinnedVertices x y L) C)
    (hm : channelUnitCount L a b h = 1)
    (C : {C // C ∈ components})
    (hexact :
      OnChannel a b h
        (canonicalCertificates
          hx hy components hcomponents C).offsetCell) :
    C.1 ∈ oneUnitExceptionalComponents components hm := by
  let cert :=
    canonicalCertificates hx hy components hcomponents C
  have hcellMem :
      (cert.left, cert.right) ∈
        rationalChannelUnits L a b h := by
    rw [mem_rationalChannelUnits]
    exact hexact
  have hcell :
      (cert.left, cert.right) =
        (uniqueChannelUnit hm).1 :=
    channelCell_eq_uniqueChannelUnit hm hcellMem
  have hleft :
      cert.left = (uniqueChannelUnit hm).1.1 :=
    congrArg Prod.fst hcell
  rw [mem_oneUnitExceptionalComponents]
  refine ⟨C.2, Or.inl ?_⟩
  rw [← hleft]
  exact cert.left_component

end

end OneUnitResidualExceptions
end PaperC
