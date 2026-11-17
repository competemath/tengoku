import Tengoku.PaperCLean.PaperC.Affine.StartBoundaryRange
import Tengoku.PaperCLean.PaperC.Arithmetic.ChannelCount
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.LinearAlgebra.Finsupp.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option maxHeartbeats 1600000

/-!
# The systematic rational channel code

This file formalizes the linear-algebraic content of Lemma 5.1.  Channel
units are represented directly by their two complete-start vertices; the
integer offset of vertex `v` is `v - 1`, so the vertices enumerate exactly
`{-1, 0, ..., L - 1}`.

An even binary selection of exact units has even boundary in each start.
The boundary-range theorem therefore lifts it uniquely to row coefficients.
For the canonical height `h = b y - a x`, the resulting coefficient vector
is a relation between the two start systems.  The lift is injective, its
image has dimension `m - 1` for a nonempty channel with `m` units, and its
affine character is the restriction of the two root indicators.
-/

namespace PaperC
namespace Affine
namespace RationalChannelCode

open scoped BigOperators

noncomputable section

/-! ## Exact units in complete-start coordinates -/

/-- Integer offset represented by a complete-start vertex.-/
def channelVertexOffset {L : ℕ} (v : Fin (L + 1)) : ℤ :=
  (v.1 : ℤ) - 1

/-- Exact units of the channel `(a,b,h)`, represented by their two vertices.-/
def rationalChannelUnits (L a b : ℕ) (h : ℤ) :
    Finset (Fin (L + 1) × Fin (L + 1)) :=
  Finset.univ.filter fun cell =>
    OnChannel a b h
      (channelVertexOffset cell.1, channelVertexOffset cell.2)

/-- The finite type of exact units of one rational channel.-/
abbrev ChannelUnit (L a b : ℕ) (h : ℤ) :=
  {cell // cell ∈ rationalChannelUnits L a b h}

/--
@isnad1 id=iff.0h5v.s8.f71bb23c8eba from=translated src=- shape=41fe0f74 vocab=c02cb507
-/
@[simp]
theorem mem_rationalChannelUnits
    {L a b : ℕ} {h : ℤ}
    {cell : Fin (L + 1) × Fin (L + 1)} :
    cell ∈ rationalChannelUnits L a b h ↔
      OnChannel a b h
        (channelVertexOffset cell.1, channelVertexOffset cell.2) := by
  simp [rationalChannelUnits]

/-- Every vertex offset lies in the paper's interval `{-1, ..., L-1}`.
@isnad1 id=mem.0h2v.s5.ff4a75f14e0d from=translated src=- shape=4cbff7c4 vocab=4672efe7
-/
theorem channelVertexOffset_mem_offsetInterval
    {L : ℕ} (v : Fin (L + 1)) :
    channelVertexOffset v ∈ offsetInterval L := by
  rw [mem_offsetInterval]
  simp only [channelVertexOffset]
  constructor <;> omega

/-- A channel unit, viewed as the integer cell used by `ChannelGeometry`.-/
def channelUnitCell
    {L a b : ℕ} {h : ℤ} (unit : ChannelUnit L a b h) :
    ℤ × ℤ :=
  (channelVertexOffset unit.1.1, channelVertexOffset unit.1.2)

/--
@isnad1 id=mem.0h5v.s5.b627a16d6dc7 from=translated src=- shape=07076a5f vocab=29251764
-/
theorem channelUnitCell_mem_channelCells
    {L a b : ℕ} {h : ℤ} (unit : ChannelUnit L a b h) :
    channelUnitCell unit ∈ channelCells L a b h := by
  rw [mem_channelCells]
  refine ⟨?_, ?_⟩
  · rw [mem_offsetBox]
    exact ⟨
      (by
        simpa only [channelUnitCell, mem_offsetInterval] using
          channelVertexOffset_mem_offsetInterval unit.1.1),
      (by
        simpa only [channelUnitCell, mem_offsetInterval] using
          channelVertexOffset_mem_offsetInterval unit.1.2)⟩
  · exact mem_rationalChannelUnits.mp unit.2

/-- Vertex corresponding to an integer offset in `{-1, ..., L-1}`.-/
def offsetVertexOfMem
    {L : ℕ} (i : ℤ) (hi : i ∈ offsetInterval L) :
    Fin (L + 1) := by
  refine ⟨(i + 1).toNat, ?_⟩
  have hibounds := mem_offsetInterval.mp hi
  rw [Int.toNat_lt (by omega)]
  omega

/--
@isnad1 id=eq.1h2v.s4.2dab17b2c68a from=translated src=- shape=ef857fe3 vocab=cdd91811
-/
@[simp]
theorem channelVertexOffset_offsetVertexOfMem
    {L : ℕ} (i : ℤ) (hi : i ∈ offsetInterval L) :
    channelVertexOffset (offsetVertexOfMem i hi) = i := by
  have hibounds := mem_offsetInterval.mp hi
  simp only [channelVertexOffset, offsetVertexOfMem]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/--
@isnad1 id=eq.0h2v.s5.459783c01d08 from=translated src=- shape=ec167725 vocab=a0377c7e
-/
@[simp]
theorem offsetVertexOfMem_channelVertexOffset
    {L : ℕ} (v : Fin (L + 1)) :
    offsetVertexOfMem (channelVertexOffset v)
        (channelVertexOffset_mem_offsetInterval v) =
      v := by
  apply Fin.ext
  simp [offsetVertexOfMem, channelVertexOffset]

/-- An integer channel cell, represented by its two complete-start vertices.-/
def channelCellUnit
    {L a b : ℕ} {h : ℤ}
    (cell : {cell // cell ∈ channelCells L a b h}) :
    ChannelUnit L a b h := by
  have hcell := mem_channelCells.mp cell.2
  have hbox := mem_offsetBox.mp hcell.1
  let vi : Fin (L + 1) :=
    offsetVertexOfMem cell.1.1
      (by simpa only [mem_offsetInterval] using hbox.1)
  let vj : Fin (L + 1) :=
    offsetVertexOfMem cell.1.2
      (by simpa only [mem_offsetInterval] using hbox.2)
  refine ⟨(vi, vj), mem_rationalChannelUnits.mpr ?_⟩
  simpa [vi, vj] using hcell.2

/--
@isnad1 id=eq.0h5v.s6.b82d1e6cf438 from=translated src=- shape=02dff467 vocab=1a8ec7b4
-/
@[simp]
theorem channelUnitCell_channelCellUnit
    {L a b : ℕ} {h : ℤ}
    (cell : {cell // cell ∈ channelCells L a b h}) :
    channelUnitCell (channelCellUnit cell) = cell := by
  apply Prod.ext <;>
    simp [channelCellUnit, channelUnitCell]

/--
@isnad1 id=eq.0h5v.s6.3848c18c33f7 from=translated src=- shape=2aa59863 vocab=4741c1bb
-/
@[simp]
theorem channelCellUnit_channelUnitCell
    {L a b : ℕ} {h : ℤ}
    (unit : ChannelUnit L a b h) :
    channelCellUnit
        (⟨channelUnitCell unit,
          channelUnitCell_mem_channelCells unit⟩ :
          {cell // cell ∈ channelCells L a b h}) =
      unit := by
  apply Subtype.ext
  apply Prod.ext <;>
    simp [channelCellUnit, channelUnitCell]

/-- Vertex-form exact units are equivalent to the manuscript's integer cells.-/
def channelUnitEquivChannelCells
    (L a b : ℕ) (h : ℤ) :
    ChannelUnit L a b h ≃
      {cell // cell ∈ channelCells L a b h} where
  toFun unit :=
    ⟨channelUnitCell unit, channelUnitCell_mem_channelCells unit⟩
  invFun := channelCellUnit
  left_inv := channelCellUnit_channelUnitCell
  right_inv := by
    intro cell
    apply Subtype.ext
    exact channelUnitCell_channelCellUnit cell

/-- The vertex representation has exactly `m(a,b,h)` elements.
@isnad1 id=eq.0h4v.s5.a3ca094368ef from=translated src=- shape=14cb3293 vocab=a270fcb2
-/
theorem card_rationalChannelUnits_eq_channelCells
    (L a b : ℕ) (h : ℤ) :
    (rationalChannelUnits L a b h).card =
      (channelCells L a b h).card := by
  simpa using
    Fintype.card_congr
      (channelUnitEquivChannelCells L a b h)

/--
After casting to integers, a complete-start label is the start plus the
vertex offset.  The positivity assumption handles the root label `x - 1`.
@isnad1 id=eq.1h3v.s5.28df133018e8 from=translated src=- shape=6e6654bc vocab=e719c2ac
-/
theorem startCompleteVertexLabel_cast
    {x L : ℕ} (hx : 1 ≤ x) (v : Fin (L + 1)) :
    (startCompleteVertexLabel x L v : ℤ) =
      (x : ℤ) + channelVertexOffset v := by
  unfold startCompleteVertexLabel channelVertexOffset
  by_cases hv : v.1 = 0
  · rw [ite_eq_left hv]
    simp only [hv, Nat.cast_sub hx, Nat.cast_one, Nat.cast_zero]
    omega
  · rw [ite_eq_right hv]
    push_cast
    omega

/-! ## Even selections and their dimension -/

/-- Sum of the coefficients of a binary family.-/
def coordinateSum (ι : Type*) [Fintype ι] :
    (ι → F₂) →ₗ[F₂] F₂ :=
  Fintype.linearCombination F₂ (fun _ => 1)

/--
@isnad1 id=eq.0h2v.s8.65b2bd575008 from=translated src=- shape=62a9ba2c vocab=b3518e0b
-/
@[simp]
theorem coordinateSum_apply
    (ι : Type*) [Fintype ι] (c : ι → F₂) :
    coordinateSum ι c = ∑ i : ι, c i := by
  simp [coordinateSum, Fintype.linearCombination_apply, smul_eq_mul]

/-- Binary selections containing an even number of channel units.-/
abbrev EvenChannelSelection (L a b : ℕ) (h : ℤ) :=
  LinearMap.ker (coordinateSum (ChannelUnit L a b h))

/-- Subset encoded by a binary unit-selection vector.-/
def selectedChannelUnits
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂) :
    Finset (ChannelUnit L a b h) :=
  Finset.univ.filter fun unit => c unit ≠ 0

private theorem f2_eq_indicator_ne_zero (z : F₂) :
    z = if z ≠ 0 then 1 else 0 := by
  classical
  by_cases hz : z = 0
  · simp [hz]
  · have hz1 : z = 1 := Fin.eq_one_of_ne_zero z hz
    simp [hz1]

/-- Coordinate sum equals the selected-subset cardinality modulo two.
@isnad1 id=eq.0h5v.s8.4960d35bf06d from=translated src=- shape=9d64e1f4 vocab=0c7a8933
-/
theorem coordinateSum_eq_selectedChannelUnits_card
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂) :
    coordinateSum (ChannelUnit L a b h) c =
      ((selectedChannelUnits c).card : F₂) := by
  classical
  simp only [coordinateSum_apply]
  calc
    (∑ unit : ChannelUnit L a b h, c unit) =
        ∑ unit : ChannelUnit L a b h,
          if c unit ≠ 0 then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro unit _hunit
            exact f2_eq_indicator_ne_zero (c unit)
    _ = ((selectedChannelUnits c).card : F₂) := by
      simpa only [selectedChannelUnits] using
        (Finset.sum_boole
          (R := F₂)
          (fun unit : ChannelUnit L a b h => c unit ≠ 0)
          Finset.univ)

/--
The kernel called `EvenChannelSelection` is literally the family of
even-cardinality subsets of exact units.
@isnad1 id=iff.0h5v.s8.151bd963497f from=translated src=- shape=fbaeef9e vocab=e4c6a0fd
-/
theorem mem_evenChannelSelection_iff_even_card
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂) :
    c ∈ EvenChannelSelection L a b h ↔
      Even (selectedChannelUnits c).card := by
  rw [LinearMap.mem_ker,
    coordinateSum_eq_selectedChannelUnits_card,
    even_iff_two_dvd]
  exact ZMod.natCast_eq_zero_iff
    (selectedChannelUnits c).card 2

/--
@isnad1 id=surjecti.0h1v.s8.8de69d804dd6 from=translated src=- shape=9f7a716e vocab=f22aa0c4
-/
theorem coordinateSum_surjective
    (ι : Type*) [Fintype ι] [Nonempty ι] :
    Function.Surjective (coordinateSum ι) := by
  classical
  let i₀ : ι := Classical.choice (inferInstance : Nonempty ι)
  intro c
  refine ⟨Pi.single i₀ c, ?_⟩
  simp [coordinateSum_apply]

/--
The even-subset hyperplane on a nonempty finite type has dimension one less
than the number of coordinates.
@isnad1 id=eq.0h1v.s10.4ec2111193f4 from=translated src=- shape=68078396 vocab=262c1579
-/
theorem finrank_ker_coordinateSum
    (ι : Type*) [Fintype ι] [Nonempty ι] :
    Module.finrank F₂ (LinearMap.ker (coordinateSum ι)) =
      Fintype.card ι - 1 := by
  have hnullity :=
    LinearMap.finrank_range_add_finrank_ker (coordinateSum ι)
  have hrange :
      LinearMap.range (coordinateSum ι) = ⊤ :=
    LinearMap.range_eq_top.mpr (coordinateSum_surjective ι)
  rw [hrange] at hnullity
  simp [Module.finrank_pi] at hnullity
  omega

/--
@isnad1 id=eq.1h4v.s9.9357d1983f48 from=translated src=- shape=764211bf vocab=794006f7
-/
theorem finrank_evenChannelSelection
    {L a b : ℕ} {h : ℤ}
    (hm : 0 < (rationalChannelUnits L a b h).card) :
    Module.finrank F₂ (EvenChannelSelection L a b h) =
      (rationalChannelUnits L a b h).card - 1 := by
  have hnonempty :
      (rationalChannelUnits L a b h).Nonempty :=
    Finset.card_pos.mp hm
  let unit₀ : ChannelUnit L a b h :=
    ⟨Classical.choose hnonempty, Classical.choose_spec hnonempty⟩
  letI : Nonempty (ChannelUnit L a b h) := ⟨unit₀⟩
  simpa using
    (finrank_ker_coordinateSum (ChannelUnit L a b h))

/-- The dimension formula also covers the empty channel (`0 - 1 = 0` in `ℕ`).
@isnad1 id=eq.0h4v.s9.d538097efd15 from=translated src=- shape=62a7e5ef vocab=44d7e5ba
-/
theorem finrank_evenChannelSelection_all
    (L a b : ℕ) (h : ℤ) :
    Module.finrank F₂ (EvenChannelSelection L a b h) =
      (rationalChannelUnits L a b h).card - 1 := by
  by_cases hm : (rationalChannelUnits L a b h).card = 0
  · have hbot :
        EvenChannelSelection L a b h = ⊥ := by
      apply (Submodule.eq_bot_iff _).2
      intro c _hc
      funext unit
      exfalso
      have hnonempty :
          (rationalChannelUnits L a b h).Nonempty :=
        ⟨unit.1, unit.2⟩
      exact (Finset.card_ne_zero.mpr hnonempty) hm
    rw [hbot, hm]
    simp
  · exact finrank_evenChannelSelection (Nat.pos_of_ne_zero hm)

/-! ## Unit boundaries and their canonical lift -/

/-- Boundary vertices selected in the left start block.-/
def leftUnitBoundary
    (L a b : ℕ) (h : ℤ) :
    (ChannelUnit L a b h → F₂) →ₗ[F₂]
      (Fin (L + 1) → F₂) :=
  Fintype.linearCombination F₂
    (fun unit => Pi.single unit.1.1 1)

/-- Boundary vertices selected in the right start block.-/
def rightUnitBoundary
    (L a b : ℕ) (h : ℤ) :
    (ChannelUnit L a b h → F₂) →ₗ[F₂]
      (Fin (L + 1) → F₂) :=
  Fintype.linearCombination F₂
    (fun unit => Pi.single unit.1.2 1)

/--
@isnad1 id=eq.0h6v.s10.c3a91264ec5f from=translated src=- shape=bd53d2fc vocab=d487012c
-/
@[simp]
theorem leftUnitBoundary_apply
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂) (v : Fin (L + 1)) :
    leftUnitBoundary L a b h c v =
      ∑ unit : ChannelUnit L a b h,
        c unit *
          (Pi.single unit.1.1 (1 : F₂) :
            Fin (L + 1) → F₂) v := by
  simp [leftUnitBoundary, Fintype.linearCombination_apply, smul_eq_mul]

/--
@isnad1 id=eq.0h6v.s10.473453c82f35 from=translated src=- shape=bd53d2fc vocab=26f34418
-/
@[simp]
theorem rightUnitBoundary_apply
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂) (v : Fin (L + 1)) :
    rightUnitBoundary L a b h c v =
      ∑ unit : ChannelUnit L a b h,
        c unit *
          (Pi.single unit.1.2 (1 : F₂) :
            Fin (L + 1) → F₂) v := by
  simp [rightUnitBoundary, Fintype.linearCombination_apply, smul_eq_mul]

/--
@isnad1 id=eq.0h5v.s10.f20acf16bcdd from=translated src=- shape=912f0494 vocab=82f2f1a5
-/
theorem startVertexSum_leftUnitBoundary
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂) :
    startVertexSum L (leftUnitBoundary L a b h c) =
      coordinateSum (ChannelUnit L a b h) c := by
  classical
  simp only [startVertexSum_apply, leftUnitBoundary_apply,
    coordinateSum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro unit _hunit
  rw [← Finset.mul_sum]
  simp

/--
@isnad1 id=eq.0h5v.s10.4e50f85f2d9a from=translated src=- shape=912f0494 vocab=3a2cb3c7
-/
theorem startVertexSum_rightUnitBoundary
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂) :
    startVertexSum L (rightUnitBoundary L a b h c) =
      coordinateSum (ChannelUnit L a b h) c := by
  classical
  simp only [startVertexSum_apply, rightUnitBoundary_apply,
    coordinateSum_apply]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro unit _hunit
  rw [← Finset.mul_sum]
  simp

/-- The unique row coefficients whose complete boundary is an even vector.-/
def liftEvenBoundary (L : ℕ) :
    LinearMap.ker (startVertexSum L) →ₗ[F₂] (Fin L → F₂) :=
  (startBoundaryEquivEven L).symm.toLinearMap

/--
@isnad1 id=eq.0h2v.s12.ed5aaa29f91d from=translated src=- shape=6b140048 vocab=507397b1
-/
@[simp]
theorem startCompleteBoundary_liftEvenBoundary
    {L : ℕ} (w : LinearMap.ker (startVertexSum L)) :
    startCompleteBoundary L (liftEvenBoundary L w) = w := by
  have h := (startBoundaryEquivEven L).apply_symm_apply w
  exact congrArg Subtype.val h

/-- Package the left unit boundary of an even selection as an even vector.-/
def evenLeftBoundary
    {L a b : ℕ} {h : ℤ} (c : EvenChannelSelection L a b h) :
    LinearMap.ker (startVertexSum L) :=
  ⟨leftUnitBoundary L a b h c,
    by
      change startVertexSum L (leftUnitBoundary L a b h c) = 0
      rw [startVertexSum_leftUnitBoundary]
      exact c.2⟩

/-- Package the right unit boundary of an even selection as an even vector.-/
def evenRightBoundary
    {L a b : ℕ} {h : ℤ} (c : EvenChannelSelection L a b h) :
    LinearMap.ker (startVertexSum L) :=
  ⟨rightUnitBoundary L a b h c,
    by
      change startVertexSum L (rightUnitBoundary L a b h c) = 0
      rw [startVertexSum_rightUnitBoundary]
      exact c.2⟩

/-- Row coefficients canonically induced by an even selection of units.-/
def channelRelationCoefficients
    (L a b : ℕ) (h : ℤ) :
    EvenChannelSelection L a b h →ₗ[F₂]
      (Sum (Fin L) (Fin L) → F₂) where
  toFun c
    | Sum.inl i => liftEvenBoundary L (evenLeftBoundary c) i
    | Sum.inr i => liftEvenBoundary L (evenRightBoundary c) i
  map_add' c d := by
    funext s
    cases s with
    | inl i =>
        change
          liftEvenBoundary L
              (evenLeftBoundary (c + d)) i =
            liftEvenBoundary L (evenLeftBoundary c) i +
              liftEvenBoundary L (evenLeftBoundary d) i
        rw [show evenLeftBoundary (c + d) =
            evenLeftBoundary c + evenLeftBoundary d by
          apply Subtype.ext
          exact LinearMap.map_add (leftUnitBoundary L a b h) c d,
          LinearMap.map_add]
        rfl
    | inr i =>
        change
          liftEvenBoundary L
              (evenRightBoundary (c + d)) i =
            liftEvenBoundary L (evenRightBoundary c) i +
              liftEvenBoundary L (evenRightBoundary d) i
        rw [show evenRightBoundary (c + d) =
            evenRightBoundary c + evenRightBoundary d by
          apply Subtype.ext
          exact LinearMap.map_add (rightUnitBoundary L a b h) c d,
          LinearMap.map_add]
        rfl
  map_smul' k c := by
    funext s
    cases s with
    | inl i =>
        change
          liftEvenBoundary L
              (evenLeftBoundary (k • c)) i =
            k • liftEvenBoundary L (evenLeftBoundary c) i
        rw [show evenLeftBoundary (k • c) =
            k • evenLeftBoundary c by
          apply Subtype.ext
          exact LinearMap.map_smul (leftUnitBoundary L a b h) k c,
          LinearMap.map_smul]
        rfl
    | inr i =>
        change
          liftEvenBoundary L
              (evenRightBoundary (k • c)) i =
            k • liftEvenBoundary L (evenRightBoundary c) i
        rw [show evenRightBoundary (k • c) =
            k • evenRightBoundary c by
          apply Subtype.ext
          exact LinearMap.map_smul (rightUnitBoundary L a b h) k c,
          LinearMap.map_smul]
        rfl

/--
@isnad1 id=eq.0h6v.s12.bb7b37bce5c7 from=translated src=- shape=a229669e vocab=c212c150
-/
@[simp]
theorem twoStartCompleteBoundary_channelRelationCoefficients_inl
    {L a b : ℕ} {h : ℤ}
    (c : EvenChannelSelection L a b h) (v : Fin (L + 1)) :
    twoStartCompleteBoundary L
        (channelRelationCoefficients L a b h c) (Sum.inl v) =
      leftUnitBoundary L a b h c v := by
  change
    startCompleteBoundary L
        (liftEvenBoundary L (evenLeftBoundary c)) v =
      leftUnitBoundary L a b h c v
  exact congrFun
    (startCompleteBoundary_liftEvenBoundary (evenLeftBoundary c)) v

/--
@isnad1 id=eq.0h6v.s12.a3f825be4754 from=translated src=- shape=a229669e vocab=99d098f9
-/
@[simp]
theorem twoStartCompleteBoundary_channelRelationCoefficients_inr
    {L a b : ℕ} {h : ℤ}
    (c : EvenChannelSelection L a b h) (v : Fin (L + 1)) :
    twoStartCompleteBoundary L
        (channelRelationCoefficients L a b h c) (Sum.inr v) =
      rightUnitBoundary L a b h c v := by
  change
    startCompleteBoundary L
        (liftEvenBoundary L (evenRightBoundary c)) v =
      rightUnitBoundary L a b h c v
  exact congrFun
    (startCompleteBoundary_liftEvenBoundary (evenRightBoundary c)) v

/-! ## Injectivity of the unit boundary -/

/-- Distinct units of a positive channel have distinct left vertices.
@isnad1 id=injectiv.1h4v.s8.2a9f369435f3 from=translated src=- shape=4a4616a6 vocab=0aa30148
-/
theorem channelUnit_left_injective
    {L a b : ℕ} {h : ℤ} (hb : 0 < b) :
    Function.Injective
      (fun unit : ChannelUnit L a b h => unit.1.1) := by
  intro unit₁ unit₂ huv
  apply Subtype.ext
  have hcell :
      channelUnitCell unit₁ = channelUnitCell unit₂ := by
    apply fst_injOn_channelCells hb
      (channelUnitCell_mem_channelCells unit₁)
      (channelUnitCell_mem_channelCells unit₂)
    simp only [channelUnitCell, huv]
  apply Prod.ext
  · exact huv
  · apply Fin.ext
    have hsnd := congrArg Prod.snd hcell
    simp only [channelUnitCell, channelVertexOffset] at hsnd
    omega

/-- Distinct units of a positive channel have distinct right vertices.
@isnad1 id=injectiv.1h4v.s8.1fa8621122df from=translated src=- shape=fe28d7b3 vocab=c88f9c07
-/
theorem channelUnit_right_injective
    {L a b : ℕ} {h : ℤ} (ha : 0 < a) :
    Function.Injective
      (fun unit : ChannelUnit L a b h => unit.1.2) := by
  intro unit₁ unit₂ huv
  apply Subtype.ext
  have hcell :
      channelUnitCell unit₁ = channelUnitCell unit₂ := by
    apply snd_injOn_channelCells ha
      (channelUnitCell_mem_channelCells unit₁)
      (channelUnitCell_mem_channelCells unit₂)
    simp only [channelUnitCell, huv]
  apply Prod.ext
  · apply Fin.ext
    have hfst := congrArg Prod.fst hcell
    simp only [channelUnitCell, channelVertexOffset] at hfst
    omega
  · exact huv

/-- The left occurrence boundary remembers every unit coefficient.
@isnad1 id=injectiv.1h4v.s9.a05a56bc5721 from=translated src=- shape=43ce4155 vocab=ceb1215a
-/
theorem leftUnitBoundary_injective
    {L a b : ℕ} {h : ℤ} (hb : 0 < b) :
    Function.Injective (leftUnitBoundary L a b h) := by
  classical
  intro c d hcd
  funext unit
  have hvalue :=
    congrFun hcd unit.1.1
  have hc :
      leftUnitBoundary L a b h c unit.1.1 = c unit := by
    simp only [leftUnitBoundary_apply]
    rw [Fintype.sum_eq_single unit]
    · simp
    · intro other hne
      have hvertex : other.1.1 ≠ unit.1.1 := by
        intro hv
        exact hne (channelUnit_left_injective hb hv)
      simp [Pi.single_apply, hvertex]
  have hd :
      leftUnitBoundary L a b h d unit.1.1 = d unit := by
    simp only [leftUnitBoundary_apply]
    rw [Fintype.sum_eq_single unit]
    · simp
    · intro other hne
      have hvertex : other.1.1 ≠ unit.1.1 := by
        intro hv
        exact hne (channelUnit_left_injective hb hv)
      simp [Pi.single_apply, hvertex]
  exact hc ▸ hd ▸ hvalue

/-- The canonical row-coefficient lift is injective on even selections.
@isnad1 id=injectiv.1h4v.s11.2a8c45493c63 from=translated src=- shape=97287b62 vocab=ccdfa568
-/
theorem channelRelationCoefficients_injective
    {L a b : ℕ} {h : ℤ} (hb : 0 < b) :
    Function.Injective (channelRelationCoefficients L a b h) := by
  intro c d hcd
  apply Subtype.ext
  apply leftUnitBoundary_injective hb
  funext v
  rw [← twoStartCompleteBoundary_channelRelationCoefficients_inl c v,
    ← twoStartCompleteBoundary_channelRelationCoefficients_inl d v,
    hcd]

/-! ## The multiplicative relation carried by an even channel selection -/

/--
One row of a start is the incidence sum of the values at its two complete
vertices.
@isnad1 id=eq.0h5v.s9.aaf78a481c60 from=translated src=- shape=f288659d vocab=45ea9b58
-/
theorem startSystem_apply_eq_sum_incidence
    (M x L : ℕ) (ω : SampleSpace M) (i : Fin L) :
    startSystem M x L ω i =
      ∑ v : Fin (L + 1),
        startIncidenceColumn i v *
          valueBit ω (startCompleteVertexLabel x L v) := by
  rw [startSystem_apply]
  by_cases hi : i.1 = 0
  · simp [startIncidenceColumn, startBaseVertex, startTipVertex,
      startRootVertex, startCompleteVertexLabel, Pi.single_apply, hi,
      add_mul, Finset.sum_add_distrib]
  · simp [startIncidenceColumn, startBaseVertex, startTipVertex,
      startRootVertex, startCompleteVertexLabel, Pi.single_apply, hi,
      add_mul, Finset.sum_add_distrib]

/-- Line-boundary identity for the actual finite-cylinder start rows.
@isnad1 id=eq.0h5v.s10.98e00ebc27e6 from=translated src=- shape=a4963945 vocab=5df4bb15
-/
theorem sum_startSystem_eq_sum_completeBoundary
    (M x L : ℕ) (ω : SampleSpace M) (u : Fin L → F₂) :
    (∑ i : Fin L, u i * startSystem M x L ω i) =
      ∑ v : Fin (L + 1),
        startCompleteBoundary L u v *
          valueBit ω (startCompleteVertexLabel x L v) := by
  simp_rw [startSystem_apply_eq_sum_incidence]
  calc
    (∑ i : Fin L,
        u i *
          ∑ v : Fin (L + 1),
            startIncidenceColumn i v *
              valueBit ω (startCompleteVertexLabel x L v)) =
        ∑ i : Fin L, ∑ v : Fin (L + 1),
          u i *
            (startIncidenceColumn i v *
              valueBit ω (startCompleteVertexLabel x L v)) := by
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
    _ = ∑ v : Fin (L + 1), ∑ i : Fin L,
          u i *
            (startIncidenceColumn i v *
              valueBit ω (startCompleteVertexLabel x L v)) :=
      Finset.sum_comm
    _ = ∑ v : Fin (L + 1),
          (∑ i : Fin L, u i * startIncidenceColumn i v) *
            valueBit ω (startCompleteVertexLabel x L v) := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          ring
    _ = ∑ v : Fin (L + 1),
          startCompleteBoundary L u v *
            valueBit ω (startCompleteVertexLabel x L v) := by
          simp only [startCompleteBoundary_apply]

/-- Joint line-boundary identity for the two finite-cylinder start systems.
@isnad1 id=eq.0h6v.s10.6a549f9227ea from=translated src=- shape=0c9796a2 vocab=ac03aba5
-/
theorem dotProduct_twoStartSystem_eq_sum_completeBoundary
    (M x y L : ℕ) (ω : SampleSpace M)
    (u : Sum (Fin L) (Fin L) → F₂) :
    dotProduct u (twoStartSystem M x y L ω) =
      ∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
        twoStartCompleteBoundary L u v *
          valueBit ω (twoStartCompleteVertexLabel x y L v) := by
  rw [dotProduct, Fintype.sum_sum_type, Fintype.sum_sum_type]
  change
    (∑ i : Fin L, u (Sum.inl i) * startSystem M x L ω i) +
        (∑ i : Fin L, u (Sum.inr i) * startSystem M y L ω i) =
      (∑ v : Fin (L + 1),
          startCompleteBoundary L (fun i => u (Sum.inl i)) v *
            valueBit ω (startCompleteVertexLabel x L v)) +
        ∑ v : Fin (L + 1),
          startCompleteBoundary L (fun i => u (Sum.inr i)) v *
            valueBit ω (startCompleteVertexLabel y L v)
  rw [sum_startSystem_eq_sum_completeBoundary,
    sum_startSystem_eq_sum_completeBoundary]

private theorem sum_leftUnitBoundary_mul
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂)
    (f : Fin (L + 1) → F₂) :
    ∑ v : Fin (L + 1), leftUnitBoundary L a b h c v * f v =
      ∑ unit : ChannelUnit L a b h, c unit * f unit.1.1 := by
  classical
  simp only [leftUnitBoundary_apply]
  calc
    (∑ v : Fin (L + 1),
        (∑ unit : ChannelUnit L a b h,
          c unit *
            (Pi.single unit.1.1 (1 : F₂) :
              Fin (L + 1) → F₂) v) * f v) =
        ∑ v : Fin (L + 1),
          ∑ unit : ChannelUnit L a b h,
            (c unit *
              (Pi.single unit.1.1 (1 : F₂) :
                Fin (L + 1) → F₂) v) * f v := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.sum_mul]
    _ = ∑ unit : ChannelUnit L a b h,
          ∑ v : Fin (L + 1),
            (c unit *
              (Pi.single unit.1.1 (1 : F₂) :
                Fin (L + 1) → F₂) v) * f v :=
      Finset.sum_comm
    _ = ∑ unit : ChannelUnit L a b h, c unit * f unit.1.1 := by
      apply Finset.sum_congr rfl
      intro unit _hunit
      simp [Pi.single_apply]

private theorem sum_rightUnitBoundary_mul
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂)
    (f : Fin (L + 1) → F₂) :
    ∑ v : Fin (L + 1), rightUnitBoundary L a b h c v * f v =
      ∑ unit : ChannelUnit L a b h, c unit * f unit.1.2 := by
  classical
  simp only [rightUnitBoundary_apply]
  calc
    (∑ v : Fin (L + 1),
        (∑ unit : ChannelUnit L a b h,
          c unit *
            (Pi.single unit.1.2 (1 : F₂) :
              Fin (L + 1) → F₂) v) * f v) =
        ∑ v : Fin (L + 1),
          ∑ unit : ChannelUnit L a b h,
            (c unit *
              (Pi.single unit.1.2 (1 : F₂) :
                Fin (L + 1) → F₂) v) * f v := by
          apply Finset.sum_congr rfl
          intro v _hv
          rw [Finset.sum_mul]
    _ = ∑ unit : ChannelUnit L a b h,
          ∑ v : Fin (L + 1),
            (c unit *
              (Pi.single unit.1.2 (1 : F₂) :
                Fin (L + 1) → F₂) v) * f v :=
      Finset.sum_comm
    _ = ∑ unit : ChannelUnit L a b h, c unit * f unit.1.2 := by
      apply Finset.sum_congr rfl
      intro unit _hunit
      simp [Pi.single_apply]

/-- The boundary sum of a channel lift is the sum over its exact units.
@isnad1 id=eq.0h9v.s12.745a1f31748e from=translated src=- shape=f73a41b9 vocab=016bbfdb
-/
theorem sum_completeBoundary_channelRelationCoefficients
    {M x y L a b : ℕ} {h : ℤ}
    (ω : SampleSpace M) (c : EvenChannelSelection L a b h) :
    (∑ v : Sum (Fin (L + 1)) (Fin (L + 1)),
        twoStartCompleteBoundary L
            (channelRelationCoefficients L a b h c) v *
          valueBit ω (twoStartCompleteVertexLabel x y L v)) =
      ∑ unit : ChannelUnit L a b h,
        (c : ChannelUnit L a b h → F₂) unit *
          (valueBit ω
              (startCompleteVertexLabel x L unit.1.1) +
            valueBit ω
              (startCompleteVertexLabel y L unit.1.2)) := by
  rw [Fintype.sum_sum_type]
  simp only [
    twoStartCompleteBoundary_channelRelationCoefficients_inl,
    twoStartCompleteBoundary_channelRelationCoefficients_inr,
    twoStartCompleteVertexLabel]
  rw [sum_leftUnitBoundary_mul, sum_rightUnitBoundary_mul,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro unit _hunit
  ring

/--
For the canonical height, each exact unit gives equal cross-products
`a(x+i) = b(y+j)`.
@isnad1 id=eq.3h7v.s9.54902462f6d8 from=translated src=- shape=a5aaa1b2 vocab=4aa8dc6f
-/
theorem channelUnit_label_mul_eq
    {x y L a b : ℕ} {h : ℤ}
    (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (unit : ChannelUnit L a b h) :
    a * startCompleteVertexLabel x L unit.1.1 =
      b * startCompleteVertexLabel y L unit.1.2 := by
  apply Int.ofNat_injective
  change
    (a : ℤ) *
        (startCompleteVertexLabel x L unit.1.1 : ℤ) =
      (b : ℤ) *
        (startCompleteVertexLabel y L unit.1.2 : ℤ)
  rw [startCompleteVertexLabel_cast hx,
    startCompleteVertexLabel_cast hy]
  have hunit := mem_rationalChannelUnits.mp unit.2
  simp only [OnChannel] at hunit
  linarith [hheight]

/--
@isnad1 id=lt.1h3v.s5.732f30b3ce80 from=translated src=- shape=78f5457e vocab=e2fdf0d6
-/
theorem startCompleteVertexLabel_pos
    {x L : ℕ} (hx : 2 ≤ x) (v : Fin (L + 1)) :
    0 < startCompleteVertexLabel x L v := by
  unfold startCompleteVertexLabel
  split_ifs <;> omega

private theorem add_cross_of_add_eq_add
    (A X B Y : F₂) (h : A + X = B + Y) :
    X + Y = A + B := by
  revert A X B Y
  decide

/-- Every exact unit has the same two-vertex value parity, namely `v(a)+v(b)`.
@isnad1 id=eq.5h9v.s9.3de579158be7 from=translated src=- shape=37379c5c vocab=e7a00dc9
-/
theorem valueBit_add_of_channelUnit
    {M x y L a b : ℕ} {h : ℤ}
    (ω : SampleSpace M) (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (unit : ChannelUnit L a b h) :
    valueBit ω (startCompleteVertexLabel x L unit.1.1) +
        valueBit ω (startCompleteVertexLabel y L unit.1.2) =
      valueBit ω a + valueBit ω b := by
  have hmul :=
    channelUnit_label_mul_eq
      (show 1 ≤ x by omega) (show 1 ≤ y by omega) hheight unit
  have hvalue := congrArg (valueBit ω) hmul
  rw [valueBit_mul ω ha.ne'
        (startCompleteVertexLabel_pos hx unit.1.1).ne',
      valueBit_mul ω hb.ne'
        (startCompleteVertexLabel_pos hy unit.1.2).ne'] at hvalue
  exact add_cross_of_add_eq_add _ _ _ _ hvalue

/--
The canonical row coefficients of an even channel selection form a relation
between the two starts.
@isnad1 id=mem.5h8v.s11.0d56074faf17 from=translated src=- shape=242ba85d vocab=78611591
-/
theorem channelRelationCoefficients_mem_relationSpace
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (c : EvenChannelSelection L a b h) :
    channelRelationCoefficients L a b h c ∈
      RelationSpace (twoStartSystem M x y L) := by
  rw [LinearMap.mem_ker]
  apply LinearMap.ext
  intro ω
  rw [relationMap_apply, relationFunctional_apply,
    dotProduct_twoStartSystem_eq_sum_completeBoundary,
    sum_completeBoundary_channelRelationCoefficients]
  calc
    (∑ unit : ChannelUnit L a b h,
        (c : ChannelUnit L a b h → F₂) unit *
          (valueBit ω (startCompleteVertexLabel x L unit.1.1) +
            valueBit ω (startCompleteVertexLabel y L unit.1.2))) =
        ∑ unit : ChannelUnit L a b h,
          (c : ChannelUnit L a b h → F₂) unit *
            (valueBit ω a + valueBit ω b) := by
            apply Finset.sum_congr rfl
            intro unit _hunit
            rw [valueBit_add_of_channelUnit
              ω ha hb hx hy hheight unit]
    _ = (∑ unit : ChannelUnit L a b h,
          (c : ChannelUnit L a b h → F₂) unit) *
          (valueBit ω a + valueBit ω b) := by
            rw [Finset.sum_mul]
    _ = 0 := by
      have hc :
          ∑ unit : ChannelUnit L a b h,
            (c : ChannelUnit L a b h → F₂) unit = 0 := by
        have hc' := c.2
        change
          coordinateSum (ChannelUnit L a b h)
              (c : ChannelUnit L a b h → F₂) = 0 at hc'
        simpa only [coordinateSum_apply] using hc'
      rw [hc, zero_mul]

/-! ## The rational code as a subspace of the relation space -/

/--
Canonical injection from even selections of exact channel units to relations
between the two starts.-/
def rationalRelationMap
    (M x y L a b : ℕ) (h : ℤ)
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x) :
    EvenChannelSelection L a b h →ₗ[F₂]
      RelationSpace (twoStartSystem M x y L) :=
  (channelRelationCoefficients L a b h).codRestrict
    (RelationSpace (twoStartSystem M x y L))
    (channelRelationCoefficients_mem_relationSpace
      ha hb hx hy hheight)

/--
@isnad1 id=eq.5h8v.s13.b4f1c016c933 from=translated src=- shape=91e6db0a vocab=d051de6b
-/
@[simp]
theorem rationalRelationMap_coe
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (c : EvenChannelSelection L a b h) :
    ((rationalRelationMap M x y L a b h
        ha hb hx hy hheight c :
      RelationSpace (twoStartSystem M x y L)) :
        Sum (Fin L) (Fin L) → F₂) =
      channelRelationCoefficients L a b h c :=
  rfl

/--
@isnad1 id=injectiv.5h7v.s12.65be453c9b39 from=translated src=- shape=40052823 vocab=f4bc1aa9
-/
theorem rationalRelationMap_injective
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x) :
    Function.Injective
      (rationalRelationMap M x y L a b h
        ha hb hx hy hheight) := by
  intro c d hcd
  apply channelRelationCoefficients_injective hb
  exact congrArg Subtype.val hcd

/-- The systematic rational subspace `S_{a,b,h} ⊂ R(x,y)`.-/
def rationalCode
    (M x y L a b : ℕ) (h : ℤ)
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x) :
    Submodule F₂ (RelationSpace (twoStartSystem M x y L)) :=
  LinearMap.range
    (rationalRelationMap M x y L a b h
      ha hb hx hy hheight)

/--
If the channel contains `m ≥ 1` exact units, its rational code has dimension
`m - 1`.
@isnad1 id=eq.6h7v.s13.38bc85913e4e from=translated src=- shape=93fbebe4 vocab=af3a393c
-/
theorem finrank_rationalCode
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hm : 0 < (rationalChannelUnits L a b h).card) :
    Module.finrank F₂
        (rationalCode M x y L a b h
          ha hb hx hy hheight) =
      (rationalChannelUnits L a b h).card - 1 := by
  rw [rationalCode,
    LinearMap.finrank_range_of_inj
      (rationalRelationMap_injective
        ha hb hx hy hheight),
    finrank_evenChannelSelection hm]

/-- Uniform dimension formula, including channels with no exact unit.
@isnad1 id=eq.5h7v.s13.5d7e7908c9fb from=translated src=- shape=3508c29a vocab=af3a393c
-/
theorem finrank_rationalCode_all
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x) :
    Module.finrank F₂
        (rationalCode M x y L a b h
          ha hb hx hy hheight) =
      (rationalChannelUnits L a b h).card - 1 := by
  rw [rationalCode,
    LinearMap.finrank_range_of_inj
      (rationalRelationMap_injective
        ha hb hx hy hheight),
    finrank_evenChannelSelection_all]

/-- The rational code is nonzero exactly when the channel has at least two units.
@isnad1 id=iff.5h7v.s11.eba7467738a6 from=translated src=- shape=50028d8e vocab=70256e09
-/
theorem rationalCode_ne_bot_iff_two_le_card
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x) :
    rationalCode M x y L a b h
        ha hb hx hy hheight ≠ ⊥ ↔
      2 ≤ (rationalChannelUnits L a b h).card := by
  rw [← Submodule.one_le_finrank_iff,
    finrank_rationalCode_all ha hb hx hy hheight]
  omega

/-- Nontriviality criterion using the manuscript's integer-cell count.
@isnad1 id=iff.5h7v.s11.a524c3c6feec from=translated src=- shape=8851475a vocab=661e6e8f
-/
theorem rationalCode_ne_bot_iff_two_le_channelCells_card
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x) :
    rationalCode M x y L a b h
        ha hb hx hy hheight ≠ ⊥ ↔
      2 ≤ (channelCells L a b h).card := by
  rw [rationalCode_ne_bot_iff_two_le_card
      ha hb hx hy hheight,
    card_rationalChannelUnits_eq_channelCells]

/-- Dimension formula stated with the manuscript's integer-cell count.
@isnad1 id=eq.6h7v.s13.489cf1cf217e from=translated src=- shape=5d38f1e4 vocab=9c7690b6
-/
theorem finrank_rationalCode_eq_channelCells_card_sub_one
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (hm : 0 < (channelCells L a b h).card) :
    Module.finrank F₂
        (rationalCode M x y L a b h
          ha hb hx hy hheight) =
      (channelCells L a b h).card - 1 := by
  have hcard :=
    card_rationalChannelUnits_eq_channelCells L a b h
  calc
    Module.finrank F₂
        (rationalCode M x y L a b h
          ha hb hx hy hheight) =
        (rationalChannelUnits L a b h).card - 1 :=
      finrank_rationalCode ha hb hx hy hheight
        (by omega)
    _ = (channelCells L a b h).card - 1 := by
      rw [hcard]

/--
If a positive primitive channel contains at least two exact units, then the
primitive coefficients satisfy the final assertion `max(a,b) ≤ L`.
@isnad1 id=le.4h4v.s6.06345ceb51f8 from=translated src=- shape=9bcf582d vocab=97852ad6
-/
theorem max_channelCoefficients_le_length
    {L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b) (hab : a.Coprime b)
    (hm : 2 ≤ (rationalChannelUnits L a b h).card) :
    max a b ≤ L := by
  have hcardEq :=
    card_rationalChannelUnits_eq_channelCells L a b h
  have hcard :
      1 < (channelCells L a b h).card := by
    omega
  have hnonempty :
      (channelCells L a b h).Nonempty :=
    Finset.card_pos.mp (by omega)
  obtain ⟨cell₁, hcell₁⟩ := hnonempty
  obtain ⟨cell₂, hcell₂, hne₂₁⟩ :=
    Finset.exists_mem_ne hcard cell₁
  have hbounds :=
    channel_coefficients_le_length_of_mem
      ha hb hab hcell₁ hcell₂ hne₂₁.symm
  exact max_le hbounds.1 hbounds.2

/-! ## Restriction of the affine character -/

/-- The boundary of a start at its root is the dot product with `startRhs`.
@isnad1 id=eq.0h2v.s9.c46e115c7b31 from=translated src=- shape=d38355bd vocab=ec6d8c0f
-/
theorem startCompleteBoundary_root_eq_dot_startRhs
    {L : ℕ} (u : Fin L → F₂) :
    startCompleteBoundary L u (startRootVertex L) =
      ∑ i : Fin L, u i * startRhs L i := by
  classical
  simp only [startCompleteBoundary_apply]
  apply Finset.sum_congr rfl
  intro i _hi
  by_cases hi : i.1 = 0
  · simp [startIncidenceColumn, startBaseVertex, startTipVertex,
      startRootVertex, startRhs, Pi.single_apply, hi]
  · simp [startIncidenceColumn, startBaseVertex, startTipVertex,
      startRootVertex, startRhs, Pi.single_apply, hi]

/-- For two starts, the affine dot product is the sum of the two root bits.
@isnad1 id=eq.0h2v.s10.ca65517c8024 from=translated src=- shape=5c648e20 vocab=4976e5ff
-/
theorem dotProduct_twoStartRhs_eq_boundary_roots
    {L : ℕ} (u : Sum (Fin L) (Fin L) → F₂) :
    dotProduct u (twoStartRhs L) =
      twoStartCompleteBoundary L u
          (Sum.inl (startRootVertex L)) +
        twoStartCompleteBoundary L u
          (Sum.inr (startRootVertex L)) := by
  rw [dotProduct, Fintype.sum_sum_type]
  change
    (∑ i : Fin L, u (Sum.inl i) * startRhs L i) +
        (∑ i : Fin L, u (Sum.inr i) * startRhs L i) =
      startCompleteBoundary L (fun i => u (Sum.inl i))
          (startRootVertex L) +
        startCompleteBoundary L (fun i => u (Sum.inr i))
          (startRootVertex L)
  rw [startCompleteBoundary_root_eq_dot_startRhs,
    startCompleteBoundary_root_eq_dot_startRhs]

/-- The paper's affine bit `d_{i,j}` on one exact unit.-/
def channelUnitAffineBit
    {L a b : ℕ} {h : ℤ} (unit : ChannelUnit L a b h) : F₂ :=
  (if channelVertexOffset unit.1.1 = -1 then 1 else 0) +
    if channelVertexOffset unit.1.2 = -1 then 1 else 0

/-- Linear character on unit selections induced by the two root indicators.-/
def channelAffineCharacter
    (L a b : ℕ) (h : ℤ) :
    (ChannelUnit L a b h → F₂) →ₗ[F₂] F₂ :=
  Fintype.linearCombination F₂ channelUnitAffineBit

/--
@isnad1 id=eq.0h5v.s8.8892a14b4be1 from=translated src=- shape=af1dfb9d vocab=2485c536
-/
@[simp]
theorem channelAffineCharacter_apply
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂) :
    channelAffineCharacter L a b h c =
      ∑ unit : ChannelUnit L a b h,
        c unit * channelUnitAffineBit unit := by
  simp [channelAffineCharacter, Fintype.linearCombination_apply,
    smul_eq_mul]

/--
@isnad1 id=iff.0h2v.s5.20014342e4b1 from=translated src=- shape=2557df57 vocab=70ffdd18
-/
theorem channelVertexOffset_eq_neg_one_iff
    {L : ℕ} (v : Fin (L + 1)) :
    channelVertexOffset v = -1 ↔ v = startRootVertex L := by
  constructor
  · intro hv
    apply Fin.ext
    simp only [channelVertexOffset] at hv
    simp only [startRootVertex]
    omega
  · rintro rfl
    simp [channelVertexOffset, startRootVertex]

/--
@isnad1 id=eq.0h1v.s4.717a66739392 from=translated src=- shape=d0627bb1 vocab=35e247ee
-/
@[simp]
theorem channelVertexOffset_startRootVertex (L : ℕ) :
    channelVertexOffset (startRootVertex L) = -1 := by
  simp [channelVertexOffset, startRootVertex]

/--
@isnad1 id=eq.0h5v.s10.94a7011290ba from=translated src=- shape=36731993 vocab=c30aa73d
-/
theorem leftUnitBoundary_root
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂) :
    leftUnitBoundary L a b h c (startRootVertex L) =
      ∑ unit : ChannelUnit L a b h,
        c unit *
          (if channelVertexOffset unit.1.1 = -1 then 1 else 0) := by
  classical
  simp only [leftUnitBoundary_apply]
  apply Finset.sum_congr rfl
  intro unit _hunit
  by_cases hoff : channelVertexOffset unit.1.1 = -1
  · have hv :
        unit.1.1 = startRootVertex L :=
      (channelVertexOffset_eq_neg_one_iff unit.1.1).mp hoff
    simp [hoff, hv, Pi.single_apply]
  · have hv :
        unit.1.1 ≠ startRootVertex L := by
      intro hv
      exact hoff
        ((channelVertexOffset_eq_neg_one_iff unit.1.1).mpr hv)
    simp [hoff, hv, Pi.single_apply]

/--
@isnad1 id=eq.0h5v.s10.ea5422be3358 from=translated src=- shape=36731993 vocab=306671ea
-/
theorem rightUnitBoundary_root
    {L a b : ℕ} {h : ℤ}
    (c : ChannelUnit L a b h → F₂) :
    rightUnitBoundary L a b h c (startRootVertex L) =
      ∑ unit : ChannelUnit L a b h,
        c unit *
          (if channelVertexOffset unit.1.2 = -1 then 1 else 0) := by
  classical
  simp only [rightUnitBoundary_apply]
  apply Finset.sum_congr rfl
  intro unit _hunit
  by_cases hoff : channelVertexOffset unit.1.2 = -1
  · have hv :
        unit.1.2 = startRootVertex L :=
      (channelVertexOffset_eq_neg_one_iff unit.1.2).mp hoff
    simp [hoff, hv, Pi.single_apply]
  · have hv :
        unit.1.2 ≠ startRootVertex L := by
      intro hv
      exact hoff
        ((channelVertexOffset_eq_neg_one_iff unit.1.2).mpr hv)
    simp [hoff, hv, Pi.single_apply]

/--
The affine relation character restricted to the rational code is exactly the
root-boundary vector `d_{i,j} = 1_{i=-1} + 1_{j=-1}`.
@isnad1 id=eq.5h8v.s13.79ddf05094b7 from=translated src=- shape=3d2614fc vocab=5620c060
-/
theorem relationCharacter_rationalRelationMap
    {M x y L a b : ℕ} {h : ℤ}
    (ha : 0 < a) (hb : 0 < b)
    (hx : 2 ≤ x) (hy : 2 ≤ y)
    (hheight : h = (b : ℤ) * y - (a : ℤ) * x)
    (c : EvenChannelSelection L a b h) :
    relationCharacter
        (twoStartSystem M x y L) (twoStartRhs L)
        (rationalRelationMap M x y L a b h
          ha hb hx hy hheight c) =
      channelAffineCharacter L a b h
        (c : ChannelUnit L a b h → F₂) := by
  rw [relationCharacter_apply,
    rationalRelationMap_coe,
    dotProduct_twoStartRhs_eq_boundary_roots,
    twoStartCompleteBoundary_channelRelationCoefficients_inl,
    twoStartCompleteBoundary_channelRelationCoefficients_inr,
    leftUnitBoundary_root, rightUnitBoundary_root,
    channelAffineCharacter_apply,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro unit _hunit
  simp only [channelUnitAffineBit]
  ring

end

end RationalChannelCode
end Affine
end PaperC
