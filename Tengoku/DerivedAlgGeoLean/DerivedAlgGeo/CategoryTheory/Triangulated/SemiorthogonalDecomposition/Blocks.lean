/-
Copyright (c) 2026 Chris Dare. All rights reserved.
Released under the MIT license.
-/
import Tengoku.DerivedAlgGeoLean.DerivedAlgGeo.CategoryTheory.Triangulated.SemiorthogonalDecomposition.Collection
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Data.Fintype.BigOperators

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Orthogonal blocks of exceptional objects

This file records the categorical part of the block-shaped semiorthogonal
decompositions used in arXiv:2104.13610v2, Proposition 1.4 and Setup 2.5.
Each block is an ordered exceptional collection; distinct blocks are
completely orthogonal after taking their triangulated spans.  The geometry
which produces the objects or relates consecutive objects by chains of
`(-2)`-curves does not belong in this generic root.

The span of a block is the triangulated envelope of the union of its
one-object components.  This is important: the union itself need not be
closed under extensions.  The residual property is the right orthogonal of
the union of these spans, matching the convention already used by
`SemiorthogonalSequence.residual`.
-/

open CategoryTheory

universe w v u t

namespace CategoryTheory.Triangulated

open Limits

namespace ExceptionalCollection

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {ι : Type t} [Preorder ι]

/-- The full triangulated span of an exceptional collection.-/
abbrev span (E : ExceptionalCollection k C ι) : ObjectProperty C :=
  E.toSemiorthogonalSequence.total.triangEnvelope

/-- Every member of an exceptional collection belongs to its full span.
@isnad1 id=span.0h5v.s6.b89004a784bd from=translated src=- shape=105e44f3 vocab=33e00a34
-/
theorem obj_mem_span (E : ExceptionalCollection k C ι) (i : ι) :
    E.span (E.obj i) := by
  apply ObjectProperty.le_triangEnvelope
  exact E.toSemiorthogonalSequence.component_le_total
    (OrderDual.toDual i) (E.obj i) (E.obj_mem_component i)

/-- The span of a nonempty exceptional collection is triangulated.
@isnad1 id=istriang.0h4v.s6.647c4ab361c9 from=translated src=- shape=22723404 vocab=4ea54262
-/
theorem span_isTriangulated [Nonempty ι] [IsTriangulated C]
    (E : ExceptionalCollection k C ι) : E.span.IsTriangulated := by
  haveI : E.toSemiorthogonalSequence.total.Nonempty := by
    let i : ι := Classical.choice (inferInstance : Nonempty ι)
    exact ⟨E.obj i, E.toSemiorthogonalSequence.component_le_total
      (OrderDual.toDual i) (E.obj i) (E.obj_mem_component i)⟩
  infer_instance

end ExceptionalCollection

variable (k : Type w) [Field k] (C : Type u) [Category.{v} C]
  [Preadditive C] [Linear k C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable (ι : Type t)

/-- A family of mutually orthogonal exceptional blocks.

The field `orthogonal` is written in the right-orthogonal convention:
`blockSpan i ≤ (blockSpan j).rightOrthogonal` says that maps from block
`j` to block `i` vanish.  Since the field is available for every ordered pair
of distinct indices, it records orthogonality in both directions.-/
structure OrthogonalExceptionalBlocks where
  /-- The positive length of each block.-/
  length : ι → ℕ
  /-- Blocks are nonempty.-/
  length_pos : ∀ i, 0 < length i
  /-- The exceptional collection inside each block.-/
  collection : ∀ i, ExceptionalCollection k C (Fin (length i))
  /-- Distinct block spans are completely orthogonal.-/
  orthogonal : ∀ {i j}, i ≠ j →
    (collection i).span ≤ ((collection j).span).rightOrthogonal

namespace OrthogonalExceptionalBlocks

variable {k : Type w} [Field k] {C : Type u} [Category.{v} C]
  [Preadditive C] [Linear k C] [Limits.HasZeroObject C] [HasShift C ℤ]
  [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
variable {ι : Type t}
variable (B : OrthogonalExceptionalBlocks k C ι)

/-- The first position in a block, available because block lengths are
positive.-/
def firstIndex (i : ι) : Fin (B.length i) :=
  ⟨0, B.length_pos i⟩

/-- The first exceptional object in a block.-/
abbrev firstObject (i : ι) : C :=
  (B.collection i).obj (B.firstIndex i)

/-- The triangulated span of one exceptional block.-/
abbrev blockSpan (i : ι) : ObjectProperty C :=
  (B.collection i).span

/-- The union of all block spans.  Its right orthogonal defines the residual
property below.-/
def total : ObjectProperty C :=
  ⨆ i, B.blockSpan i

/-- The residual object property of the block decomposition.-/
def residual : ObjectProperty C :=
  B.total.rightOrthogonal

/-- The full subcategory on the residual property.-/
abbrev ResidualCategory :=
  B.residual.FullSubcategory

/-- Every member of a block belongs to that block's span.
@isnad1 id=blockspa.0h6v.s7.b791528eb89d from=translated src=- shape=29d94949 vocab=3fe8c19c
-/
theorem obj_mem_blockSpan (i : ι) (j : Fin (B.length i)) :
    B.blockSpan i ((B.collection i).obj j) :=
  (B.collection i).obj_mem_span j

/-- Every member of every block belongs to the total exceptional part.
@isnad1 id=total.0h6v.s7.7752fb333ba1 from=translated src=- shape=c01e1512 vocab=71de4036
-/
theorem obj_mem_total (i : ι) (j : Fin (B.length i)) :
    B.total ((B.collection i).obj j) :=
  le_iSup B.blockSpan i _ (B.obj_mem_blockSpan i j)

/-- To prove that the total exceptional part lies in a triangulated,
retract-closed property, it suffices to check every member of every block.
@isnad1 id=le.0h6v.s7.11b2838104d5 from=translated src=- shape=f5a5dcc0 vocab=26da778c
-/
theorem total_le_of_forall_obj
    {P : ObjectProperty C} [P.IsTriangulated] [P.IsStableUnderRetracts]
    (hP : ∀ (i : ι) (j : Fin (B.length i)),
      P ((B.collection i).obj j)) :
    B.total ≤ P := by
  rw [total]
  apply iSup_le
  intro i
  change (B.collection i).toSemiorthogonalSequence.total.triangEnvelope ≤ P
  rw [ObjectProperty.triangEnvelope_le_iff]
  rw [SemiorthogonalSequence.total]
  apply iSup_le
  intro j
  change (ObjectProperty.shiftClosure
    (fun X : C ↦ X = (B.collection i).obj j) ℤ).triangEnvelope ≤ P
  rw [ObjectProperty.triangEnvelope_le_iff]
  rw [ObjectProperty.shiftClosure_le_iff]
  intro X hX
  subst X
  exact hP i j

/-- A positive block length is either one or at least two.
@isnad1 id=or.0h5v.s6.dd323bd53aea from=translated src=- shape=b57697bd vocab=e0fc49e4
-/
theorem length_eq_one_or_two_le (i : ι) :
    B.length i = 1 ∨ 2 ≤ B.length i := by
  have := B.length_pos i
  omega

/-- Maps between distinct block spans vanish in either direction.
@isnad1 id=eq.1h11v.s7.e007f4cce9e9 from=translated src=- shape=ff58cd5a vocab=6feb8a2a
-/
theorem hom_eq_zero_of_ne {i j : ι} (hij : i ≠ j) {X Y : C}
    (hX : B.blockSpan i X) (hY : B.blockSpan j Y) (f : X ⟶ Y) :
    f = 0 :=
  B.orthogonal (i := j) (j := i) (Ne.symm hij) Y hY f hX

/-- Maps between members of distinct exceptional blocks vanish.
@isnad1 id=eq.1h10v.s9.9ee986762828 from=translated src=- shape=edc4fb9e vocab=5a0e243d
-/
theorem obj_hom_shift_eq_zero_of_ne {i j : ι} (hij : i ≠ j)
    (a : Fin (B.length i)) (b : Fin (B.length j)) (n : ℤ)
    (f : (B.collection i).obj a ⟶ ((B.collection j).obj b)⟦n⟧) :
    f = 0 := by
  apply B.hom_eq_zero_of_ne hij (B.obj_mem_blockSpan i a)
  exact (B.blockSpan j).le_shift n _ (B.obj_mem_blockSpan j b)

/-- The blocks as a root-oriented semiorthogonal sequence.  Because distinct
blocks are orthogonal, any preorder on their indices is permitted.-/
def toSemiorthogonalSequence [Preorder ι] : SemiorthogonalSequence C ι where
  component := B.blockSpan
  semiorthogonal := by
    intro i j hij
    exact B.orthogonal (i := j) (j := i) (ne_of_gt hij)

/--
@isnad1 id=eq.0h5v.s6.151f2f651ba4 from=translated src=- shape=7a8abb10 vocab=d727935a
-/
@[simp]
theorem toSemiorthogonalSequence_component [Preorder ι] (i : ι) :
    B.toSemiorthogonalSequence.component i = B.blockSpan i :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.7f011eb292b5 from=translated src=- shape=6d3fc110 vocab=998f476a
-/
@[simp]
theorem toSemiorthogonalSequence_total [Preorder ι] :
    B.toSemiorthogonalSequence.total = B.total :=
  rfl

/--
@isnad1 id=eq.0h4v.s6.b4fe70d62d49 from=translated src=- shape=6d3fc110 vocab=9904fcae
-/
@[simp]
theorem toSemiorthogonalSequence_residual [Preorder ι] :
    B.toSemiorthogonalSequence.residual = B.residual :=
  rfl

/-- Every block span is triangulated.
@isnad1 id=istriang.0h5v.s6.c1cc452171e9 from=translated src=- shape=65372199 vocab=9c090277
-/
theorem blockSpan_isTriangulated [IsTriangulated C] (i : ι) :
    (B.blockSpan i).IsTriangulated := by
  letI : Nonempty (Fin (B.length i)) := ⟨B.firstIndex i⟩
  exact (B.collection i).span_isTriangulated

/-- The block sequence has triangulated components.
@isnad1 id=hastrian.0h4v.s6.3f88177a6f6e from=translated src=- shape=d2ed4358 vocab=fbaec7c4
-/
theorem hasTriangulatedComponents [Preorder ι] [IsTriangulated C] :
    B.toSemiorthogonalSequence.HasTriangulatedComponents :=
  B.blockSpan_isTriangulated

/-- The union of the block spans is stable under every integral shift.
@isnad1 id=isstable.0h4v.s6.c23622ac3002 from=translated src=- shape=29a913f9 vocab=1439ee41
-/
theorem total_isStableUnderShift :
    B.total.IsStableUnderShift ℤ := by
  letI (i : ι) : (B.blockSpan i).IsStableUnderShift ℤ := by
    change (B.collection i).span.IsStableUnderShift ℤ
    infer_instance
  constructor
  intro n
  constructor
  intro X hX
  change B.total (X⟦n⟧)
  rw [total, ObjectProperty.prop_iSup_iff] at hX ⊢
  obtain ⟨i, hi⟩ := hX
  exact ⟨i, (B.blockSpan i).le_shift n X hi⟩

/-- The residual property of orthogonal exceptional blocks is triangulated.
@isnad1 id=istriang.0h4v.s6.2ef6ad2dbea0 from=translated src=- shape=c8534cff vocab=8a9ac843
-/
theorem residual_isTriangulated :
    B.residual.IsTriangulated := by
  letI : B.total.IsStableUnderShift ℤ := B.total_isStableUnderShift
  change B.total.rightOrthogonal.IsTriangulated
  infer_instance

/-- Maps from any block object to a residual object vanish.
@isnad1 id=eq.0h9v.s8.22260d7436dc from=translated src=- shape=652a1cc8 vocab=1c753762
-/
theorem obj_hom_residual_eq_zero (i : ι) (j : Fin (B.length i))
    {R : C} (hR : B.residual R)
    (f : (B.collection i).obj j ⟶ R) : f = 0 :=
  hR f (B.obj_mem_total i j)

section Finite

variable [Fintype ι]

/-- The total number of exceptional objects across all blocks.-/
def totalLength : ℕ :=
  ∑ i, B.length i

/-- The unordered block-length sequence, i.e. the type of the block-shaped
decomposition in the terminology of arXiv:2104.13610v2, Definition 1.5.-/
noncomputable def decompositionType : Multiset ℕ :=
  (Finset.univ : Finset ι).val.map B.length

/--
@isnad1 id=eq.0h4v.s6.ce93a174c1f1 from=translated src=- shape=099781b1 vocab=31e5863d
-/
@[simp]
theorem decompositionType_card : B.decompositionType.card = Fintype.card ι := by
  simp [decompositionType]

/--
@isnad1 id=eq.0h4v.s6.6d004d131e22 from=translated src=- shape=50bb2290 vocab=789b275b
-/
@[simp]
theorem decompositionType_sum : B.decompositionType.sum = B.totalLength := by
  simp [decompositionType, totalLength]

/-- The number of blocks is bounded by the total number of exceptional
objects.
@isnad1 id=le.0h4v.s6.f3e6ec738701 from=translated src=- shape=70128a3d vocab=00c60f2e
-/
theorem card_le_totalLength : Fintype.card ι ≤ B.totalLength := by
  rw [totalLength, ← Finset.card_univ, Finset.card_eq_sum_ones]
  exact Finset.sum_le_sum fun i _ ↦ B.length_pos i

end Finite

end OrthogonalExceptionalBlocks

end CategoryTheory.Triangulated
