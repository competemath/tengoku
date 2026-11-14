import Tengoku.TdaLib.TDA.Persistence.PersistenceMeasureContent
import Tengoku.TdaLib.TDA.Persistence.DecoratedRectangleTopology
import Tengoku.TdaLib.TDA.Persistence.DecoratedCutEndpoints
import Tengoku.TdaLib.TDA.Persistence.IntegerContentAtoms
import Tengoku.Seed.Topology.Homeomorph.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Canonical decorated multiplicities from a q-tame module

Minimum containing-rectangle contents define the module's finite-death decorated
multiplicity. Compact open cut cells yield finite support in every separated rectangle
and exact reconstruction of every rectangle quotient dimension. No interval decomposition
or diagram-existence certificate is supplied as input. Essential boundary points and
algebraic stability are separate results.
-/

universe u w

namespace TDA.Persistence.RectangleMeasure

open Set MeasureTheory
open scoped Classical

private theorem exists_cutPair_topology :
    ∃ t : TopologicalSpace (Cut ℝ × Cut ℝ),
      (∀ U ∈ separatedRectangleCells, @IsOpen _ t U) ∧
      (∀ U ∈ separatedRectangleCells, @IsCompact _ t U) := by
  let : TopologicalSpace (LowerSet ℝ) := Preorder.topology _
  let : OrderTopology (LowerSet ℝ) := ⟨rfl⟩
  let : TopologicalSpace (Cut ℝ × Cut ℝ) :=
    TopologicalSpace.induced rectangleLowerSetEquiv inferInstance
  let e := (rectangleLowerSetEquiv (α := ℝ)).toHomeomorphOfIsInducing ⟨rfl⟩
  refine ⟨inferInstance, ?_, ?_⟩
  · rintro U (rfl | ⟨a, b, c, d, _, _, _, rfl⟩)
    · exact isOpen_empty
    · exact e.isOpen_image.mp (isOpen_image_rectangleCell a b c d)
  · rintro U (rfl | ⟨a, b, c, d, _, _, _, rfl⟩)
    · exact isCompact_empty
    · exact e.isCompact_image.mp (isCompact_image_rectangleCell a b c d)

private theorem separatedRectangleCells_separate {K : Set (Cut ℝ × Cut ℝ)}
    (hK : K ∈ separatedRectangleCells) (x : Cut ℝ × Cut ℝ) (hx : x ∈ K)
    (y : Cut ℝ × Cut ℝ) (hxy : x ≠ y) :
    ∃ U ∈ separatedRectangleCells, x ∈ U ∧ y ∉ U := by
  rcases hK with rfl | ⟨a, b, c, d, _, hbc, _, rfl⟩
  · exact hx.elim
  · exact exists_rectangleCell_separating hxy hbc hx

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

/-- Canonical finite-death decorated multiplicity, extracted from the module's actual
rectangle content by a minimum over containing rectangles.-/
noncomputable def moduleDiagramMultiplicity (hM : M.QTame) (p : Cut ℝ × Cut ℝ) : ℕ :=
  contentMultiplicity (moduleRectangleContent M hM) p

/-- No positive multiplicity is assigned to a point invisible to every separated rectangle.
@isnad1 id=eq.2h3v.s6.c05c351b3ef1 from=translated src=- shape=2cf1e4a6 vocab=d0e95110
-/
theorem moduleDiagramMultiplicity_eq_zero_of_not_visible (hM : M.QTame)
    (p : Cut ℝ × Cut ℝ) (hp : ¬ ∃ U ∈ separatedRectangleCells, p ∈ U) :
    moduleDiagramMultiplicity M hM p = 0 := by
  have hempty : {n | ∃ U ∈ separatedRectangleCells, p ∈ U ∧
      moduleRectangleContent M hM U = n} = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro n ⟨U, hU, hpU, _⟩
    exact hp ⟨U, hU, hpU⟩
  simp only [moduleDiagramMultiplicity, contentMultiplicity, hempty, Nat.sInf_empty]

/-- Every positive finite-death diagram point is seen by an actual separated rectangle.
@isnad1 id=ex.2h3v.s6.3c11a3c072a4 from=translated src=- shape=9e25a052 vocab=b0dffd15
-/
theorem moduleDiagramMultiplicity_visible_of_pos (hM : M.QTame)
    {p : Cut ℝ × Cut ℝ} (hp : 0 < moduleDiagramMultiplicity M hM p) :
    ∃ U ∈ separatedRectangleCells, p ∈ U := by
  by_contra hn
  have hz := moduleDiagramMultiplicity_eq_zero_of_not_visible M hM p hn
  omega

/-- Positive finite-death diagram points have strictly ordered finite numeric endpoints.
@isnad1 id=lt.2h3v.s6.c8f945e10051 from=translated src=- shape=f3e1725a vocab=20295b9b
-/
theorem moduleDiagramMultiplicity_endpoints_lt (hM : M.QTame)
    {p : Cut ℝ × Cut ℝ} (hp : 0 < moduleDiagramMultiplicity M hM p) :
    cutEndpoint p.1 < cutEndpoint p.2 := by
  obtain ⟨U, hU, hpU⟩ := moduleDiagramMultiplicity_visible_of_pos M hM hp
  rcases hU with rfl | ⟨a, b, c, d, _, hbc, _, rfl⟩
  · exact hpU.elim
  · exact cutEndpoint_lt_of_mem_rectangleCell hbc hpU

/-- Every containing cell bounds the extracted multiplicity by its actual module content.
@isnad1 id=le.3h4v.s7.db4c4d918236 from=translated src=- shape=898ee9a9 vocab=f65f9e24
-/
theorem moduleDiagramMultiplicity_le_content (hM : M.QTame)
    {K : Set (Cut ℝ × Cut ℝ)} (hK : K ∈ separatedRectangleCells)
    {p : Cut ℝ × Cut ℝ} (hp : p ∈ K) :
    moduleDiagramMultiplicity M hM p ≤ moduleRectangleContent M hM K :=
  contentMultiplicity_le _ hK hp

/-- A positive rectangle content produces an actual positive decorated point.
@isnad1 id=ex.3h3v.s7.3fd4026ffaf7 from=translated src=- shape=59e16986 vocab=5af7046d
-/
theorem exists_moduleDiagram_atom_of_positive (hM : M.QTame)
    {K : Set (Cut ℝ × Cut ℝ)} (hK : K ∈ separatedRectangleCells)
    (hpos : 0 < moduleRectangleContent M hM K) :
    ∃ p ∈ K, 0 < moduleDiagramMultiplicity M hM p := by
  obtain ⟨t, hOpen, hCompact⟩ := exists_cutPair_topology
  let := t
  exact exists_positive_content_atom isSetSemiring_separatedRectangleCells
    (moduleRectangleContent M hM) hOpen hK (hCompact K hK) hpos

/-- Positive decorated multiplicities have finite support in each separated rectangle.
@isnad1 id=finite.2h3v.s6.d82bcb58efe8 from=translated src=- shape=87392e9e vocab=975e0590
-/
theorem moduleDiagramMultiplicity_locally_finite (hM : M.QTame)
    {K : Set (Cut ℝ × Cut ℝ)} (hK : K ∈ separatedRectangleCells) :
    Set.Finite {p | p ∈ K ∧ 0 < moduleDiagramMultiplicity M hM p} := by
  obtain ⟨t, hOpen, hCompact⟩ := exists_cutPair_topology
  let := t
  exact finite_positive_content_support isSetSemiring_separatedRectangleCells
    (moduleRectangleContent M hM) hOpen (separatedRectangleCells_separate hK) hK (hCompact K hK)

/-- The constructed multiplicities reproduce each cell's actual module content exactly.
@isnad1 id=ex.2h3v.s7.3720e7922bbe from=translated src=- shape=20978140 vocab=46d17c38
-/
theorem moduleDiagramMultiplicity_content_counts (hM : M.QTame)
    {K : Set (Cut ℝ × Cut ℝ)} (hK : K ∈ separatedRectangleCells) :
    ∃ S : Finset (Cut ℝ × Cut ℝ),
      (∀ p, p ∈ S ↔ p ∈ K ∧ 0 < moduleDiagramMultiplicity M hM p) ∧
      moduleRectangleContent M hM K = ∑ p ∈ S, moduleDiagramMultiplicity M hM p := by
  obtain ⟨t, hOpen, hCompact⟩ := exists_cutPair_topology
  let := t
  exact content_eq_sum_multiplicity isSetSemiring_separatedRectangleCells
    (moduleRectangleContent M hM) hOpen (separatedRectangleCells_separate hK) hK (hCompact K hK)

/-- Every strict separated persistence rectangle counts exactly the constructed decorated
point multiplicities it contains.
@isnad1 id=ex.4h6v.s7.7c9e90a42de2 from=translated src=- shape=b6891942 vocab=51ae3c38
-/
theorem moduleDiagramMultiplicity_rectangle_counts (hM : M.QTame) (a b c d : ℝ)
    (hab : a < b) (hbc : b < c) (hcd : c < d) :
    ∃ S : Finset (Cut ℝ × Cut ℝ),
      (∀ p, p ∈ S ↔ p ∈ rectangleCell a b c d ∧ 0 < moduleDiagramMultiplicity M hM p) ∧
      persistenceMeasureValue M hab.le hbc.le hcd.le =
        ∑ p ∈ S, moduleDiagramMultiplicity M hM p := by
  obtain ⟨S, hS, hcount⟩ := moduleDiagramMultiplicity_content_counts M hM
    (rectangleCell_mem_separatedRectangleCells a b c d hbc)
  exact ⟨S, hS, (moduleRectangleContent_apply M hM a b c d hab hbc hcd).symm.trans hcount⟩

/-- Modules with zero separated rectangle counts have zero extracted finite-death diagram.
@isnad1 id=eq.2h3v.s6.05fae547e4b6 from=translated src=- shape=36b1a0d1 vocab=abf9f87e
-/
theorem moduleDiagramMultiplicity_eq_zero_of_rectangle_zero (hM : M.QTame)
    (hzero : ∀ (a b c d : ℝ) (hab : a < b) (hbc : b < c) (hcd : c < d),
      persistenceMeasureValue M hab.le hbc.le hcd.le = 0) (p : Cut ℝ × Cut ℝ) :
    moduleDiagramMultiplicity M hM p = 0 := by
  by_contra hne
  have hpos := Nat.pos_of_ne_zero hne
  obtain ⟨U, hU, hpU⟩ := moduleDiagramMultiplicity_visible_of_pos M hM hpos
  rcases hU with rfl | ⟨a, b, c, d, hab, hbc, hcd, rfl⟩
  · exact hpU.elim
  · have hle := moduleDiagramMultiplicity_le_content M hM
      (rectangleCell_mem_separatedRectangleCells a b c d hbc) hpU
    rw [moduleRectangleContent_apply M hM a b c d hab hbc hcd,
      hzero a b c d hab hbc hcd] at hle
    omega

end TDA.Persistence.RectangleMeasure
