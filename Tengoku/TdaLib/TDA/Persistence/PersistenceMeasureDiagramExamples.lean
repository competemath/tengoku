import Tengoku.TdaLib.TDA.Persistence.PersistenceMeasureDiagram
import Tengoku.TdaLib.TDA.Persistence.PersistenceMeasureExamples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# An actual module produces a nonzero decorated diagram point

The existing interval module `[0,2)` has one rectangle occurrence. The construction
extracts a decorated point of multiplicity one from its actual module content.
-/

universe u

namespace TDA.Persistence.RectangleMeasure

open Set
open scoped Classical

variable {k : Type u} [Field k]

private theorem exampleInterval_qTame (p : ℝ × WithTop ℝ) :
    (RealBarcode.intervalModule (k := k) p).QTame :=
  PModule.qTame_of_finiteDimensional _ (fun t => by
    change FiniteDimensional k (RealBarcode.fiber (k := k) p t)
    infer_instance)

/-- The module-to-content-to-multiplicity construction extracts an actual unit atom.
@isnad1 id=ex.0h1v.s6.3d2b0f88fb0b from=translated src=- shape=91dd92d2 vocab=bcd25bca
-/
theorem interval_has_decorated_unit_atom :
    ∃ p ∈ rectangleCell (-1 : ℝ) 0 1 2,
      moduleDiagramMultiplicity
        (RealBarcode.intervalModule (k := k) (0, (2 : WithTop ℝ)))
        (exampleInterval_qTame _) p = 1 := by
  let M := RealBarcode.intervalModule (k := k) (0, (2 : WithTop ℝ))
  have hM := exampleInterval_qTame (k := k) (0, (2 : WithTop ℝ))
  have hK : rectangleCell (-1 : ℝ) 0 1 2 ∈ separatedRectangleCells :=
    rectangleCell_mem_separatedRectangleCells _ _ _ _ (by norm_num)
  have hcount : moduleRectangleContent M hM (rectangleCell (-1 : ℝ) 0 1 2) = 1 := by
    rw [moduleRectangleContent_apply M hM _ _ _ _ (by norm_num) (by norm_num) (by norm_num)]
    exact PersistenceMeasureExamples.upper_edges_count_one
  obtain ⟨p, hpK, hp⟩ := exists_moduleDiagram_atom_of_positive M hM hK (by omega)
  have hle := moduleDiagramMultiplicity_le_content M hM hK hpK
  refine ⟨p, hpK, ?_⟩
  change moduleDiagramMultiplicity M hM p = 1
  omega

/-- The existing module with infinite-dimensional ephemeral fibers really extracts to zero.
@isnad1 id=eq.0h2v.s4.03b4180fcd53 from=translated src=- shape=fb7ff15a vocab=0c4f5651
-/
theorem infinite_ephemeral_extracted_diagram_zero (p : Cut ℝ × Cut ℝ) :
    moduleDiagramMultiplicity _
      (PersistenceMeasureExamples.infinite_ephemeral_qTame (k := k)) p = 0 := by
  apply moduleDiagramMultiplicity_eq_zero_of_rectangle_zero
  intro a b c d hab hbc hcd
  exact PersistenceMeasureExamples.infinite_ephemeral_rectangle_zero hab.le hbc hcd.le

end TDA.Persistence.RectangleMeasure
