import Tengoku.TdaLib.TDA.Persistence.PersistenceMeasureLowerBound
import Tengoku.TdaLib.TDA.Persistence.PersistenceMeasureExamples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact essential atom of an actual interval module

The essential interval `[0,∞)` yields exactly the minus birth cut at zero and the infinite
death cut. Its zero negative tail fixes the birth coordinate and decoration. Every point
with finite death has zero multiplicity.
-/

universe u

namespace TDA.Persistence.RectangleMeasure

open Set CategoryTheory.Limits
open scoped Classical

variable {k : Type u} [Field k]

private theorem interval_qTame (p : ℝ × WithTop ℝ) :
    (RealBarcode.intervalModule (k := k) p).QTame :=
  PModule.qTame_of_finiteDimensional _ (fun t => by
    change FiniteDimensional k (RealBarcode.fiber (k := k) p t)
    infer_instance)

private theorem interval_zero_below_zero (d : WithTop ℝ) (t : ℝ) (ht : t < 0) :
    IsZero ((RealBarcode.intervalModule (k := k) (0, d)).obj t) := by
  apply ModuleCat.isZero_iff_subsingleton.mpr
  change Subsingleton (RealBarcode.fiber (k := k) (0, d) t)
  have hn : ¬ RealBarcode.alive (0, d) t := fun h => not_le_of_gt ht h.1
  have hbot : RealBarcode.fiber (k := k) (0, d) t = (⊥ : Submodule k k) := by
    unfold RealBarcode.fiber
    exact ite_eq_right hn
  rw [hbot]
  infer_instance

/-- The actual essential interval extracts the unit atom at its exact decorated coordinates.
@isnad1 id=eq.0h1v.s5.47442e601b59 from=translated src=- shape=4ffeb739 vocab=5207c2a9
-/
theorem essential_interval_exact_boundary_atom :
    moduleExtendedDiagramMultiplicity (RealBarcode.intervalModule (k := k) (0, ⊤))
      (interval_qTame _) (minusCut 0, infinityCut) = 1 := by
  let M := RealBarcode.intervalModule (k := k) (0, (⊤ : WithTop ℝ))
  have hM := interval_qTame (k := k) (0, (⊤ : WithTop ℝ))
  have hK : cutCell (-1 : ℝ) 0 ∈ cutCells := cutCell_mem_cutCells _ _
  have hcount : essentialCutContent M hM (cutCell (-1 : ℝ) 0) = 1 := by
    rw [essentialCutContent_apply M hM (show (-1 : ℝ) ≤ 0 by norm_num)]
    exact PersistenceMeasureExamples.essential_interval_count_one
  obtain ⟨birth, hbK, hbpos⟩ := exists_moduleEssential_atom_of_positive M hM hK (by omega)
  have hle := moduleEssentialMultiplicity_le_content M hM hK hbK
  have hbunit : moduleExtendedDiagramMultiplicity M hM (birth, infinityCut) = 1 := by
    rw [moduleExtendedDiagramMultiplicity_infinity]
    omega
  have hlower := moduleExtendedDiagramMultiplicity_birth_lower_bound M hM 0
    (interval_zero_below_zero (k := k) ⊤) (p := (birth, infinityCut)) (by omega)
  have hupper := (cutEndpoint_bounds hbK).2
  have hEndpoint : cutEndpoint birth = 0 := le_antisymm hupper hlower
  have hbirth : birth = minusCut 0 := by
    rcases cut_eq_minus_or_plus_of_mem_cutCell hbK with hm | hp
    · simpa only [hEndpoint] using hm
    · have heq : birth = plusCut 0 := by simpa only [hEndpoint] using hp
      have hu := hbK.2
      rw [heq] at hu
      norm_num [plusCut] at hu
  change moduleExtendedDiagramMultiplicity M hM (minusCut 0, infinityCut) = 1
  rw [← hbirth]
  exact hbunit

/-- The essential interval has no extracted finite-death point.
@isnad1 id=eq.1h2v.s5.72f8e1e95a80 from=translated src=- shape=b0102054 vocab=084b7aec
-/
theorem essential_interval_no_finite_death_atom (p : Cut ℝ × Cut ℝ) (hp : p.2 ≠ infinityCut) :
    moduleExtendedDiagramMultiplicity (RealBarcode.intervalModule (k := k) (0, ⊤))
      (interval_qTame _) p = 0 := by
  rw [moduleExtendedDiagramMultiplicity, ite_eq_right hp]
  apply moduleDiagramMultiplicity_eq_zero_of_rectangle_zero
  intro a b c d hab hbc hcd
  exact PersistenceMeasureExamples.essential_interval_finite_rectangle_zero hab.le hbc.le hcd.le

end TDA.Persistence.RectangleMeasure
