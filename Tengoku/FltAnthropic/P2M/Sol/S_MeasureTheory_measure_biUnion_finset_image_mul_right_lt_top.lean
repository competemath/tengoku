import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MeasureTheory_measure_biUnion_finset_image_mul_right_lt_top

set_option autoImplicit false

open MeasureTheory

theorem solution
    {G : Type*} [Group G] [MeasurableSpace G] [MeasurableMul G] (μ : Measure G) [μ.IsMulRightInvariant]
    (s : Set G) (hs : μ s < ⊤) (T : Finset G) :
    μ (⋃ x ∈ T, (· * x) '' s) < ⊤ := by
  refine lt_of_le_of_lt (measure_biUnion_finset_le T _) ?_
  refine ENNReal.sum_lt_top.mpr fun x _ => ?_
  have : (· * x) '' s = (· * x⁻¹) ⁻¹' s := by
    ext g; simp [Set.mem_preimage]
  rw [this, measure_preimage_mul_right]
  exact hs
