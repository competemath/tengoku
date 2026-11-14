import Tengoku.Piirrationalitymeasure.Formalization.SavingEndpoints

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Bounded-interval finiteness for endpoint slopes of either nonzero sign. -/

namespace PiIrrationality

open Set

theorem savingEndpoint_finite_on_interval_nonzero {a b c : ℝ} (z : ℝ × ℝ)
    (T : SavingEndpointType) (hT : savingEndpointSlope a b c T ≠ 0) (l r : ℝ) :
    (Set.range (savingEndpoint a b c z T) ∩ Icc l r).Finite := by
  rcases lt_or_gt_of_ne hT with hneg | hpos
  · let m := savingEndpointSlope a b c T
    let d := savingEndpointShift z T
    apply ((finite_Icc ⌈m * r + d⌉ ⌊m * l + d⌋).image
      (savingEndpoint a b c z T)).subset
    rintro u ⟨⟨j, rfl⟩, hu⟩
    have he := (savingEndpoint_eq_iff hT).mp
      (rfl : savingEndpoint a b c z T j = savingEndpoint a b c z T j)
    refine ⟨j, ⟨?_, ?_⟩, rfl⟩
    · apply Int.ceil_le.mpr
      have h := mul_le_mul_of_nonpos_left hu.2 hneg.le
      dsimp [m, d]
      linarith
    · apply Int.le_floor.mpr
      have h := mul_le_mul_of_nonpos_left hu.1 hneg.le
      dsimp [m, d]
      linarith
  · exact savingEndpoint_finite_on_interval z T hpos l r

theorem savingEndpoints_finite_on_interval_nonzero {a b c : ℝ} (z : ℝ × ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hq : a + 2 * b - c ≠ 0) (l r : ℝ) :
    (⋃ T, Set.range (savingEndpoint a b c z T) ∩ Icc l r).Finite := by
  apply Set.finite_iUnion
  intro T
  apply savingEndpoint_finite_on_interval_nonzero
  cases T <;> assumption

end PiIrrationality
