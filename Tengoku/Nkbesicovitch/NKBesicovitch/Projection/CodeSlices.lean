/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CodeMarginal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Slicing a code fiber at the second base height

For fixed first-line position and code, the second line's slope is fixed. The
remaining common positions form a translate of a parallel fiber of the line family.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- The common-position mass with the first line's second-base position fixed.-/
noncomputable def codeSliceMass (a b c : ℝ) (W : Set (PairCoordinates m))
    (z y : EuclideanSpace ℝ (Fin m)) : ℝ≥0∞ :=
  ∫⁻ w, W.indicator 1 (pairFromCode a b c (lineAt a w ((b - a)⁻¹ • (y - w))) z)

/--
@isnad1 id=eq.1h5v.s7.4a5574ebe918 from=translated src=- shape=1b68871d vocab=1405aa00
-/
theorem atHeight_lineAt_of_positions {a b : ℝ} (hab : a ≠ b) (w y : EuclideanSpace ℝ (Fin m)) :
    atHeight b (lineAt a w ((b - a)⁻¹ • (y - w))) = y := by
  simp [atHeight_lineAt, smul_smul, mul_inv_cancel₀ (sub_ne_zero.mpr hab.symm)]

/--
@isnad1 id=other.1h7v.s8.4d8f9eda1a08 from=translated src=- shape=a12c7e46 vocab=ee49a5de
-/
theorem second_pairFromCode_of_positions {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    (w y z : EuclideanSpace ℝ (Fin m)) :
    let p := pairFromCode a b c (lineAt a w ((b - a)⁻¹ • (y - w))) z
    lineAt a p.1 p.2.2 = lineAt a w ((b - a)⁻¹ • (z - c • y)) := by
  dsimp only [pairFromCode]
  rw [atHeight_lineAt_of_positions hab]
  simp [atHeight_lineAt]

/--
@isnad1 id=measurab.1h6v.s7.23efa48d29f4 from=translated src=- shape=fd742cae vocab=33fe5b55
-/
theorem measurable_codeSliceMass (a b c : ℝ) {W : Set (PairCoordinates m)}
    (hW : MeasurableSet W) (z : EuclideanSpace ℝ (Fin m)) : Measurable
      (codeSliceMass a b c W z) := by
  have hF : Continuous (fun p : Line m ↦
      pairFromCode a b c (lineAt a p.1 ((b - a)⁻¹ • (p.2 - p.1))) z) := by
    unfold pairFromCode lineAt atHeight
    fun_prop
  exact ((measurable_const.indicator hW).comp hF.measurable).lintegral_prod_left'

/--
@isnad1 id=eq.2h6v.s8.3b9a2c2851ac from=translated src=- shape=31bd4f13 vocab=746f3aef
-/
theorem codeDensity_eq_lintegral_codeSliceMass {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {W : Set (PairCoordinates m)} (hW : MeasurableSet W) (z : EuclideanSpace ℝ (Fin m)) :
    codeDensity a b c W z = codeJacobian m a b ^ 2 * ∫⁻ y, codeSliceMass a b c W z y := by
  simpa only [pow_two, codeJacobian, codeSliceMass] using
    codeDensity_eq_twoSlice_lintegral hab.symm c hW z

/--
@isnad1 id=le.2h8v.s9.0826d8db1d7f from=translated src=- shape=f71b8b82 vocab=c1e9369a
-/
theorem codeSliceMass_le_parallelFiber {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hWG : W ⊆ pairFamily a G)
    (z y : EuclideanSpace ℝ (Fin m)) :
    codeSliceMass a b c W z y ≤ volume {x : EuclideanSpace ℝ (Fin m) | (x,
      (b - a)⁻¹ • (z - c • y)) ∈ G} := by
  let ξ := (b - a)⁻¹ • (z - c • y)
  let S : Set (EuclideanSpace ℝ (Fin m)) := {w | lineAt a w ξ ∈ G}
  calc
    _ ≤ ∫⁻ w, S.indicator 1 w := by
      apply lintegral_mono
      intro w
      dsimp only
      by_cases hp : pairFromCode a b c (lineAt a w ((b - a)⁻¹ • (y - w))) z ∈ W
      · have hg := (hWG hp).2
        rw [second_pairFromCode_of_positions hab] at hg
        rw [Set.indicator_of_mem hp, Set.indicator_of_mem (show w ∈ S from hg)]
        exact le_rfl
      · simp [Set.indicator_of_notMem hp]
    _ ≤ volume S := lintegral_indicator_one_le S
    _ = _ := by
      change volume ((fun w : EuclideanSpace ℝ (Fin m) ↦ w + -(a • ξ)) ⁻¹' {x | (x, ξ) ∈ G}) = _
      exact measure_preimage_add_right volume (-(a • ξ)) _

/--
@isnad1 id=le.2h7v.s6.9a894f1bba5d from=translated src=- shape=6c7c3d26 vocab=045e9c44
-/
theorem support_codeSliceMass_subset {a b : ℝ} (hab : a ≠ b) (c : ℝ)
    {G : Set (Line m)} {W : Set (PairCoordinates m)} (hWG : W ⊆ pairFamily a G)
    (z : EuclideanSpace ℝ (Fin m)) : Function.support
      (codeSliceMass a b c W z) ⊆ atHeight b '' G := by
  intro y hy
  by_contra h
  have hz (w : EuclideanSpace ℝ (Fin m)) : pairFromCode a b c
    (lineAt a w ((b - a)⁻¹ • (y - w))) z ∉ W := by
    intro hp
    have hg := (hWG hp).1
    rw [first_pairFromCode] at hg
    exact h ⟨_, hg, atHeight_lineAt_of_positions hab w y⟩
  exact hy (by simp [codeSliceMass, Set.indicator_of_notMem, hz])

end NKBesicovitch.Projection
