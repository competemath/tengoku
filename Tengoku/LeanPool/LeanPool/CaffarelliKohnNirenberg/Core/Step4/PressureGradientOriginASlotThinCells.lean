/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotLargeCellsGeometry
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals

/-! # From the common half-collar scale to every clipped cell

Bounds at closed carrier centres for radii at most `1/256` imply the
unrestricted clipped-cell bound. The explicit cover count is absorbed once
into the affine pressure coefficient.
-/

@[expose] public section

section

/-! # An absolute lattice cover for thin pressure collars

The doubled cells have radius `1/512`, below both prescribed half-collars.
The existing shifted-centre construction keeps every centre in the carrier.
-/

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- The lattice indices that a cell of radius `1/1024` can carry while
meeting the origin carrier of radius `R < 3/4`. -/
def originASlotThinCoverBox : Finset ((Fin 3 → ℤ) × ℤ) :=
  (Fintype.piFinset (fun _ : Fin 3 => Finset.Icc (-1538 : ℤ) 1538)) ×ˢ
    (Finset.Icc (-1179648 : ℤ) 2)

attribute [irreducible] originASlotThinCoverBox

end CKN.Core.Step4
end

end

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame
noncomputable section
namespace CKN.Core.Step4

/-- The Calderón–Zygmund threshold at which every clipped cell of the origin
carrier inherits the thin-cell A slot: the number of thin cells used to
cover the carrier, times the constant of the thin-cell estimate. -/
def originASlotThinCellThreshold (Cbase : ℝ) : ℝ :=
  34366557335620983 * (|Cbase| + 1)

/-- The threshold multiplies the affine slot by the cover count. -/
theorem originKPAffineASlot_thin_cover_count_mul_le {q ε Cbase C_CZ : ℝ} {KU KD : ℝ≥0∞}
    (hthreshold : originASlotThinCellThreshold Cbase ≤ C_CZ) :
    (34366557335620983 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD ≤
      originKPAffineASlot q C_CZ ε KU KD := by
  refine originKPAffineASlot_const_mul_le (by norm_num) ?_
  have hcast : (34366557335620983 : ℝ≥0∞) = ENNReal.ofReal (34366557335620983 : ℝ) := by
    rw [ENNReal.ofReal]
    norm_num
  rw [hcast, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have habs : C_CZ ≤ |C_CZ| := le_abs_self C_CZ
  have hth : 34366557335620983 * (|Cbase| + 1) ≤ C_CZ := hthreshold
  linarith only [habs, hth]

end CKN.Core.Step4
