/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginASlotLargeCellsGeometry
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Core.Step4.PressureGradientOriginCellInstanceTimeIntegrals

/-! # From margin cells to all cells in the origin A slot of `prop:bootstrap`

The clipped cell estimate of `prop:bootstrap` for the spatial pressure gradient
is proved directly only on *margin cells*: cells whose centre lies in the
closure of the origin carrier of radius `R₁` and whose radius is at most
`(1 - R₁)/4`.  This file removes both restrictions, at the cost of one absolute
factor on the Calderón–Zygmund constant.

The clipped time integral of the `6/5` power of the spatial `L^{6/5}` slice
norm is the space-time mass of `|∂ᵢp|^{6/5}` over the cell clipped to the
carrier, so it is monotone in the cell.  Two comparisons then suffice.

* A cell of radius at most `(1 - R₁)/8` clipped to the carrier is contained in
  a margin cell of twice the radius centred in the carrier.  Doubling the
  radius costs the factor `2^θ ≤ 8`, since the growth exponent `θ` of
  `prop:bootstrap` is at most `71/25`.
* A cell of radius larger than `(1 - R₁)/8` is bounded by the whole clipped
  carrier mass, and the carrier is covered by `197³ · 4611` margin cells of
  radius exactly `(1 - R₁)/8`, each of which is smaller than the given radius,
  so the growth factor only improves.

Both costs are absolute, and the affine slot `originKPAffineASlot` is
superhomogeneous in `|C_CZ| + 1`, so both are absorbed by requiring
`C_CZ ≥ originASlotLargeCellThreshold Cbase`.  Nothing else is assumed: the
centre of the given cell is arbitrary and its radius is arbitrary.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal NNReal BigOperators
open CKN.Foundation.Parabolic CKN.Foundation.Parabolic.Morrey
open CKN.Core.Endgame

noncomputable section
namespace CKN.Core.Step4

/-- The Calderón–Zygmund threshold at which every clipped cell of the origin
carrier inherits the margin-cell A slot: the number of margin cells used to
cover the carrier, times the constant of the margin-cell estimate. -/
def originASlotLargeCellThreshold (Cbase : ℝ) : ℝ :=
  35252814903 * (|Cbase| + 1)

/-- The threshold multiplies the affine slot by the cover count. -/
theorem originKPAffineASlot_cover_count_mul_le {q ε Cbase C_CZ : ℝ} {KU KD : ℝ≥0∞}
    (hthreshold : originASlotLargeCellThreshold Cbase ≤ C_CZ) :
    (35252814903 : ℝ≥0∞) * originKPAffineASlot q Cbase ε KU KD ≤
      originKPAffineASlot q C_CZ ε KU KD := by
  refine originKPAffineASlot_const_mul_le (by norm_num) ?_
  have hcast : (35252814903 : ℝ≥0∞) = ENNReal.ofReal (35252814903 : ℝ) := by
    rw [ENNReal.ofReal]
    norm_num
  rw [hcast, ← ENNReal.ofReal_mul (by norm_num)]
  refine ENNReal.ofReal_le_ofReal ?_
  have habs : C_CZ ≤ |C_CZ| := le_abs_self C_CZ
  have hth : 35252814903 * (|Cbase| + 1) ≤ C_CZ := hthreshold
  linarith only [habs, hth]

end CKN.Core.Step4
