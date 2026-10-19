/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.Potentials
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Pressure.LeibnizLaplacian

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Slice Selected Gradient Potential

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Core.Step4

/-! The pressure-gradient section of the paper controls `∇p` through the weak pairing
against a compactly supported test function, as in display (3.5).  The Newtonian
derivative potential of a source field is the kernel representation of that weak
gradient.  This file records the integrability input that display (3.5) assumes, the
local integrability of a finite sum of such potentials, and the passage from a
per-coordinate Calderón–Zygmund bound to the corresponding bound for the potential of
a vector-valued source. -/

/-- A function in `L^{6/5}` with compact support is integrable.  This is the
integrability input that display (3.5) of the pressure-gradient section takes for
granted: the source of the Newtonian derivative potential is supported on a compact
set of finite measure, so membership in `L^{6/5}` may be lowered to membership in
`L^1`. -/
theorem memLp_six_fifths_integrable_of_hasCompactSupport {G : Vec3 → ℝ}
    (hG : MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume) (hGc : HasCompactSupport G) :
    Integrable G volume := by
  rw [← memLp_one_iff_integrable]
  refine hG.mono_exponent_of_measure_support_ne_top (s := tsupport G) ?_ ?_ ?_
  · intro x hx
    exact image_eq_zero_of_notMem_tsupport hx
  · exact hGc.isCompact.measure_lt_top.ne
  · exact ENNReal.one_le_ofReal.2 (by norm_num)

end CKN.Core.Step4
