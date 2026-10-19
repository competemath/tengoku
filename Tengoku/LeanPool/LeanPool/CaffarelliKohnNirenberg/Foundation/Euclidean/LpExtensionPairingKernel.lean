/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.LpExtensionPairing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Lp Extension Pairing Kernel

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic
open CKN.Foundation.Heat

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- A function in `L^p` with compact support is integrable.

The compact support confines the function to a finite-measure set, where the
`L^p` membership with `p ≥ 1` yields integrability, and integrability on the
support is equivalent to integrability on the whole space.  This is the
integrability input for the pairing identities of `cor:CZ-harmonic`. -/
theorem integrable_of_memLp_hasCompactSupport {p : ℝ≥0∞} (hp : 1 ≤ p)
    {G : Vec3 → ℝ} (hG : MemLp G p volume) (hGc : HasCompactSupport G) :
    Integrable G volume := by
  have hfin : IsFiniteMeasure (volume.restrict (tsupport G)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hGc.measure_lt_top⟩
  exact (integrableOn_iff_integrable_of_support_subset (subset_tsupport G)).mp
    (MemLp.integrable hp (hG.restrict (tsupport G)))

end CKN.Foundation.Euclidean
