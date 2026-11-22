/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Euclidean.NewtonianDerivativeLocalLp

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Potential Local Lp Exponents

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter Metric
open scoped BigOperators ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN

/-- Data supported in a closed ball and of class `L^q` is of class `L^p` for every `p ≤ q`.
@isnad1 id=memlp.3h4v.s8.dc5514c07c8b from=translated src=- shape=05c0fe79 vocab=e2110cd0
-/
theorem memLp_of_memLp_of_support_closedBall {G : Vec3 → ℝ} {R : ℝ} {p q : ℝ≥0∞}
    (hpq : p ≤ q) (hG : MemLp G q volume)
    (hzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) R → G y = 0) :
    MemLp G p volume :=
  hG.mono_exponent_of_measure_support_ne_top hzero measure_closedBall_lt_top.ne hpq

/-- The `L^(6/5)` instance used by the Young estimate for the Newtonian potential: compactly
supported data of class `L^q` with `6 / 5 ≤ q` is of class `L^(6/5)`.
@isnad1 id=memlp.3h3v.s8.32b101e2f057 from=translated src=- shape=f885b1e5 vocab=4c4009b6
-/
theorem memLp_six_fifths_of_memLp_ofReal {G : Vec3 → ℝ} {R q : ℝ} (hq : 6 / 5 ≤ q)
    (hG : MemLp G (ENNReal.ofReal q) volume)
    (hzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) R → G y = 0) :
    MemLp G (ENNReal.ofReal (6 / 5 : ℝ)) volume :=
  memLp_of_memLp_of_support_closedBall
    (p := ENNReal.ofReal (6 / 5 : ℝ)) (q := ENNReal.ofReal q)
    (ENNReal.ofReal_le_ofReal hq) hG hzero

/-- Compactly supported data of class `L^q` with `1 ≤ q` is integrable.
@isnad1 id=integrab.3h3v.s8.ce2a49d05d9d from=translated src=- shape=acc195d1 vocab=d7c4de3d
-/
theorem integrable_of_memLp_ofReal_of_support {G : Vec3 → ℝ} {R q : ℝ} (hq : 1 ≤ q)
    (hG : MemLp G (ENNReal.ofReal q) volume)
    (hzero : ∀ y, y ∉ Metric.closedBall (0 : Vec3) R → G y = 0) :
    Integrable G volume :=
  memLp_one_iff_integrable.1
    (memLp_of_memLp_of_support_closedBall (p := (1 : ℝ≥0∞)) (q := ENNReal.ofReal q)
      (ENNReal.one_le_ofReal.2 hq) hG hzero)

end CKN.Foundation.Euclidean
