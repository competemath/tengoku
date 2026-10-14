/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Parabolic.Basic
public import Tengoku

/-!
# Density and pairing helpers for Euclidean `Lᵖ`

This file records the approximation facts used when an operator is first
defined on its `L²` carrier and then extended to lower exponents.  The
approximants are continuous and compactly supported; in particular they are
in every finite `Lᵖ` space.  The pairing estimates are stated in the real
integral form supplied by Hölder's inequality, which is convenient when
passing a distributional identity to the limit.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology

noncomputable section

namespace CKN.Foundation.Euclidean

open CKN.Foundation.Parabolic

/-- Hölder's estimate for the pairing against a fixed `Lq` test function.
@isnad1 id=le.3h4v.s9.0fbf254f4398 from=translated src=- shape=f93cfe3a vocab=8f7feb37
-/
theorem integral_mul_test_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {g ψ : Vec3 → ℝ} (hg : MemLp g (ENNReal.ofReal p) volume)
    (hψ : MemLp ψ (ENNReal.ofReal q) volume) :
    ‖∫ x, g x * ψ x‖ ≤
      (∫ x, ‖g x‖ ^ p) ^ (1 / p) *
        (∫ x, ‖ψ x‖ ^ q) ^ (1 / q) := by
  have hp : 0 < p := hpq.left_pos
  have hq : 0 < q := hpq.right_pos
  let _ : (ENNReal.ofReal p).HolderTriple (ENNReal.ofReal q) 1 :=
    ENNReal.HolderTriple.of_toReal (by
      simpa [ENNReal.toReal_ofReal hp.le, ENNReal.toReal_ofReal hq.le] using hpq)
  have hmul : Integrable (fun x => g x * ψ x) volume := by
    exact hg.integrable_mul hψ
  calc
    ‖∫ x, g x * ψ x‖ ≤ ∫ x, ‖g x * ψ x‖ :=
      norm_integral_le_integral_norm _
    _ = ∫ x, ‖g x‖ * ‖ψ x‖ := by
      apply integral_congr_ae
      filter_upwards [] with x
      simp only [norm_mul]
    _ ≤ _ := integral_mul_norm_le_Lp_mul_Lq hpq hg hψ

/-- Hölder's estimate for the difference of two pairings against a fixed
`Lq` test function.  This is the quantitative `Lᵖ` continuity used in the
distributional limit.
@isnad1 id=le.4h5v.s9.de3c93860214 from=translated src=- shape=4e594c89 vocab=a19dc50d
-/
theorem integral_mul_test_sub_le {p q : ℝ} (hpq : p.HolderConjugate q)
    {g h ψ : Vec3 → ℝ} (hg : MemLp g (ENNReal.ofReal p) volume)
    (hh : MemLp h (ENNReal.ofReal p) volume)
    (hψ : MemLp ψ (ENNReal.ofReal q) volume) :
    ‖∫ x, (g x - h x) * ψ x‖ ≤
      (∫ x, ‖(g x - h x)‖ ^ p) ^ (1 / p) *
        (∫ x, ‖ψ x‖ ^ q) ^ (1 / q) := by
  exact integral_mul_test_le hpq (hg.sub hh) hψ

/-- The pairing estimate when the test is continuous and compactly supported.
Such a test is automatically in every finite `Lq` space.
@isnad1 id=le.4h4v.s9.86e20ef4f3d1 from=translated src=- shape=ad0e7dc4 vocab=585446a9
-/
theorem integral_mul_continuousCompactSupport_le {p q : ℝ}
    (hpq : p.HolderConjugate q) {g ψ : Vec3 → ℝ}
    (hg : MemLp g (ENNReal.ofReal p) volume) (hψc : Continuous ψ)
    (hψs : HasCompactSupport ψ) :
    ‖∫ x, g x * ψ x‖ ≤
      (∫ x, ‖g x‖ ^ p) ^ (1 / p) *
        (∫ x, ‖ψ x‖ ^ q) ^ (1 / q) := by
  exact integral_mul_test_le hpq hg (hψc.memLp_of_hasCompactSupport hψs)

end CKN.Foundation.Euclidean
