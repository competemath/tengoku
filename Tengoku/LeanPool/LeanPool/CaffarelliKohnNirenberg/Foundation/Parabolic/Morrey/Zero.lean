/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Statements.MorreyVecMem

/-!
# Zero

Part of the Caffarelli–Kohn–Nirenberg partial regularity proof.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Metric
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

/-! # Parabolic Morrey quantities of the zero function

This module records the cylinder and ball power integrals, Morrey cells and Morrey
seminorms of the zero function.
-/

noncomputable section

namespace CKN.Foundation.Parabolic.Morrey

/-- The cylinder power integral of the zero function vanishes at every centre and radius.
@isnad1 id=eq.1h3v.s5.0d399eb41514 from=translated src=- shape=c2fe7e18 vocab=23e74e45
-/
theorem cylinderPowerIntegral_zero {p : ℝ} (hp : 0 < p) (z : ParabolicPoint) (r : ℝ) :
    cylinderPowerIntegral p (fun _ => (0 : ℝ)) z r = 0 := by
  unfold cylinderPowerIntegral
  simp only [abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp, lintegral_zero]

/-- The ball power integral of the zero function vanishes at every centre and radius.
@isnad1 id=eq.1h3v.s5.19cad93ad073 from=translated src=- shape=c2fe7e18 vocab=4b1bdef3
-/
theorem ballPowerIntegral_zero {p : ℝ} (hp : 0 < p) (z : ParabolicPoint) (r : ℝ) :
    ballPowerIntegral p (fun _ => (0 : ℝ)) z r = 0 := by
  unfold ballPowerIntegral
  simp only [abs_zero, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_pos hp, lintegral_zero]

/-- The Morrey cell quantity of the zero function vanishes at every centre and radius.
@isnad1 id=eq.1h4v.s5.a6ed6198fee1 from=translated src=- shape=77c819d8 vocab=750040a6
-/
theorem morreyCell_zero {p q : ℝ} (hp : 0 < p) (z : ParabolicPoint) (r : ℝ) :
    morreyCell p q (fun _ => (0 : ℝ)) z r = 0 := by
  unfold morreyCell
  rw [cylinderPowerIntegral_zero hp z r]
  have hone_div_pos : 0 < 1 / p := one_div_pos.mpr hp
  rw [ENNReal.zero_rpow_of_pos hone_div_pos]
  simp

/-- The Morrey ball cell quantity of the zero function vanishes at every centre and radius.
@isnad1 id=eq.1h4v.s5.42cd98aa29ac from=translated src=- shape=77c819d8 vocab=396b53c5
-/
theorem morreyBallCell_zero {p q : ℝ} (hp : 0 < p) (z : ParabolicPoint) (r : ℝ) :
    morreyBallCell p q (fun _ => (0 : ℝ)) z r = 0 := by
  unfold morreyBallCell
  rw [ballPowerIntegral_zero hp z r]
  have hone_div_pos : 0 < 1 / p := one_div_pos.mpr hp
  rw [ENNReal.zero_rpow_of_pos hone_div_pos]
  simp

/-- The Morrey norm of the zero function vanishes identically.
@isnad1 id=eq.1h2v.s5.fd27cd691e91 from=translated src=- shape=d5af5dde vocab=5509a487
-/
theorem morreyNorm_zero {p q : ℝ} (hp : 0 < p) :
    morreyNorm p q (fun _ => (0 : ℝ)) = 0 := by
  unfold morreyNorm
  apply le_antisymm
  · refine iSup_le fun z => iSup_le fun r => ?_
    rw [morreyCell_zero hp z r.1]
  · simp

/-- The Morrey ball norm of the zero function vanishes identically.
@isnad1 id=eq.1h2v.s5.48a9ddddde1b from=translated src=- shape=d5af5dde vocab=f82aae85
-/
theorem morreyBallNorm_zero {p q : ℝ} (hp : 0 < p) :
    morreyBallNorm p q (fun _ => (0 : ℝ)) = 0 := by
  unfold morreyBallNorm
  apply le_antisymm
  · refine iSup_le fun z => iSup_le fun r => ?_
    rw [morreyBallCell_zero hp z r.1]
  · simp

end CKN.Foundation.Parabolic.Morrey
