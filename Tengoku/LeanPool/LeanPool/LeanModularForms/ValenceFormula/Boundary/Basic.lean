/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.LeanPool.LeanPool.LeanModularForms.ValenceFormula.Definitions
import Tengoku.Seed.CategoryTheory.Category.Init

namespace LeanPoolFork

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fundamental Domain Boundary – Basic Definitions

Definitions and continuity for the boundary of the standard fundamental domain
for SL₂(ℤ), both at fixed height `heightCutoff` and at variable height `H`.

## Main Definitions

* `heightCutoff` — fixed cutoff height (√3/2 + 1)
* `fdBoundary` — 5-segment boundary at fixed height
* `fdBoundaryH` — 5-segment boundary at variable height H
* `fdPartition` — interior partition points
* `fdBoundaryFullPartition` — full partition including endpoints
* `fdBoundaryHPartition` — partition for H-parameterized boundary
* `seg5QRadiusH` — q-expansion radius e^(-2πH)
-/

@[expose] public section

open Complex MeasureTheory Set Filter Topology
open scoped Real Interval

noncomputable section

/-- Height cutoff for the finite-height fundamental domain boundary. -/
def heightCutoff : ℝ := Real.sqrt 3 / 2 + 1

/--
@isnad1 id=lt.0h0v.s3.5032c1ed8fe0 from=translated src=- shape=ff3a10fc vocab=e0c887aa
-/
lemma one_lt_heightCutoff : 1 < heightCutoff := by
  unfold heightCutoff; linarith [Real.sqrt_pos_of_pos (show (3 : ℝ) > 0 by norm_num)]

/--
@isnad1 id=lt.0h0v.s4.baecaa94901a from=translated src=- shape=9e62e5be vocab=75b40ff6
-/
lemma sqrt3_div2_lt_heightCutoff :
    Real.sqrt 3 / 2 < heightCutoff := by unfold heightCutoff; linarith

/-- Segment 1: right vertical from (1/2 + H·i) down to ρ+1. -/
def fdBoundarySeg1 : ℝ → ℂ := fun t =>
  1 / 2 + (heightCutoff - t * (heightCutoff - Real.sqrt 3 / 2)) * I

/-- Segment 2: arc from ρ+1 to i (angle π/3 → π/2). -/
def fdBoundarySeg2 : ℝ → ℂ := fun t =>
  Complex.exp ((Real.pi / 3 + (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)

/-- Segment 3: arc from i to ρ (angle π/2 → 2π/3). -/
def fdBoundarySeg3 : ℝ → ℂ := fun t =>
  Complex.exp ((Real.pi / 2 + (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)

/-- Segment 4: left vertical from ρ up to (-1/2 + H·i). -/
def fdBoundarySeg4 : ℝ → ℂ := fun t =>
  -1 / 2 + (Real.sqrt 3 / 2 + (t - 3) * (heightCutoff - Real.sqrt 3 / 2)) * I

/-- Segment 5: horizontal from (-1/2 + H·i) to (1/2 + H·i). -/
def fdBoundarySeg5 : ℝ → ℂ := fun t =>
  (t - 9 / 2) + heightCutoff * I

/-- Boundary of the standard fundamental domain at fixed
height `heightCutoff`, parameterized over [0, 5]. -/
def fdBoundary : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    1 / 2 +
      (heightCutoff - t * (heightCutoff - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    Complex.exp
      ((Real.pi / 3 +
        (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  else if t ≤ 3 then
    Complex.exp
      ((Real.pi / 2 +
        (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  else if t ≤ 4 then
    -1 / 2 +
      (Real.sqrt 3 / 2 +
        (t - 3) * (heightCutoff - Real.sqrt 3 / 2)) * I
  else
    (t - 9 / 2) + heightCutoff * I

/-- Interior partition points of fdBoundary. -/
def fdPartition : Finset ℝ := {1, 2, 3, 4}

/-- Full partition including endpoints. -/
def fdBoundaryFullPartition : Finset ℝ := {0, 1, 2, 3, 4, 5}

/--
@isnad1 id=eq.0h0v.s5.83ac8a2e756d from=translated src=- shape=0977d038 vocab=ba86cfb7
-/
lemma fdBoundary_at_zero :
    fdBoundary 0 = 1 / 2 + heightCutoff * I := by
  simp only [fdBoundary, show (0 : ℝ) ≤ 1 from by norm_num, ite_true]
  push_cast; ring

/--
@isnad1 id=eq.0h0v.s3.5e0724debe35 from=translated src=- shape=d3a93718 vocab=af7ecb1e
-/
lemma fdBoundary_at_one :
    fdBoundary 1 = ellipticPointRhoPlusOne := by
  simp only [fdBoundary, show (1 : ℝ) ≤ 1 from le_refl _, ite_true,
    ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
    UpperHalfPlane.coe_mk, heightCutoff]
  push_cast; ring

/--
@isnad1 id=eq.0h0v.s3.06178c128e75 from=translated src=- shape=d3a93718 vocab=cf35ba05
-/
lemma fdBoundary_at_two :
    fdBoundary 2 = ellipticPointI := by
  simp only [fdBoundary, show ¬(2 : ℝ) ≤ 1 from by norm_num,
    show (2 : ℝ) ≤ 2 from le_refl _, ite_true, ite_false]
  have h : (↑Real.pi / 3 + (↑(2 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 2) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp [ellipticPointI, ellipticPointI']

/--
@isnad1 id=eq.0h0v.s3.bfdc00db35ce from=translated src=- shape=d3a93718 vocab=12ad31aa
-/
lemma fdBoundary_at_three :
    fdBoundary 3 = ellipticPointRho := by
  simp only [fdBoundary, show ¬(3 : ℝ) ≤ 1 from by norm_num,
    show ¬(3 : ℝ) ≤ 2 from by norm_num, show (3 : ℝ) ≤ 3 from le_refl _,
    ite_true, ite_false]
  have h : (↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  ring

/--
@isnad1 id=eq.0h0v.s5.2307362ecb17 from=translated src=- shape=20726076 vocab=5e20b9b3
-/
lemma fdBoundary_at_four :
    fdBoundary 4 = -1 / 2 + heightCutoff * I := by
  simp only [fdBoundary, show ¬(4 : ℝ) ≤ 1 from by norm_num,
    show ¬(4 : ℝ) ≤ 2 from by norm_num, show ¬(4 : ℝ) ≤ 3 from by norm_num,
    show (4 : ℝ) ≤ 4 from le_refl _, ite_true, ite_false, heightCutoff]
  push_cast; ring

/--
@isnad1 id=eq.0h0v.s5.ab3db8ba03ec from=translated src=- shape=0977d038 vocab=ba86cfb7
-/
lemma fdBoundary_at_five :
    fdBoundary 5 = 1 / 2 + heightCutoff * I := by
  simp only [fdBoundary, show ¬(5 : ℝ) ≤ 1 from by norm_num,
    show ¬(5 : ℝ) ≤ 2 from by norm_num, show ¬(5 : ℝ) ≤ 3 from by norm_num,
    show ¬(5 : ℝ) ≤ 4 from by norm_num, ite_false]
  push_cast; ring

/--
@isnad1 id=eq.0h0v.s4.c38fc477529c from=translated src=- shape=31c619a8 vocab=f10d9633
-/
lemma fdBoundary_closed : fdBoundary 0 = fdBoundary 5 := by
  rw [fdBoundary_at_zero, fdBoundary_at_five]

/-- Segment 1 at height H: right vertical from (1/2 + H·i) down
to ρ+1. -/
def fdBoundarySeg1H (H : ℝ) : ℝ → ℂ := fun t =>
  1 / 2 + (H - t * (H - Real.sqrt 3 / 2)) * I

/-- Segment 2 at height H (H-independent): arc from ρ+1 to i. -/
def fdBoundarySeg2H : ℝ → ℂ := fdBoundarySeg2

/-- Segment 3 at height H (H-independent): arc from i to ρ. -/
def fdBoundarySeg3H : ℝ → ℂ := fdBoundarySeg3

/-- Segment 4 at height H: left vertical from ρ up to (-1/2 + H·i). -/
def fdBoundarySeg4H (H : ℝ) : ℝ → ℂ := fun t =>
  -1 / 2 + (Real.sqrt 3 / 2 + (t - 3) * (H - Real.sqrt 3 / 2)) * I

/-- Segment 5 at height H: horizontal from (-1/2 + H·i) to (1/2 + H·i). -/
def fdBoundarySeg5H (H : ℝ) : ℝ → ℂ := fun t => (t - 9 / 2) + H * I

/-- Boundary of the standard fundamental domain at variable height H,
parameterized over [0, 5]. -/
def fdBoundaryH (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 1 then
    1 / 2 + (H - t * (H - Real.sqrt 3 / 2)) * I
  else if t ≤ 2 then
    Complex.exp
      ((Real.pi / 3 +
        (t - 1) * (Real.pi / 2 - Real.pi / 3)) * I)
  else if t ≤ 3 then
    Complex.exp
      ((Real.pi / 2 +
        (t - 2) * (2 * Real.pi / 3 - Real.pi / 2)) * I)
  else if t ≤ 4 then
    -1 / 2 +
      (Real.sqrt 3 / 2 +
        (t - 3) * (H - Real.sqrt 3 / 2)) * I
  else
    (t - 9 / 2) + H * I

/-- Non-differentiable corner points of fdBoundaryH (excluding smooth
transitions at t = 2). -/
def fdBoundaryHPartition : Finset ℝ := {1, 3, 4}

/-- The q-expansion radius at height H: e^(-2πH). -/
def seg5QRadiusH (H : ℝ) : ℝ := Real.exp (-2 * Real.pi * H)

/--
@isnad1 id=eq.0h0v.s2.91719d7e8fc4 from=translated src=- shape=54fd580d vocab=7ac63c4e
-/
theorem fdBoundary_eq_fdBoundary_H :
    fdBoundary = fdBoundaryH heightCutoff := by
  ext t; simp only [fdBoundary, fdBoundaryH, heightCutoff]

/--
@isnad1 id=eq.0h1v.s5.6a0001e9e28e from=translated src=- shape=ec367fbd vocab=12615c05
-/
lemma fdBoundary_H_at_zero (H : ℝ) :
    fdBoundaryH H 0 = 1 / 2 + H * I := by
  simp only [fdBoundaryH, show (0 : ℝ) ≤ 1 from by norm_num, ite_true]
  push_cast; ring

/--
@isnad1 id=eq.0h1v.s3.572ca794581f from=translated src=- shape=a62063d2 vocab=3f77cbca
-/
lemma fdBoundary_H_at_one (H : ℝ) :
    fdBoundaryH H 1 = ellipticPointRhoPlusOne := by
  simp only [fdBoundaryH, show (1 : ℝ) ≤ 1 from le_refl _, ite_true,
    ellipticPointRhoPlusOne, ellipticPointRhoPlusOne',
    UpperHalfPlane.coe_mk]
  push_cast; ring

/--
@isnad1 id=eq.0h1v.s3.eadc0133ff55 from=translated src=- shape=a62063d2 vocab=89d1152d
-/
lemma fdBoundary_H_at_two (H : ℝ) :
    fdBoundaryH H 2 = ellipticPointI := by
  simp only [fdBoundaryH, show ¬(2 : ℝ) ≤ 1 from by norm_num,
    show (2 : ℝ) ≤ 2 from le_refl _, ite_true, ite_false]
  have h : (↑Real.pi / 3 + (↑(2 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 2) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_two, Real.sin_pi_div_two]
  simp [ellipticPointI, ellipticPointI']

/--
@isnad1 id=eq.0h1v.s3.534f645d986e from=translated src=- shape=a62063d2 vocab=10e149af
-/
lemma fdBoundary_H_at_three (H : ℝ) :
    fdBoundaryH H 3 = ellipticPointRho := by
  simp only [fdBoundaryH, show ¬(3 : ℝ) ≤ 1 from by norm_num,
    show ¬(3 : ℝ) ≤ 2 from by norm_num, show (3 : ℝ) ≤ 3 from le_refl _,
    ite_true, ite_false]
  have h : (↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  simp [ellipticPointRho, ellipticPointRho', UpperHalfPlane.coe_mk]
  ring

/--
@isnad1 id=eq.0h1v.s5.b81d8166cc4d from=translated src=- shape=a0bf8e68 vocab=98735cb0
-/
lemma fdBoundary_H_at_four (H : ℝ) :
    fdBoundaryH H 4 = -1 / 2 + H * I := by
  simp only [fdBoundaryH, show ¬(4 : ℝ) ≤ 1 from by norm_num,
    show ¬(4 : ℝ) ≤ 2 from by norm_num, show ¬(4 : ℝ) ≤ 3 from by norm_num,
    show (4 : ℝ) ≤ 4 from le_refl _, ite_true, ite_false]
  push_cast; ring

/--
@isnad1 id=eq.0h1v.s5.a9613aceffd6 from=translated src=- shape=ec367fbd vocab=12615c05
-/
lemma fdBoundary_H_at_five (H : ℝ) :
    fdBoundaryH H 5 = 1 / 2 + H * I := by
  simp only [fdBoundaryH, show ¬(5 : ℝ) ≤ 1 from by norm_num,
    show ¬(5 : ℝ) ≤ 2 from by norm_num, show ¬(5 : ℝ) ≤ 3 from by norm_num,
    show ¬(5 : ℝ) ≤ 4 from by norm_num, ite_false]
  push_cast; ring

/--
@isnad1 id=eq.0h1v.s4.a1d0f68d350c from=translated src=- shape=b4d3c9b0 vocab=9241e0f7
-/
lemma fdBoundary_H_closed (H : ℝ) :
    fdBoundaryH H 0 = fdBoundaryH H 5 := by rw [fdBoundary_H_at_zero, fdBoundary_H_at_five]

private lemma fdBoundary_H_seg1_cont (H : ℝ) :
    Continuous (fun t : ℝ => (1 : ℂ) / 2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I) :=
  (continuous_const.add ((continuous_const.sub
    (Complex.continuous_ofReal.mul continuous_const)).mul continuous_const))

private lemma fdBoundary_H_seg23_cont :
    Continuous (fun t : ℝ => exp
      ((↑Real.pi / 3 + (↑t - 1) *
        (↑Real.pi / 2 - ↑Real.pi / 3)) * I)) :=
  Complex.continuous_exp.comp ((continuous_const.add
    ((Complex.continuous_ofReal.sub continuous_const).mul continuous_const)).mul continuous_const)

private lemma fdBoundary_H_seg23b_cont :
    Continuous (fun t : ℝ => exp
      ((↑Real.pi / 2 + (↑t - 2) *
        (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)) :=
  Complex.continuous_exp.comp ((continuous_const.add
    ((Complex.continuous_ofReal.sub continuous_const).mul continuous_const)).mul continuous_const)

private lemma fdBoundary_H_seg4_cont (H : ℝ) :
    Continuous (fun t : ℝ =>
      (-1 : ℂ) / 2 + (↑(Real.sqrt 3) / 2 +
        (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I) :=
  (continuous_const.add ((continuous_const.add
    ((Complex.continuous_ofReal.sub continuous_const).mul continuous_const)).mul continuous_const))

private lemma fdBoundary_H_seg5_cont (H : ℝ) :
    Continuous (fun t : ℝ => (↑t - 9 / 2 : ℂ) + ↑H * I) :=
  (Complex.continuous_ofReal.sub continuous_const).add continuous_const

private def fdBoundary_H_inner34 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 4 then
    -1 / 2 + (↑(Real.sqrt 3) / 2 + (↑t - 3) * (↑H - ↑(Real.sqrt 3) / 2)) * I
  else (↑t - 9 / 2 : ℂ) + ↑H * I

private lemma fdBoundary_H_inner34_cont (H : ℝ) : Continuous (fdBoundary_H_inner34 H) :=
  Continuous.if_le (fdBoundary_H_seg4_cont H) (fdBoundary_H_seg5_cont H)
    continuous_id continuous_const (fun t (ht : t = 4) => by subst ht; push_cast; ring)

private def fdBoundary_H_inner234 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 3 then
    exp ((↑Real.pi / 2 + (↑t - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I)
  else fdBoundary_H_inner34 H t

private lemma fdBoundary_H_inner234_cont (H : ℝ) : Continuous (fdBoundary_H_inner234 H) := by
  apply Continuous.if_le fdBoundary_H_seg23b_cont
    (fdBoundary_H_inner34_cont H) continuous_id continuous_const
  intro t ht; simp only [id] at ht
  have : t = 3 := by linarith
  subst this; unfold fdBoundary_H_inner34
  simp only [show (3 : ℝ) ≤ 4 from by norm_num, ite_true]
  have h : (↑Real.pi / 2 + (↑(3 : ℝ) - 2) * (2 * ↑Real.pi / 3 - ↑Real.pi / 2)) * I =
      ↑(2 * Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    show (2 * Real.pi / 3 : ℝ) = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three, Real.sin_pi_sub, Real.sin_pi_div_three]
  push_cast; ring

private def fdBoundary_H_inner1234 (H : ℝ) : ℝ → ℂ := fun t =>
  if t ≤ 2 then
    exp ((↑Real.pi / 3 + (↑t - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I)
  else fdBoundary_H_inner234 H t

private lemma fdBoundary_H_inner1234_cont (H : ℝ) : Continuous (fdBoundary_H_inner1234 H) := by
  apply Continuous.if_le fdBoundary_H_seg23_cont
    (fdBoundary_H_inner234_cont H) continuous_id continuous_const
  intro t ht; simp only [id] at ht
  have : t = 2 := by linarith
  subst this; unfold fdBoundary_H_inner234
  simp only [show (2 : ℝ) ≤ 3 from by norm_num, ite_true]
  have h1 : (↑Real.pi / 3 + (↑(2 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 2) * I := by push_cast; ring
  simp_all

private lemma fdBoundary_H_eq_layered (H : ℝ) (t : ℝ) :
    fdBoundaryH H t =
      (if t ≤ 1 then 1 / 2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I
       else fdBoundary_H_inner1234 H t) := by
  unfold fdBoundaryH fdBoundary_H_inner1234 fdBoundary_H_inner234 fdBoundary_H_inner34
  split_ifs <;> rfl

/--
@isnad1 id=continuo.0h1v.s4.9e2edbadebf4 from=translated src=- shape=9bb0b988 vocab=8bf1852a
-/
theorem fdBoundary_H_continuous (H : ℝ) :
    Continuous (fdBoundaryH H) := by
  have : (fdBoundaryH H) = (fun t => if t ≤ 1 then
      1 / 2 + (↑H - ↑t * (↑H - ↑(Real.sqrt 3) / 2)) * I
      else fdBoundary_H_inner1234 H t) := by ext t; exact fdBoundary_H_eq_layered H t
  rw [this]
  apply Continuous.if_le (fdBoundary_H_seg1_cont H) (fdBoundary_H_inner1234_cont H)
    continuous_id continuous_const
  intro t ht; simp only [id] at ht
  have : t = 1 := by linarith
  subst this; unfold fdBoundary_H_inner1234
  simp only [show (1 : ℝ) ≤ 2 from by norm_num, ite_true]
  have h : (↑Real.pi / 3 + (↑(1 : ℝ) - 1) * (↑Real.pi / 2 - ↑Real.pi / 3)) * I =
      ↑(Real.pi / 3) * I := by push_cast; ring
  rw [h, exp_mul_I, ← ofReal_cos, ← ofReal_sin,
    Real.cos_pi_div_three, Real.sin_pi_div_three]
  push_cast; ring

end
