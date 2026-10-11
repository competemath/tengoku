/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.ClassEquivalence.BallCover
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Setting.ExtSobolevBallTime
public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.H1.Basic

/-!
# The velocity is locally `L^{10/3}`, hence locally `L³`

The data clauses of `def:sws` place the velocity in `L^∞_t L²_x ∩ L²_t H¹_x` on
every local box.  Two of the terms of the local energy inequality - the cubic
term `|u|² u · ∇ψ` and the pressure term `p u · ∇ψ` - are not integrable for a
field that is merely square integrable, so those two terms need the parabolic
interpolation

`L^∞_t L²_x ∩ L²_t homogeneous H¹_x ↪ L^{10/3}_{t,x}`,

which is the content of `CKN.ball_time_sobolev`.  This file turns that estimate
into the three local statements the energy inequality actually consumes: the
velocity is cubed-integrable, the pressure times the velocity is integrable, and
the force times the velocity is integrable, all on an arbitrary compact subset of
the space-time carrier.

Two features of the interpolation shape the file.

* It lives on Euclidean balls, because the spatial factor of a local box is an
  arbitrary open set and carries no Sobolev extension.  The reduction to balls is
  `CKN.exists_localBox_ball_cover_of_data`; the time factor of the box is used
  unchanged, since the interpolation accepts any order-connected time set.
* Its hypothesis on spatial slices asks for a genuine `CKN.H1Function` on the
  ball for almost every time.  The data clauses give an almost-everywhere weak
  gradient on the box and, after a slicing argument for the joint energy, an
  almost-everywhere square-integrable slice; those two are assembled here into
  the required slice representative and restricted to the ball.

Everything below takes `CKN.IsSuitableWeakSolutionData`, never the full class, so
these lemmas may be used while the integrability clauses of `def:sws` are still
being established.

The sup norm `‖·‖` of `Vec3` is the one the data clauses use, while the energy
density of the paper is the Euclidean norm `CKN.Foundation.Parabolic.vec3EuclideanNorm`.
Both comparisons needed here are the easy direction of the equivalence of the two
norms: a component is bounded by the sup norm on the way into the interpolation,
and the Euclidean norm is bounded by `√3` times the sup norm on the way out.
-/

@[expose] public section

open MeasureTheory MeasureTheory.Measure Set Filter
open scoped ENNReal NNReal Topology
open CKN.Foundation.Parabolic

noncomputable section

namespace CKN

variable {Ω : Set Vec3} {I : Set ℝ} {q : ℝ}
variable {u : ParabolicPoint → Vec3} {Du : ParabolicPoint → Fin 3 → Vec3}
variable {p : ParabolicPoint → ℝ} {f : ParabolicPoint → Vec3}

/-! ### Exponents

The data clauses record the pressure exponent as `ENNReal.ofReal (3 / 2)` and the
interpolation records its own exponent as `ENNReal.ofReal (10 / 3)`, while the
Hölder machinery of Mathlib is stated for extended-real numerals.  The two
bridges below and the Hölder pairing `3 / 2` with `3` are what connect them;
Mathlib supplies no such pairing for these numerals. -/

/-- The pressure exponent of `def:sws` as an extended-real numeral. -/
theorem ofReal_threeHalves : ENNReal.ofReal (3 / 2 : ℝ) = (3 / 2 : ℝ≥0∞) := by
  rw [show (3 / 2 : ℝ) = ((3 : ℝ) / 2) by norm_num]
  rw [ENNReal.ofReal_div_of_pos (by norm_num)]
  norm_num

/-- The velocity exponent used below as an extended-real numeral. -/
theorem ofReal_three : ENNReal.ofReal (3 : ℝ) = (3 : ℝ≥0∞) := by simp

/-! ### `L^p` membership through the Lebesgue integral

The data clauses state their finiteness with Lebesgue integrals of powers of the
extended norm, whereas the interpolation and Hölder's inequality both speak of
`MeasureTheory.MemLp`.  The two are the same statement for a finite exponent, and
the translations are collected here once. -/

/-! ### Spatial slices of the velocity

The interpolation is proved slice by slice in time, so it asks for a spatial
Sobolev representative at almost every time.  The data clauses give the joint
finiteness of the energy on the box and an almost-everywhere weak gradient on the
box; the first is turned into almost-everywhere square integrability of the
slices by the product structure of Lebesgue measure on space-time, and the two
are then combined. -/

/-! ### The interpolation on one ball cylinder -/

/-! ### Cubic integrability on a compact set -/

/-! ### The two Hölder pairings against the velocity -/

end CKN
