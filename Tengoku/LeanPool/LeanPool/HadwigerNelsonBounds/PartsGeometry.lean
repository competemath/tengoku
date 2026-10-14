/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.HadwigerNelsonBounds.Basic

/-!
# Exact geometry for the Parts lower-bound certificate

The 481-vertex base graph in Parts' certificate uses points

`(a + b * sqrt 33, c * sqrt 3 + d * sqrt 11) / 12`.

The equivalent coordinates below use only `sqrt 33` and `sqrt 3`; this makes
the unit-distance check an integer calculation.
-/

@[expose] public section

namespace HadwigerNelsonBounds

/-- Integer coordinates for the quadratic field used by the Parts graph. -/
structure PartsPoint where
  /-- Rational coefficient in the first Cartesian coordinate. -/
  a : Int
  /-- `sqrt 33` coefficient in the first Cartesian coordinate. -/
  b : Int
  /-- Rational coefficient in the second Cartesian coordinate. -/
  c : Int
  /-- `sqrt 33` coefficient in the second Cartesian coordinate. -/
  d : Int
deriving DecidableEq

namespace PartsPoint

/-- Difference of two exact Parts coordinates. -/
def sub (p q : PartsPoint) : PartsPoint :=
  ⟨p.a - q.a, p.b - q.b, p.c - q.c, p.d - q.d⟩

/-- Rational coefficient of 144 times the squared norm. -/
def normNumerator (p : PartsPoint) : Int :=
  p.a ^ 2 + 33 * p.b ^ 2 + 3 * p.c ^ 2 + 11 * p.d ^ 2

/-- Coefficient of `2 * sqrt 33` in 144 times the squared norm. -/
def radicalCoefficient (p : PartsPoint) : Int := p.a * p.b + p.c * p.d

/-- Exact decidable test that an integer coordinate vector has length one. -/
def IsUnit (p : PartsPoint) : Bool :=
  decide (p.normNumerator = 144 ∧ p.radicalCoefficient = 0)

/--
@isnad1 id=iff.0h1v.s4.f1ddf9e26dfe from=translated src=- shape=209cba00 vocab=f2fdfd9c
-/
lemma isUnit_iff (p : PartsPoint) :
    p.IsUnit ↔ p.normNumerator = 144 ∧ p.radicalCoefficient = 0 := by
  simp [IsUnit]

/-- Embed exact certificate coordinates in the Euclidean plane. -/
noncomputable def toR2 (p : PartsPoint) : R2 :=
  WithLp.toLp 2
    ![((p.a : ℝ) + (p.b : ℝ) * Real.sqrt 33) / 12,
      (3 * (p.c : ℝ) + (p.d : ℝ) * Real.sqrt 33) / (12 * Real.sqrt 3)]

/--
@isnad1 id=eq.0h1v.s7.d42d98687815 from=translated src=- shape=a3d15b36 vocab=7aef5bb8
-/
@[simp] lemma toR2_zero (p : PartsPoint) :
    p.toR2 0 = ((p.a : ℝ) + (p.b : ℝ) * Real.sqrt 33) / 12 := rfl

/--
@isnad1 id=eq.0h1v.s9.9cee04ef48cf from=translated src=- shape=f1ec7d41 vocab=55d8e6f8
-/
@[simp] lemma toR2_one (p : PartsPoint) :
    p.toR2 1 =
      (3 * (p.c : ℝ) + (p.d : ℝ) * Real.sqrt 33) / (12 * Real.sqrt 3) := rfl

/--
@isnad1 id=eq.0h2v.s7.dc9f30f5917a from=translated src=- shape=63ddb0e9 vocab=372eba45
-/
lemma dist_sq (p q : PartsPoint) :
    dist p.toR2 q.toR2 ^ 2 =
      ((p.sub q).normNumerator : ℝ) / 144 +
        2 * ((p.sub q).radicalCoefficient : ℝ) * Real.sqrt 33 / 144 := by
  rw [PiLp.dist_sq_eq_of_L2]
  simp only [Fin.sum_univ_two, toR2_zero, toR2_one, Real.dist_eq, sq_abs]
  have hs33 : Real.sqrt 33 * Real.sqrt 33 = 33 :=
    Real.mul_self_sqrt (by norm_num)
  have hs3 : Real.sqrt 3 * Real.sqrt 3 = 3 := sqrt_three_mul_self
  have hs3ne : Real.sqrt 3 ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by norm_num))
  have hs33sq : Real.sqrt 33 ^ 2 = 33 := by nlinarith
  have hs3sq : Real.sqrt 3 ^ 2 = 3 := by nlinarith
  simp only [PartsPoint.sub, normNumerator, radicalCoefficient, Int.cast_add,
    Int.cast_sub, Int.cast_mul, Int.cast_pow, Int.cast_ofNat]
  field_simp [PartsPoint.sub, normNumerator, radicalCoefficient, hs3ne]
  ring_nf
  rw [hs33sq, hs3sq]
  ring

/-- Every positive exact unit vector embeds as a Euclidean unit segment.
@isnad1 id=eq.1h2v.s6.819c260977da from=translated src=- shape=9db32cbd vocab=e6a6d6ef
-/
lemma dist_eq_one_of_isUnit {p q : PartsPoint} (h : (p.sub q).IsUnit) :
    dist p.toR2 q.toR2 = 1 := by
  rw [isUnit_iff] at h
  have hsq : dist p.toR2 q.toR2 ^ 2 = 1 := by
    rw [dist_sq, h.1, h.2]
    norm_num
  have hnonneg : 0 ≤ dist p.toR2 q.toR2 := dist_nonneg
  nlinarith

end PartsPoint

end HadwigerNelsonBounds
