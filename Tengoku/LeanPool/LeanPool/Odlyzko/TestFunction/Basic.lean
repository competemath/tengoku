/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Tengoku

/-! TODO: Add doc-string. -/

@[expose] public section

namespace NumberField.Odlyzko

/-- A weight used in the Odlyzko-bound argument. -/
noncomputable def Tartar.weight (x : ℝ) : ℝ :=
  max (1 - x ^ 2) 0

/-- An amplitude used in the Odlyzko-bound argument. -/
noncomputable def Tartar.amplitude (x : ℝ) : ℝ :=
  if x = 0 then 1 else 3 * (Real.sin x - x * Real.cos x) / x ^ 3

/-- A test function used in the Odlyzko-bound argument. -/
noncomputable def Tartar.testFunction (x : ℝ) : ℝ :=
  Tartar.amplitude x ^ 2

/--
@isnad1 id=eq.0h0v.s3.0d42bb058929 from=translated src=- shape=3c26ae4f vocab=c6fdb245
-/
@[simp]
theorem tartarAmplitude_zero : Tartar.amplitude 0 = 1 := by
  simp [Tartar.amplitude]

/--
@isnad1 id=eq.0h0v.s3.c81a67730ea0 from=translated src=- shape=3c26ae4f vocab=55e47dd9
-/
@[simp]
theorem tartarTestFunction_zero : Tartar.testFunction 0 = 1 := by
  simp [Tartar.testFunction]

/--
@isnad1 id=le.0h1v.s3.ee6baab77afc from=translated src=- shape=8a62b088 vocab=c378e603
-/
theorem tartarWeight_nonneg (x : ℝ) : 0 ≤ Tartar.weight x :=
  le_max_right _ _

/--
@isnad1 id=le.0h1v.s3.c231df7677cb from=translated src=- shape=8a62b088 vocab=d1780e24
-/
theorem tartarTestFunction_nonneg (x : ℝ) : 0 ≤ Tartar.testFunction x := by
  exact sq_nonneg _

/--
@isnad1 id=eq.1h1v.s4.79fa72f49165 from=translated src=- shape=7a8068be vocab=8d84c867
-/
theorem tartarWeight_eq_zero_of_one_le_abs {x : ℝ} (hx : 1 ≤ |x|) :
    Tartar.weight x = 0 := by
  rw [Tartar.weight, max_eq_right]
  simp_all

/--
@isnad1 id=eq.1h1v.s5.0e8d2f7201ee from=translated src=- shape=28ab88e1 vocab=69c863cc
-/
theorem tartarWeight_eq_one_sub_sq_of_abs_le_one {x : ℝ} (hx : |x| ≤ 1) :
    Tartar.weight x = 1 - x ^ 2 := by
  rw [Tartar.weight, max_eq_left]
  simp_all

/--
@isnad1 id=eq.0h1v.s3.5eaf76c7c65d from=translated src=- shape=cd419dad vocab=116309bd
-/
theorem tartarWeight_neg (x : ℝ) : Tartar.weight (-x) = Tartar.weight x := by
  simp [Tartar.weight]

/--
@isnad1 id=eq.0h1v.s3.0e3b0e27e52c from=translated src=- shape=cd419dad vocab=999f1e2b
-/
theorem tartarAmplitude_neg (x : ℝ) : Tartar.amplitude (-x) = Tartar.amplitude x := by
  by_cases hx : x = 0
  · simp [hx]
  · simp only [Tartar.amplitude, neg_eq_zero, hx, ite_false, Real.sin_neg, Real.cos_neg]
    ring

/--
@isnad1 id=eq.0h1v.s3.a5d5e8d7d52f from=translated src=- shape=cd419dad vocab=79c0c0f6
-/
theorem tartarTestFunction_neg (x : ℝ) :
    Tartar.testFunction (-x) = Tartar.testFunction x := by
  simp [Tartar.testFunction, tartarAmplitude_neg]

/--
@isnad1 id=continuo.0h0v.s3.92d3697b926b from=translated src=- shape=e3d48bcb vocab=e46a87c1
-/
theorem tartarWeight_continuous : Continuous Tartar.weight := by
  unfold Tartar.weight
  fun_prop

end NumberField.Odlyzko
