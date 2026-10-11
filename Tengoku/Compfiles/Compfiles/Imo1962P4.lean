/-
Copyright (c) 2020 Kevin Lacker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Lacker, Heather Macbeth
-/
module

public import Tengoku

@[expose] public section

/-!
# International Mathematics Olympiad 1962, Problem 4

Solve the equation
     cos² x + cos² (2 * x) + cos² (3 * x) = 1.
-/

open Real

namespace Imo1962P4

def ProblemEquation (x : ℝ) : Prop :=
  cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 = 1

abbrev solutionSet : Set ℝ :=
  {x : ℝ | ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 ∨ x = (2 * ↑k + 1) * π / 6}

noncomputable section

/-
The key to solving this problem simply is that we can rewrite the equation as
a product of terms, shown in `alt_formula`, being equal to zero.
-/
def altFormula (x : ℝ) : ℝ :=
  cos x * (cos x ^ 2 - 1 / 2) * cos (3 * x)

/--
@isnad1 id=eq.0h1v.s7.e1865e08be55 from=translated src=- shape=7ff1d442 vocab=b68f160e
-/
theorem cos_sum_equiv {x : ℝ} :
    (cos x ^ 2 + cos (2 * x) ^ 2 + cos (3 * x) ^ 2 - 1) / 4 = altFormula x := by
  simp only [Real.cos_two_mul, cos_three_mul, altFormula]
  ring

/--
@isnad1 id=iff.0h1v.s3.f8383887722d from=translated src=- shape=64386546 vocab=9675f6ae
-/
theorem alt_equiv {x : ℝ} : ProblemEquation x ↔ altFormula x = 0 := by
  rw [ProblemEquation, ← cos_sum_equiv, div_eq_zero_iff, sub_eq_zero]
  norm_num

/--
@isnad1 id=iff.0h1v.s6.b8c5c0ba5d79 from=translated src=- shape=e9bf5cdb vocab=cafc2181
-/
theorem finding_zeros {x : ℝ} : altFormula x = 0 ↔ cos x ^ 2 = 1 / 2 ∨ cos (3 * x) = 0 := by
  simp only [altFormula, mul_assoc, mul_eq_zero, sub_eq_zero]
  constructor
  · rintro (h1 | h2)
    · right
      rw [cos_three_mul, h1]
      ring
    · exact h2
  · exact Or.inr

/-
Now we can solve for `x` using basic-ish trigonometry.
-/
/--
@isnad1 id=iff.0h1v.s6.8ed49a07c5b3 from=translated src=- shape=1a98c2f8 vocab=c70ed4c6
-/
theorem solve_cos2_half {x : ℝ} : cos x ^ 2 = 1 / 2 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 4 := by
  rw [cos_sq]
  simp only [add_eq_left, div_eq_zero_iff]
  norm_num
  rw [cos_eq_zero_iff]
  constructor <;>
    · rintro ⟨k, h⟩
      use k
      linarith

/--
@isnad1 id=iff.0h1v.s6.d882a3550ddf from=translated src=- shape=3a8d0448 vocab=2fcbf40a
-/
theorem solve_cos3x_0 {x : ℝ} : cos (3 * x) = 0 ↔ ∃ k : ℤ, x = (2 * ↑k + 1) * π / 6 := by
  rw [cos_eq_zero_iff]
  refine exists_congr fun k => ?_
  constructor <;> intro <;> linarith

end

/-
The final theorem is now just gluing together our lemmas.
-/

end Imo1962P4
