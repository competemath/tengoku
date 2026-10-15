/-
Copyright (c) 2026 Nikolay Ulyanov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nikolay Ulyanov
-/
module

public import Tengoku.LeanPool.LeanPool.Sabidussi.Color
public import Tengoku

/-!
# Local difference patterns

For every number `n + 2` of transition occurrences we construct three admissible local patterns.
The construction is the degree-splitting step of the manuscript written without changing the
graph: remove pairs of occurrences recursively, ending with a pair or a triple.
-/

@[expose] public section

namespace Sabidussi

open scoped BigOperators

/-- A fixed enumeration of the three nonzero colours. -/
def choiceColor (c : Fin 3) : Color := tripleDifference (1, 0) c

/--
@isnad1 id=ne.0h1v.s5.c931d2eb60d1 from=translated src=- shape=9a4b31c0 vocab=f6efce87
-/
theorem choiceColor_ne_zero (c : Fin 3) : choiceColor c ≠ 0 := by
  apply tripleDifference_ne_zero
  norm_num [Prod.ext_iff]

/--
@isnad1 id=eq.0h0v.s6.1ed46451aa00 from=translated src=- shape=c69a548c vocab=e4f756d9
-/
theorem sum_choiceColor : ∑ c, choiceColor c = 0 := by
  exact sum_tripleDifference (1, 0)

/--
@isnad1 id=eq.0h1v.s6.8f4c1d5a9184 from=translated src=- shape=5df02e48 vocab=77cd4215
-/
theorem sum_tripleDifference_choice (i : Fin 3) :
    ∑ c, tripleDifference (choiceColor c) i = 0 := by
  fin_cases i <;>
    simp [Fin.sum_univ_three, choiceColor, tripleDifference, Prod.ext_iff]

/-- Three local patterns on `n + 2` occurrences.  For `2` occurrences the difference is constant;
for `3` it is the anisotropic triple; every additional pair receives the same nonzero colour and
is then removed recursively. -/
def localDifference : (n : ℕ) → Fin 3 → Fin (n + 2) → Color
  | 0, c => doubleDifference (choiceColor c)
  | 1, c => tripleDifference (choiceColor c)
  | n + 2, c =>
      Fin.cases (choiceColor c) (Fin.cases (choiceColor c) (localDifference n c))

/--
@isnad1 id=eq.0h1v.s5.abbcf43d5cda from=translated src=- shape=e8dc0208 vocab=b7c153d9
-/
@[simp]
theorem localDifference_zero (c : Fin 3) :
    localDifference 0 c = doubleDifference (choiceColor c) := rfl

/--
@isnad1 id=eq.0h1v.s5.973c9db3c8db from=translated src=- shape=e8dc0208 vocab=592d4270
-/
@[simp]
theorem localDifference_one (c : Fin 3) :
    localDifference 1 c = tripleDifference (choiceColor c) := rfl

/--
@isnad1 id=ne.0h3v.s6.8cbb3762b681 from=translated src=- shape=87769a4f vocab=dee1d494
-/
theorem localDifference_ne_zero (n : ℕ) (c : Fin 3) (i : Fin (n + 2)) :
    localDifference n c i ≠ 0 := by
  induction n using Nat.twoStepInduction with
  | zero => exact doubleDifference_ne_zero _ (choiceColor_ne_zero c) i
  | one => exact tripleDifference_ne_zero _ (choiceColor_ne_zero c) i
  | more n ih _ =>
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ih k) j) i
      · exact choiceColor_ne_zero c
      · exact choiceColor_ne_zero c

/--
@isnad1 id=eq.0h2v.s7.723bc258ff28 from=translated src=- shape=6d684a4e vocab=db45a347
-/
theorem sum_localDifference_occurrences (n : ℕ) (c : Fin 3) :
    ∑ i, localDifference n c i = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => exact sum_doubleDifference (choiceColor c)
  | one => exact sum_tripleDifference (choiceColor c)
  | more n ih _ =>
      rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
      simp only [localDifference, Fin.cases_zero, Fin.cases_succ]
      calc
        choiceColor c + (choiceColor c + ∑ i, localDifference n c i) =
            (choiceColor c + choiceColor c) + ∑ i, localDifference n c i := by abel
        _ = 0 := by rw [color_add_self, zero_add, ih]

/--
@isnad1 id=eq.0h2v.s6.f9461669fb8d from=translated src=- shape=2d77f689 vocab=db45a347
-/
theorem sum_localDifference_choices (n : ℕ) (i : Fin (n + 2)) :
    ∑ c, localDifference n c i = 0 := by
  induction n using Nat.twoStepInduction with
  | zero => fin_cases i <;> simpa [doubleDifference] using sum_choiceColor
  | one => exact sum_tripleDifference_choice i
  | more n ih _ =>
      refine Fin.cases ?_ (fun j ↦ Fin.cases ?_ (fun k ↦ ih k) j) i
      · exact sum_choiceColor
      · exact sum_choiceColor

end Sabidussi
