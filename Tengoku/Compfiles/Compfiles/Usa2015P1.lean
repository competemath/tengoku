/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongyu Ouyang
-/

module

public import Tengoku

@[expose] public section

/-!
# USA Mathematical Olympiad 2015, Problem 1

Solve in integers the equation x² + xy + y² = ((x + y) / 3 + 1)³.
-/

namespace Usa2015P1

/--
@isnad1 id=iff.1h5v.s4.835ffc40e538 from=translated src=- shape=31f52f94 vocab=e3b0c442
-/
lemma iff_comm {a b c : Prop} : (a → c) → (b → c) → (c → (a ↔ b)) → (a ↔ b) := by
  grind

/--
@isnad1 id=ex.2h3v.s6.32a57b715e78 from=translated src=- shape=f65f6a99 vocab=36c32c22
-/
lemma abc { a b c : ℤ } (hb : b ≠ 0) : a ^ 2 = b ^ 2 * c → ∃ d, c = d ^ 2 := by
  intro h
  have h1 : b ^ 2 ∣ a ^ 2 := by simp_all only [ne_eq, dvd_mul_right]
  have h2 : b ∣ a := by apply (Int.pow_dvd_pow_iff (by positivity)).mp h1
  obtain ⟨d, rfl⟩ := h2
  rw [mul_pow, mul_right_inj' (by positivity)] at h
  use d
  exact h.symm

abbrev SolutionSet : Set (ℤ × ℤ) :=
  {⟨x, y⟩ | ∃ n, x = n ^ 3 + 3 * n ^ 2 - 1 ∧ y = -n ^ 3 + 3 * n + 1} ∪
  {⟨x, y⟩ | ∃ n, y = n ^ 3 + 3 * n ^ 2 - 1 ∧ x = -n ^ 3 + 3 * n + 1}

end Usa2015P1
