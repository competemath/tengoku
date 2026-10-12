/-
Copyright (c) 2024 The Compfiles Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Kurkiewicz
-/

module

public import Tengoku

@[expose] public section

/-!
Polish Mathematical Olympiad 2016, Stage 1, Problem 8
Author of the problem: Nguyen Hung Son
Source of the problem: https://om.sem.edu.pl/static/app_main/problems/om68_1r.pdf

Let a, b, c be integers. Show that there exists a positive integer n, such that

  n³ + an² + bn + c

is not a square of any integer.
-/

namespace Poland2016S1P8

/--
@isnad1 id=even.2h2v.s4.29dec01c872b from=translated src=- shape=b1e4833c vocab=df0368af
-/
lemma even_of_add {a b : ℤ} (ha : Even a) (hb : Even (a + b)) : Even b := by
  rw [show b = a + b - a by ring]
  exact Even.sub hb ha

/--
@isnad1 id=dvd.1h2v.s4.f753c7a92516 from=translated src=- shape=49d943ca vocab=17f7a1e8
-/
lemma div_4_mul_of_both_even {a b : ℤ } (H : Even a ∧ Even b) : 4 ∣ a * b := by
  obtain ⟨⟨k, rfl⟩, ⟨l, rfl⟩⟩ := H
  use k * l
  ring

end Poland2016S1P8
