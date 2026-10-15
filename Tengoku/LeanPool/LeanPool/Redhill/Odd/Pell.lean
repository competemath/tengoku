/-
Copyright (c) 2026 Jeremy Tan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Tan
-/
module

public import Tengoku

/-!
# Pell equation for the odd case
-/

@[expose] public section

namespace OddCase

/-- An infinite sequence of pairs of natural numbers `(s, t)` satisfying
`y * s ^ 2 + 1 = (y + 1) * t ^ 2`. This will be applied with `y = Y n F ^ 2`. -/
def pell (y : ℕ) : ℕ → ℕ × ℕ
  | 0 => (1, 1)
  | k + 1 =>
    let (s, t) := pell y k
    ((2 * y + 1) * s + (2 * y + 2) * t, 2 * y * s + (2 * y + 1) * t)

variable {y k : ℕ}

/--
@isnad1 id=eq.0h2v.s6.29047e195b9d from=translated src=- shape=6720d708 vocab=9572df0d
-/
lemma pell_spec : y * (pell y k).1 ^ 2 + 1 = (y + 1) * (pell y k).2 ^ 2 := by
  induction k <;> grind [pell]

/--
@isnad1 id=lt.0h2v.s4.8f868ea6ac17 from=translated src=- shape=48a3bebe vocab=9c0853f2
-/
lemma pell_snd_pos : 0 < (pell y k).2 := by induction k <;> grind [pell]

/--
@isnad1 id=le.0h2v.s4.12c3a3f61266 from=translated src=- shape=de9dd48f vocab=a555860b
-/
lemma pell_snd_le_pell_fst : (pell y k).2 ≤ (pell y k).1 := by induction k <;> grind [pell]

/--
@isnad1 id=lt.0h2v.s4.e94141b36582 from=translated src=- shape=48a3bebe vocab=65783586
-/
lemma pell_fst_pos : 0 < (pell y k).1 := pell_snd_pos.trans_le pell_snd_le_pell_fst

/--
@isnad1 id=strictmo.0h1v.s3.f4d923605175 from=translated src=- shape=2f87ade1 vocab=2c59045a
-/
lemma strictMono_pell_fst : StrictMono fun k ↦ (pell y k).1 := by
  refine strictMono_nat_of_lt_succ fun n ↦ ?_
  induction n <;> grind [pell]

open UniqueFactorizationMonoid in
/--
@isnad1 id=dvd.0h2v.s7.f4ee8430f728 from=translated src=- shape=5fa84e97 vocab=d93d4363
-/
lemma radical_mul_pell_sq_add_one_dvd :
    radical (((pell (y ^ 2) k).1 * y) ^ 2 + 1) ∣ (y ^ 2 + 1) * (pell (y ^ 2) k).2 := by
  rw [mul_comm, mul_pow, pell_spec]
  exact radical_mul_dvd.trans
    (mul_dvd_mul radical_dvd_self (radical_pow_dvd.trans radical_dvd_self))

end OddCase
