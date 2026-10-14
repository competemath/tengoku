/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Tengoku

/-!
# LeanPool.EcTateLean.Algebra.Ring.Basic

Imported Lean Pool material for `LeanPool.EcTateLean.Algebra.Ring.Basic`.
-/

@[expose] public section

variable {R : Type _}

/--
@isnad1 id=eq.0h2v.s5.1273bd46861d from=translated src=- shape=7c1a12a5 vocab=1147b86a
-/
theorem add_self_eq_mul_two [Semiring R] (a : R) : a + a = 2 * a := (two_mul a).symm

section CommRing
variable [CommRing R]

/--
@isnad1 id=eq.1h4v.s6.78cb1615ffed from=translated src=- shape=3e89cdc2 vocab=14f3b069
-/
theorem evenpow_neg {n m : ℕ} (a : R) (h : n = 2 * m) : (-a) ^ n = a ^ n := by
  rw [h, pow_mul, pow_mul, neg_sq]

/--
@isnad1 id=eq.1h4v.s6.6938de3ec498 from=translated src=- shape=80da7cc2 vocab=17974e62
-/
theorem oddpow_neg {n m : ℕ} (a : R) (h : n = 2 * m + 1) : (-a) ^ n = -(a ^ n) := by
  rw [h, pow_succ, evenpow_neg a (show 2 * m = 2 * m by rfl), pow_succ, mul_neg]

end CommRing

section IntegralDomain
variable [CommRing R] [IsDomain R]

-- TODO maybe delete
/--
@isnad1 id=eq.2h4v.s6.f8c173214273 from=translated src=- shape=1dff983f vocab=cd3547e6
-/
theorem nzero_mul_left_cancel (a b c : R) : a ≠ 0 → a * b = a * c → b = c :=
  fun h => mul_left_cancel₀ h

end IntegralDomain
