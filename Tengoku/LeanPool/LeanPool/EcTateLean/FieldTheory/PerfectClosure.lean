/-
Copyright (c) 2023 Alex J. Best and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
module

public import Tengoku

/-!
# LeanPool.EcTateLean.FieldTheory.PerfectClosure

Imported Lean Pool material for `LeanPool.EcTateLean.FieldTheory.PerfectClosure`.
-/

@[expose] public section

namespace ECTate
/-- A perfect ring is one where raising to the power of the ring characteristic is a bijection
  or a ring of char zero.

  Note this is distinct from the mathlib version in that we allow char 0
-/
class PerfectRing (R : Type _) [CommSemiring R] where
  -- TODO maybe refactor to be [Char R p] bijective pth power
  -- TODO maybe make this follow from mathlib perfect, via instance
  pth_power_bijective : ringChar R = 0 ∨ Function.Bijective (fun x : R => x ^ (ringChar R))

namespace PerfectRing
variable {R : Type _} [CommSemiring R]

/--
@isnad1 id=bijectiv.1h1v.s5.40366c100e9d from=translated src=- shape=1d9e1791 vocab=dc7996c3
-/
lemma pth_power_bijective_of_char_nonzero [PerfectRing R] (h : ringChar R ≠ 0) :
  Function.Bijective (fun x : R => x ^ (ringChar R)) := Or.resolve_left pth_power_bijective h

/-- The inverse of the `p`-th power map on a perfect ring (the identity in
characteristic zero). -/
noncomputable
def pthRoot [PerfectRing R] : R → R :=
if h : ringChar R = 0 then id else Function.surjInv (pth_power_bijective_of_char_nonzero h).2

/--
@isnad1 id=eq.1h2v.s5.5ca12909c115 from=translated src=- shape=0da6ae50 vocab=0bb3abc5
-/
lemma pthRoot_pow_char [PerfectRing R] (h : ringChar R ≠ 0) (x : R) :
  pthRoot x ^ (ringChar R) = x := by
  simp only [pthRoot, h, dite_false]
  exact Function.rightInverse_surjInv (pth_power_bijective_of_char_nonzero h).2 x

/--
@isnad1 id=eq.0h3v.s6.59fd7da9ba52 from=translated src=- shape=b090989c vocab=648ea5dd
-/
lemma pthRoot_pow_eq [PerfectRing R] (x : R) :
  pthRoot x ^ n = x ^ (n / ringChar R) * pthRoot x ^ (n % ringChar R) := by
  by_cases h : ringChar R = 0
  · simp [h]
  conv =>
    lhs
    rw [← Nat.mod_add_div n (ringChar R)]
  rw [pow_add, pow_mul, pthRoot_pow_char h, mul_comm]

/--
@isnad1 id=eq.0h1v.s5.3bd5146c2414 from=translated src=- shape=527b592f vocab=57b1b920
-/
@[simp]
lemma pthRoot_zero [PerfectRing R] : pthRoot (0 : R) = 0 := by
  rw [pthRoot]
  split
  · simp
  · apply_fun (fun x : R => x ^ ringChar R)
    · dsimp only
      rw [Function.surjInv_eq
            (pth_power_bijective_of_char_nonzero (by assumption)).surjective,
          zero_pow (by assumption)]
    · exact (pth_power_bijective_of_char_nonzero (by assumption)).injective

end PerfectRing

end ECTate
