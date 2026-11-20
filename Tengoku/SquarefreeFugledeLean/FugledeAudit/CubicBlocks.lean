import Tengoku.Seed.LinearAlgebra.Matrix.Notation
import Tengoku.Seed.Tactic.NoncommRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

/-!
# Exact noncommutative block identities at q = 3

The entries may themselves be operators in any ring. These are symbolic
identities for all such entries, not numerical tests of selected matrices.
This file checks the exceptional exponent-3 step, not the entire regular
decomposition for arbitrary primes.
-/

namespace FugledeAudit

open Matrix

def cyclicThreeBlock {R : Type*} [Ring R] (D S : Fin 3 → R) : Matrix (Fin 3) (Fin 3) R :=
  !![D 0, S 0, 0; 0, D 1, S 1; S 2, 0, D 2]

/--
@isnad1 id=eq.0h3v.s8.2c24e5732ab1 from=translated src=- shape=cc6a8a9c vocab=5a24bf85
-/
theorem cyclic_three_square_shift {R : Type*} [Ring R] (D S : Fin 3 → R) :
    (cyclicThreeBlock D S ^ 2) 0 1 = D 0 * S 0 + S 0 * D 1 := by
  simp [pow_succ, cyclicThreeBlock, Matrix.mul_apply, Fin.sum_univ_succ]

/--
@isnad1 id=eq.0h3v.s8.72eb335b7afd from=translated src=- shape=f0e1a0fc vocab=5a24bf85
-/
theorem cyclic_three_cube_shift {R : Type*} [Ring R] (D S : Fin 3 → R) :
    (cyclicThreeBlock D S ^ 3) 0 1 =
      D 0 ^ 2 * S 0 + D 0 * S 0 * D 1 + S 0 * D 1 ^ 2 := by
  simp [pow_succ, cyclicThreeBlock, Matrix.mul_apply, Fin.sum_univ_succ]
  noncomm_ring

/--
@isnad1 id=eq.0h3v.s8.3ad88d10112d from=translated src=- shape=1dfc5d60 vocab=5a24bf85
-/
theorem cyclic_three_cube_diagonal {R : Type*} [Ring R] (D S : Fin 3 → R) :
    (cyclicThreeBlock D S ^ 3) 0 0 = D 0 ^ 3 + S 0 * S 1 * S 2 := by
  simp [pow_succ, cyclicThreeBlock, Matrix.mul_apply, Fin.sum_univ_succ]

/-- At q = 3, the missing sparse-power assertion at exponent 3 is supplied
by U³ = I itself. No r < q hypothesis is smuggled into this step.
@isnad1 id=eq.1h3v.s8.50f83daa5f8a from=translated src=- shape=c3ab689e vocab=5a24bf85
-/
theorem cubic_identity_forces_shift_relation {R : Type*} [Ring R]
    (D S : Fin 3 → R) (hU : cyclicThreeBlock D S ^ 3 = 1) :
    D 0 ^ 2 * S 0 + D 0 * S 0 * D 1 + S 0 * D 1 ^ 2 = 0 := by
  rw [← cyclic_three_cube_shift, hU]
  simp

end FugledeAudit
