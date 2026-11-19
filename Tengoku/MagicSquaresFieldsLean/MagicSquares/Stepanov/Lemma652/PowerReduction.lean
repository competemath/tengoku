import Tengoku.Seed.Algebra.Polynomial.RingDivision
import Tengoku.Seed.Algebra.Polynomial.Degree.Support
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F]

/-!
# Power reduction modulo B in LN97 Lemma 6.52

On p. 306, if `B(c)=0` and `deg B = r`, the proof writes

    c^i = b_{0i} + b_{1i} c + ... + b_{r-1,i} c^(r-1).

A canonical choice of these coefficients is obtained by reducing `X^i`
modulo the monic polynomial `B`.

This file formalizes that choice.
-/

/-- The canonical representative of `X^i` modulo a monic polynomial `B`.-/
noncomputable def powerRemainder
    (B : Polynomial F) (i : ℕ) : Polynomial F :=
  (X ^ i : Polynomial F) %ₘ B

/-- The coefficient `b_{t,i}` from the remainder of `X^i` modulo `B`.-/
noncomputable def powerReductionCoeff
    (B : Polynomial F) (i t : ℕ) : F :=
  (powerRemainder B i).coeff t

/-- If `c` is a root of `B`, reduction modulo `B` does not change the
value at `c`.-/
theorem eval_powerRemainder_eq_pow_of_isRoot
    (B : Polynomial F) (i : ℕ) (c : F)
    (hc : B.IsRoot c) :
    eval c (powerRemainder B i) = c ^ i := by
  have hroot : (aeval c) B = 0 := by
    simpa [Polynomial.aeval_def] using hc
  have h :=
    Polynomial.aeval_modByMonic_eq_self_of_root
      (p := (X ^ i : Polynomial F))
      (q := B) hroot
  simpa [powerRemainder, Polynomial.aeval_def] using h

/-- For a nonconstant monic `B`, every power remainder has degree
strictly smaller than `deg B`.-/
theorem powerRemainder_natDegree_lt
    (B : Polynomial F) (i : ℕ)
    (hB : B.Monic)
    (hB1 : B ≠ 1) :
    (powerRemainder B i).natDegree < B.natDegree := by
  exact Polynomial.natDegree_modByMonic_lt
    (X ^ i : Polynomial F) hB hB1

/-- If `B` is monic of natural degree `r > 0`, the remainder has
natural degree `< r`.-/
theorem powerRemainder_natDegree_lt_of_natDegree_eq
    (B : Polynomial F) (i r : ℕ)
    (hB : B.Monic)
    (hr : 0 < r)
    (hdeg : B.natDegree = r) :
    (powerRemainder B i).natDegree < r := by
  have hB1 : B ≠ 1 := by
    intro h
    rw [h] at hdeg
    simp at hdeg
    omega
  simpa [hdeg] using
    powerRemainder_natDegree_lt (F := F) B i hB hB1

/-- Finite coefficient expansion of the remainder in the basis
`1,X,...,X^(r-1)`.-/
theorem powerRemainder_eq_sum_range
    (B : Polynomial F) (i r : ℕ)
    (hB : B.Monic)
    (hr : 0 < r)
    (hdeg : B.natDegree = r) :
    powerRemainder B i =
      ∑ t ∈ Finset.range r,
        monomial t (powerReductionCoeff B i t) := by
  have hlt :
      (powerRemainder B i).natDegree < r :=
    powerRemainder_natDegree_lt_of_natDegree_eq
      (F := F) B i r hB hr hdeg
  simpa [powerReductionCoeff] using
    (Polynomial.as_sum_range'
      (powerRemainder B i) r hlt)

end LN97
end MagicSquares
