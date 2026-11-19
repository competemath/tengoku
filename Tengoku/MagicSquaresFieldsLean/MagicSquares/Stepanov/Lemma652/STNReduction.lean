import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.STN
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.PowerExpansion
import Tengoku.Seed.Algebra.BigOperators.Fin
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Regrouping by the reduced powers of g(c)

After equation (6.25), LN97 replaces every `g(c)^i` by a linear
combination of `1,g(c),...,g(c)^(r-1)`.  The resulting coefficient of
`g(c)^t` is exactly `s_{t,n}(c)`.

Version 2 uses `Fin r` throughout.  This avoids repeatedly converting a
natural number known to lie in `Finset.range r` into an element of
`Fin r`, and separates the proof into three elementary steps:

1. rewrite `z^i` using the remainder of `X^i` modulo `B`;
2. commute the three finite sums;
3. identify the coefficient with the evaluation of `stepanovSTN`.
-/

omit [Fintype F] [DecidableEq F] in
/-- The power-reduction identity indexed directly by `Fin r`.-/
theorem pow_eq_sum_fin_powerReductionCoeff
    {r : ℕ}
    (B : Polynomial F) (i : ℕ) (c : F)
    (hB : B.Monic)
    (hr : 0 < r)
    (hdeg : B.natDegree = r)
    (hc : B.IsRoot c) :
    c ^ i =
      ∑ t : Fin r,
        powerReductionCoeff B i (t : ℕ) * c ^ (t : ℕ) := by
  simpa only [Finset.sum_range] using
    (pow_eq_sum_powerReductionCoeff
      (F := F) B i r c hB hr hdeg hc)

omit [Fintype F] [DecidableEq F] in
/-- Evaluating `s_{t,n}` gives the scalar coefficient appearing after
the power-reduction regrouping.-/
theorem eval_stepanovSTN
    {m r u : ℕ}
    (b : Fin r → Fin m → F)
    (e : Fin m → Fin (u + 1) → Polynomial F)
    (t : Fin r) (c : F) :
    eval c (stepanovSTN b e t)
      =
    ∑ i : Fin m,
      ∑ j : Fin (u + 1),
        b t i * eval c (e i j) * c ^ (j : ℕ) := by
  unfold stepanovSTN
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro j hj
  simp [mul_assoc]

omit [Fintype F] [DecidableEq F] in
/-- Regroup the double sum after replacing every `z^i` by its
`B`-remainder expansion.  This is the finite-sum algebra immediately
following equation (6.25) on LN97 p. 306.-/
theorem sum_e_mul_pow_eq_sum_STN_mul_pow
    {m r u : ℕ}
    (B : Polynomial F)
    (hB : B.Monic)
    (hr : 0 < r)
    (hdeg : B.natDegree = r)
    (e : Fin m → Fin (u + 1) → Polynomial F)
    (c z : F)
    (hz : B.IsRoot z) :
    (∑ i : Fin m,
      ∑ j : Fin (u + 1),
        eval c (e i j) * z ^ (i : ℕ) * c ^ (j : ℕ))
      =
    ∑ t : Fin r,
      eval c
        (stepanovSTN
          (fun tt ii =>
            powerReductionCoeff B (ii : ℕ) (tt : ℕ))
          e t) *
        z ^ (t : ℕ) := by
  let b : Fin r → Fin m → F :=
    fun tt ii => powerReductionCoeff B (ii : ℕ) (tt : ℕ)

  have hzpow :
      ∀ i : Fin m,
        z ^ (i : ℕ) =
          ∑ t : Fin r, b t i * z ^ (t : ℕ) := by
    intro i
    exact pow_eq_sum_fin_powerReductionCoeff
      (F := F) B (i : ℕ) z hB hr hdeg hz

  calc
    (∑ i : Fin m,
      ∑ j : Fin (u + 1),
        eval c (e i j) * z ^ (i : ℕ) * c ^ (j : ℕ))
        =
      ∑ i : Fin m,
        ∑ j : Fin (u + 1),
          eval c (e i j) *
            (∑ t : Fin r, b t i * z ^ (t : ℕ)) *
            c ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [hzpow i]

    _ =
      ∑ i : Fin m,
        ∑ j : Fin (u + 1),
          ∑ t : Fin r,
            eval c (e i j) *
              (b t i * z ^ (t : ℕ)) *
              c ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.mul_sum, Finset.sum_mul]

    _ =
      ∑ i : Fin m,
        ∑ t : Fin r,
          ∑ j : Fin (u + 1),
            eval c (e i j) *
              (b t i * z ^ (t : ℕ)) *
              c ^ (j : ℕ) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]

    _ =
      ∑ t : Fin r,
        ∑ i : Fin m,
          ∑ j : Fin (u + 1),
            eval c (e i j) *
              (b t i * z ^ (t : ℕ)) *
              c ^ (j : ℕ) := by
      rw [Finset.sum_comm]

    _ =
      ∑ t : Fin r,
        (∑ i : Fin m,
          ∑ j : Fin (u + 1),
            b t i * eval c (e i j) * c ^ (j : ℕ)) *
          z ^ (t : ℕ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j hj
      ring

    _ =
      ∑ t : Fin r,
        eval c (stepanovSTN b e t) *
          z ^ (t : ℕ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [eval_stepanovSTN]

    _ =
      ∑ t : Fin r,
        eval c
          (stepanovSTN
            (fun tt ii =>
              powerReductionCoeff B (ii : ℕ) (tt : ℕ))
            e t) *
          z ^ (t : ℕ) := by
      rfl

end LN97
end MagicSquares
