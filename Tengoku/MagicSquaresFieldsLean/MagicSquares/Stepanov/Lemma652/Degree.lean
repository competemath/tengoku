import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Core
import Tengoku.Seed.Algebra.Polynomial.BigOperators
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# Degree bookkeeping for LN97 Lemma 6.52

This file formalizes the elementary degree estimates behind the final
degree calculation on p. 308.

Recall that

    blockEval q E = E(X^q)

for a polynomial `E` whose coefficients are themselves polynomials in `X`.
If every coefficient of `E` has degree at most `D` and the outer degree of
`E` is at most `u`, then

    deg (blockEval q E) ≤ D + q*u.

We then propagate this through the Stepanov bracket and auxiliary
polynomial (6.22).
-/

omit [Fintype F] in
/-- A zero-safe natural-degree bound for products.-/
theorem natDegree_mul_le_add
    (P Q : Polynomial F) :
    (P * Q).natDegree ≤ P.natDegree + Q.natDegree := by
  by_cases hP : P = 0
  · subst P
    simp
  by_cases hQ : Q = 0
  · subst Q
    simp
  rw [Polynomial.natDegree_mul hP hQ]

omit [Fintype F] in
/-- Degree of a base-`q` block evaluation.

If every coefficient polynomial has degree at most `D` and the outer
degree is at most `u`, then substituting the outer variable by `X^q`
has degree at most `D + q*u`.-/
theorem blockEval_natDegree_le
    (q D u : ℕ)
    (E : Polynomial (Polynomial F))
    (houter : E.natDegree ≤ u)
    (hcoeff : ∀ j, (E.coeff j).natDegree ≤ D) :
    (blockEval q E).natDegree ≤ D + q * u := by
  unfold blockEval
  rw [Polynomial.eval_eq_sum_range]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hiE : i ≤ E.natDegree := by
    exact Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hiu : i ≤ u := le_trans hiE houter
  have hmul :=
    natDegree_mul_le_add
      (F := F) (E.coeff i) ((X ^ q : Polynomial F) ^ i)
  calc
    (E.coeff i * (X ^ q : Polynomial F) ^ i).natDegree
        ≤ (E.coeff i).natDegree +
            ((X ^ q : Polynomial F) ^ i).natDegree := hmul
    _ = (E.coeff i).natDegree + i * q := by
      rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow]
      simp
    _ ≤ D + u * q := by
      exact Nat.add_le_add (hcoeff i) (Nat.mul_le_mul_right q hiu)
    _ = D + q * u := by
      rw [Nat.mul_comm u q]

omit [Fintype F] in
/-- Degree bound for the bracket in (6.22).

`G` is any chosen upper bound for `deg g`.-/
theorem stepanovBracket_natDegree_le
    {m : ℕ}
    (q D u G : ℕ)
    (g : Polynomial F)
    (E : Fin m → Polynomial (Polynomial F))
    (houter : ∀ i, (E i).natDegree ≤ u)
    (hcoeff : ∀ i j, ((E i).coeff j).natDegree ≤ D)
    (hg : g.natDegree ≤ G) :
    (stepanovBracket q g E).natDegree
      ≤ D + q * u + (m - 1) * G := by
  unfold stepanovBracket
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  have hb :
      (blockEval q (E i)).natDegree ≤ D + q * u :=
    blockEval_natDegree_le
      (F := F) q D u (E i) (houter i) (hcoeff i)
  have hipred : (i : ℕ) ≤ m - 1 :=
    Nat.le_pred_of_lt i.isLt
  have hgpow :
      (g ^ (i : ℕ)).natDegree ≤ (m - 1) * G := by
    calc
      (g ^ (i : ℕ)).natDegree
          = (i : ℕ) * g.natDegree := by
              rw [Polynomial.natDegree_pow]
      _ ≤ (m - 1) * g.natDegree :=
          Nat.mul_le_mul_right g.natDegree hipred
      _ ≤ (m - 1) * G :=
          Nat.mul_le_mul_left (m - 1) hg
  have hmul :=
    natDegree_mul_le_add
      (F := F) (blockEval q (E i)) (g ^ (i : ℕ))
  exact le_trans hmul (Nat.add_le_add hb hgpow)

omit [Fintype F] in
/-- Degree bound for the complete auxiliary polynomial (6.22).

If `K` bounds `deg f` and `G` bounds `deg g`, then

    deg h ≤ M*K + D + q*u + (m-1)*G.-/
theorem stepanovAuxiliary_natDegree_le
    {m : ℕ}
    (q M D u K G : ℕ)
    (f g : Polynomial F)
    (E : Fin m → Polynomial (Polynomial F))
    (houter : ∀ i, (E i).natDegree ≤ u)
    (hcoeff : ∀ i j, ((E i).coeff j).natDegree ≤ D)
    (hf : f.natDegree ≤ K)
    (hg : g.natDegree ≤ G) :
    (stepanovAuxiliary q M f g E).natDegree
      ≤ M * K + (D + q * u + (m - 1) * G) := by
  unfold stepanovAuxiliary
  have hmul :=
    natDegree_mul_le_add
      (F := F) (f ^ M) (stepanovBracket q g E)
  have hfpow :
      (f ^ M).natDegree ≤ M * K := by
    rw [Polynomial.natDegree_pow]
    exact Nat.mul_le_mul_left M hf
  have hbracket :
      (stepanovBracket q g E).natDegree
        ≤ D + q * u + (m - 1) * G :=
    stepanovBracket_natDegree_le
      (F := F) q D u G g E houter hcoeff hg
  exact le_trans hmul (Nat.add_le_add hfpow hbracket)

end LN97
end MagicSquares
