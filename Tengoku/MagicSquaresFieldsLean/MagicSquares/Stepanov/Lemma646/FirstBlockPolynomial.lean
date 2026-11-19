import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.DomainOrbit
import Tengoku.Seed.Algebra.Polynomial.BigOperators
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# The polynomial A(Y) formed from the first coefficient blocks

For `a_i(X) ∈ F_q[X]`, define

    A(Y) = a_0(X) + a_1(X)Y + ... + a_{m-1}(X)Y^(m-1)

as an element of `F_q[X][Y]`.
-/

variable {R : Type*} [CommRing R] [IsDomain R]

noncomputable def firstBlockPolynomial
    {m : ℕ} (a : Fin m → R) : Polynomial R :=
  ∑ i : Fin m, C (a i) * X ^ (i : ℕ)

omit [IsDomain R] in
theorem eval_firstBlockPolynomial
    {m : ℕ} (a : Fin m → R) (y : R) :
    eval y (firstBlockPolynomial a) =
      ∑ i : Fin m, a i * y ^ (i : ℕ) := by
  unfold firstBlockPolynomial
  change
    (Polynomial.evalRingHom y)
        (∑ i : Fin m, C (a i) * X ^ (i : ℕ)) =
      ∑ i : Fin m, a i * y ^ (i : ℕ)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

theorem firstBlockPolynomial_natDegree_le
    {m : ℕ} (hm : 0 < m)
    (a : Fin m → R) :
    (firstBlockPolynomial a).natDegree ≤ m - 1 := by
  unfold firstBlockPolynomial
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  calc
    (C (a i) * X ^ (i : ℕ)).natDegree
        ≤ (X ^ (i : ℕ) : Polynomial R).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ = (i : ℕ) := by simp
    _ ≤ m - 1 := by omega

omit [IsDomain R] in
theorem map_firstBlockPolynomial
    {S : Type*} [CommRing S]
    {m : ℕ}
    (phi : R →+* S)
    (a : Fin m → R) :
    Polynomial.map phi (firstBlockPolynomial a) =
      firstBlockPolynomial (fun i => phi (a i)) := by
  unfold firstBlockPolynomial
  change
    (Polynomial.mapRingHom phi)
        (∑ i : Fin m, C (a i) * X ^ (i : ℕ)) =
      ∑ i : Fin m, C (phi (a i)) * X ^ (i : ℕ)
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp

end LN97
end MagicSquares
