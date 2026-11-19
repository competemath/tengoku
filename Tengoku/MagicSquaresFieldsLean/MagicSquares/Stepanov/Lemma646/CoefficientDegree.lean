import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.FirstBlockOrbit
import Tengoku.Seed.Algebra.Polynomial.Coeff
import Tengoku.Seed.Algebra.Polynomial.Degree.Lemmas
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# Coefficientwise `X`-degree bounds for the orbit polynomial

In LN97 (6.19), the coefficients of the contracted orbit polynomial are
polynomials in the first blocks `e_{i,0}(X)`.  The later reduction modulo
`X^q` needs an `X`-degree bound on each such coefficient, not merely an
outer-degree bound in `Y`.

This file proves the needed estimate directly from the orbit product.  If
every coefficient of `A(Y)` has `X`-degree at most `D`, then every coefficient
of a product of `m` scaled copies `A(z_j Y)` has `X`-degree at most `m * D`.
Contraction only selects the coefficients whose outer exponent is divisible
by `m`, so the same bound holds for every coefficient of the polynomial in
`Y^m`.
-/

variable {F : Type*} [Field F]

/-- Every coefficient of a polynomial in `Y` with coefficients in `F[X]`
has `X`-degree at most `D`.-/
def CoeffNatDegreeLE (D : ℕ) (P : Polynomial (Polynomial F)) : Prop :=
  ∀ n, (P.coeff n).natDegree ≤ D

theorem coeffNatDegreeLE_mul
    {D E : ℕ} {P Q : Polynomial (Polynomial F)}
    (hP : CoeffNatDegreeLE D P)
    (hQ : CoeffNatDegreeLE E Q) :
    CoeffNatDegreeLE (D + E) (P * Q) := by
  intro n
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro ij hij
  exact le_trans Polynomial.natDegree_mul_le
    (Nat.add_le_add (hP ij.1) (hQ ij.2))

theorem coeffNatDegreeLE_finset_prod
    {ι : Type*} (s : Finset ι)
    (P : ι → Polynomial (Polynomial F)) {D : ℕ}
    (hP : ∀ i ∈ s, CoeffNatDegreeLE D (P i)) :
    CoeffNatDegreeLE (s.card * D) (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro n
      simp only [Finset.prod_empty, Finset.card_empty, zero_mul]
      rw [Polynomial.coeff_one]
      split_ifs <;> simp
  | @insert i s hi ih =>
      have hiP : CoeffNatDegreeLE D (P i) := hP i (Finset.mem_insert_self i s)
      have hsP : ∀ j ∈ s, CoeffNatDegreeLE D (P j) := by
        intro j hj
        exact hP j (Finset.mem_insert_of_mem hj)
      have htail :
          CoeffNatDegreeLE (s.card * D) (∏ j ∈ s, P j) :=
        ih hsP
      have hmul :
          CoeffNatDegreeLE (D + s.card * D)
            (P i * ∏ j ∈ s, P j) :=
        coeffNatDegreeLE_mul hiP htail
      rw [Finset.prod_insert hi]
      simpa [Finset.card_insert_of_notMem hi, Nat.succ_mul, Nat.add_comm] using hmul

theorem firstBlockPolynomial_coeffNatDegreeLE
    {m D : ℕ} (a : Fin m → Polynomial F)
    (ha : ∀ i, (a i).natDegree ≤ D) :
    CoeffNatDegreeLE D (firstBlockPolynomial a) := by
  intro n
  unfold firstBlockPolynomial
  rw [Polynomial.finsetSum_coeff]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  rw [Polynomial.coeff_C_mul_X_pow]
  split_ifs with h
  · simpa using ha i
  · simp

theorem firstBlockOrbitFactor_coeffNatDegreeLE
    {m D : ℕ} (zeta : F) (a : Fin m → Polynomial F)
    (ha : ∀ i, (a i).natDegree ≤ D) (j : ℕ) :
    CoeffNatDegreeLE D
      (domainOrbitFactor (Polynomial.C zeta)
        (firstBlockPolynomial a) j) := by
  intro n
  unfold domainOrbitFactor
  rw [Polynomial.comp_C_mul_X_coeff]
  calc
    ((firstBlockPolynomial a).coeff n *
          ((Polynomial.C zeta) ^ j) ^ n).natDegree
        ≤ ((firstBlockPolynomial a).coeff n).natDegree +
            (((Polynomial.C zeta) ^ j) ^ n).natDegree :=
      Polynomial.natDegree_mul_le
    _ ≤ D + 0 := by
      apply Nat.add_le_add
      · exact firstBlockPolynomial_coeffNatDegreeLE a ha n
      · simp
    _ = D := by simp

/-- Coefficientwise form of the degree assertion implicit in LN97 (6.19):
every `X`-polynomial coefficient of the full orbit product has degree at most
`m * D`.-/
theorem firstBlockOrbitProduct_coeffNatDegreeLE
    {m D : ℕ} (zeta : F) (a : Fin m → Polynomial F)
    (ha : ∀ i, (a i).natDegree ≤ D) :
    CoeffNatDegreeLE (m * D) (firstBlockOrbitProduct zeta a) := by
  unfold firstBlockOrbitProduct domainOrbitProduct
  simpa using
    (coeffNatDegreeLE_finset_prod
      (F := F) (Finset.range m)
      (fun j =>
        domainOrbitFactor (Polynomial.C zeta)
          (firstBlockPolynomial a) j)
      (fun j hj => firstBlockOrbitFactor_coeffNatDegreeLE zeta a ha j))

/-- The coefficientwise `X`-degree bound for the contracted polynomial
`G` in (6.19).  This is the estimate needed in

`m (q / m - k) + (m - 1) k < q`.-/
theorem firstBlockSymmetric_coeff_natDegree_le
    {m D : ℕ} (hm : 0 < m) (zeta : F)
    (a : Fin m → Polynomial F)
    (ha : ∀ i, (a i).natDegree ≤ D) (r : ℕ) :
    ((firstBlockSymmetric zeta a).coeff r).natDegree ≤ m * D := by
  unfold firstBlockSymmetric
  rw [Polynomial.coeff_contract (Nat.ne_of_gt hm)]
  exact firstBlockOrbitProduct_coeffNatDegreeLE zeta a ha (r * m)

end LN97
end MagicSquares
