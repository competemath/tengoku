import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.FirstBlockPolynomial
import Tengoku.Seed.Algebra.Polynomial.Degree.Lemmas
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# The symmetric polynomial G from LN97 (6.19)

For a primitive m-th root `zeta`, the orbit product of `A(Y)` is invariant
under `Y ↦ zeta Y`, hence is a polynomial in `Y^m`.  Its contraction is the
polynomial `G` whose coefficients are the symmetric expressions `C_i(a)`.
-/

variable {F : Type*} [Field F]

noncomputable def firstBlockOrbitProduct
    {m : ℕ} (zeta : F) (a : Fin m → Polynomial F) :
    Polynomial (Polynomial F) :=
  domainOrbitProduct m (Polynomial.C zeta) (firstBlockPolynomial a)

noncomputable def firstBlockSymmetric
    {m : ℕ} (zeta : F) (a : Fin m → Polynomial F) :
    Polynomial (Polynomial F) :=
  Polynomial.contract m (firstBlockOrbitProduct zeta a)

theorem C_isPrimitiveRoot
    {m : ℕ} {zeta : F}
    (hzeta : IsPrimitiveRoot zeta m) :
    IsPrimitiveRoot (Polynomial.C zeta) m := by
  exact hzeta.map_of_injective Polynomial.C_injective

theorem firstBlockOrbitProduct_scale_invariant
    {m : ℕ} {zeta : F}
    (hzeta : IsPrimitiveRoot zeta m)
    (a : Fin m → Polynomial F) :
    (firstBlockOrbitProduct zeta a).comp
        (Polynomial.C (Polynomial.C zeta) * Polynomial.X) =
      firstBlockOrbitProduct zeta a := by
  exact domainOrbitProduct_scale_invariant
    (R := Polynomial F) (C_isPrimitiveRoot hzeta)
      (firstBlockPolynomial a)

theorem firstBlockOrbit_eq_symmetric_comp
    {m : ℕ} {zeta : F}
    (hm : 0 < m)
    (hzeta : IsPrimitiveRoot zeta m)
    (a : Fin m → Polynomial F) :
    firstBlockOrbitProduct zeta a =
      (firstBlockSymmetric zeta a).comp (X ^ m) := by
  unfold firstBlockSymmetric
  have h :=
    expand_contract_eq_of_primitiveRoot_scale_invariant_domain
      (R := Polynomial F) hm (C_isPrimitiveRoot hzeta)
      (firstBlockOrbitProduct_scale_invariant hzeta a)
  rw [Polynomial.expand_eq_comp_X_pow] at h
  exact h.symm

theorem firstBlockSymmetric_natDegree_le
    {m : ℕ} {zeta : F}
    (hm : 0 < m)
    (hzeta : IsPrimitiveRoot zeta m)
    (a : Fin m → Polynomial F) :
    (firstBlockSymmetric zeta a).natDegree ≤ m - 1 := by
  have hA :
      (firstBlockPolynomial a).natDegree ≤ m - 1 :=
    firstBlockPolynomial_natDegree_le
      (R := Polynomial F) hm a
  have hB :
      (firstBlockOrbitProduct zeta a).natDegree ≤ m * (m - 1) := by
    exact le_trans
      (domainOrbitProduct_natDegree_le
        (R := Polynomial F) m (Polynomial.C zeta)
          (firstBlockPolynomial a))
      (Nat.mul_le_mul_left m hA)
  have hscale :
      (firstBlockSymmetric zeta a).natDegree * m =
        (firstBlockOrbitProduct zeta a).natDegree := by
    unfold firstBlockSymmetric
    exact
      natDegree_contract_mul_eq_of_primitiveRoot_scale_invariant_domain
        (R := Polynomial F) hm (C_isPrimitiveRoot hzeta)
        (firstBlockOrbitProduct_scale_invariant hzeta a)
  have hmul :
      (firstBlockSymmetric zeta a).natDegree * m ≤ (m - 1) * m := by
    calc
      (firstBlockSymmetric zeta a).natDegree * m =
          (firstBlockOrbitProduct zeta a).natDegree := hscale
      _ ≤ m * (m - 1) := hB
      _ = (m - 1) * m := Nat.mul_comm _ _
  exact Nat.le_of_mul_le_mul_right hmul hm

end LN97
end MagicSquares
