import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.Orbit
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F]

/-!
# The degree conclusion after the root-of-unity orbit product in LN97 6.46

On p. 302, LN97 constructs an orbit product of degree at most
`m * deg A`, observes that it is a polynomial in `Y^m`, and concludes
that the resulting polynomial in `Y^m` has degree at most `deg A`
(and in the application, at most `m-1`).

The orbit and invariant files already prove the two inputs.  This file
combines them into the exact degree conclusion.
-/

/-- Contracting the root-of-unity orbit product by `m` does not increase
the original degree of `A`.
@isnad1 id=le.2h4v.s6.168073776d78 from=translated src=- shape=3417b33f vocab=fae64c7d
-/
theorem orbitProduct_contract_natDegree_le
    {m : ℕ} {ζ : F}
    (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ m)
    (A : Polynomial F) :
    (Polynomial.contract m (orbitProduct m ζ A)).natDegree
      ≤ A.natDegree := by
  have hinv :
      (orbitProduct m ζ A).comp (C ζ * X) =
        orbitProduct m ζ A :=
    orbitProduct_scale_invariant (F := F) hζ A
  have hscale :
      (Polynomial.contract m (orbitProduct m ζ A)).natDegree * m =
        (orbitProduct m ζ A).natDegree :=
    natDegree_contract_mul_eq_of_primitiveRoot_scale_invariant
      (F := F) hm hζ hinv
  have horbit :
      (orbitProduct m ζ A).natDegree ≤ m * A.natDegree :=
    orbitProduct_natDegree_le (F := F) m ζ A
  have hmul :
      m * (Polynomial.contract m (orbitProduct m ζ A)).natDegree
        ≤ m * A.natDegree := by
    calc
      m * (Polynomial.contract m (orbitProduct m ζ A)).natDegree
          =
        (Polynomial.contract m (orbitProduct m ζ A)).natDegree * m := by
          rw [Nat.mul_comm]
      _ = (orbitProduct m ζ A).natDegree := hscale
      _ ≤ m * A.natDegree := horbit
  exact Nat.le_of_mul_le_mul_left hmul hm

/-- The form used literally on LN97 p. 302: if `deg A ≤ m-1`, then the
polynomial obtained after writing the orbit product as a polynomial in
`Y^m` also has degree at most `m-1`.
@isnad1 id=le.3h4v.s6.324f7943c5c2 from=translated src=- shape=a412e461 vocab=251be331
-/
theorem orbitProduct_contract_natDegree_le_pred
    {m : ℕ} {ζ : F}
    (hm : 0 < m)
    (hζ : IsPrimitiveRoot ζ m)
    (A : Polynomial F)
    (hA : A.natDegree ≤ m - 1) :
    (Polynomial.contract m (orbitProduct m ζ A)).natDegree
      ≤ m - 1 :=
  le_trans
    (orbitProduct_contract_natDegree_le (F := F) hm hζ A)
    hA

end LN97
end MagicSquares
