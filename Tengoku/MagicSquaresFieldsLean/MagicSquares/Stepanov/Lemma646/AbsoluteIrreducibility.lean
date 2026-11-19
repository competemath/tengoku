import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.FirstBlockIndependence
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.Algebra.Polynomial.Taylor
import Tengoku.Seed.Algebra.Polynomial.Eval.Irreducible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F]

/-!
# Absolute irreducibility and the changes of variables in Lemma 6.46

Absolute irreducibility is expressed by irreducibility over an algebraic
closure of the constant field.  Scaling the outer variable by a nonzero
`m`-th root of `f(0)` gives the normalized Kummer polynomial, up to a unit.
Translation of the inner variable is a polynomial-ring automorphism.
-/

/-- Absolute irreducibility of the bivariate polynomial `Y^m - f(X)`.-/
def KummerAbsolutelyIrreducible (m : ℕ) (f : Polynomial F) : Prop :=
  Irreducible (kummerPolynomial m (f.map (algebraMap F (AlgebraicClosure F))))

theorem kummer_irreducible_normalize_of_isAlgClosed
    [IsAlgClosed F] {m : ℕ} (hm : 0 < m)
    (f : Polynomial F) (a : F) (ha : a ≠ 0)
    (hirr : Irreducible (kummerPolynomial m f)) :
    Irreducible (kummerPolynomial m (C a⁻¹ * f)) := by
  obtain ⟨alpha, halpha⟩ := IsAlgClosed.exists_pow_nat_eq a hm
  have halpha0 : alpha ≠ 0 := by
    intro h
    simp [h, zero_pow (Nat.ne_of_gt hm)] at halpha
    exact ha halpha.symm
  letI : Invertible (C alpha : Polynomial F) :=
    (IsUnit.map Polynomial.C (isUnit_iff_ne_zero.mpr halpha0)).invertible
  let e := Polynomial.algEquivCMulXAddC (C alpha : Polynomial F) 0
  have he : Irreducible (e (kummerPolynomial m f)) :=
    hirr.map e.toRingEquiv.toMulEquiv
  have heq : e (kummerPolynomial m f) =
      C (C a) * kummerPolynomial m (C a⁻¹ * f) := by
    simp only [e, Polynomial.algEquivCMulXAddC_apply, kummerPolynomial,
      map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Polynomial.algebraMap_eq, map_zero, add_zero, mul_pow,
      ← Polynomial.C_pow, halpha]
    rw [mul_sub, ← Polynomial.C_mul, ← mul_assoc, ← Polynomial.C_mul,
      mul_inv_cancel₀ ha, Polynomial.C_1, one_mul]
  rw [heq] at he
  exact (irreducible_isUnit_mul
    ((isUnit_iff_ne_zero.mpr ha).map Polynomial.C |>.map Polynomial.C)).mp he

/-- The normalization hypothesis in the first-block theorem follows from
absolute irreducibility of the original Kummer polynomial.-/
theorem KummerAbsolutelyIrreducible.normalized_irreducible
    {m : ℕ} {f : Polynomial F} (hirr : KummerAbsolutelyIrreducible m f)
    (hm : 0 < m) (hf0 : f.eval 0 ≠ 0) :
    Irreducible (kummerPolynomial m (normalizedKummerBase f)) := by
  let phi := algebraMap F (AlgebraicClosure F)
  have h := kummer_irreducible_normalize_of_isAlgClosed hm (f.map phi)
    (phi (f.eval 0)) ((map_ne_zero phi).mpr hf0) hirr
  apply Polynomial.Monic.irreducible_of_irreducible_map (Polynomial.mapRingHom phi)
    _ (kummerPolynomial_monic hm _)
  simpa [kummerPolynomial, normalizedKummerBase, Polynomial.map_mul,
    Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_C, Polynomial.map_X,
    map_inv₀] using h

end LN97
end MagicSquares
