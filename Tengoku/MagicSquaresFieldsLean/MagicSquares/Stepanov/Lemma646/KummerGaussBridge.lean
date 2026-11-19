import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma646.KummerRootInterface
import Tengoku.Seed.RingTheory.Polynomial.GaussLemma
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

/-!
# Gauss-lemma bridge for the Kummer root in LN97 Lemma 6.46

The book uses absolute irreducibility of

    Y^m - f(X)

to know that, after passing from `F[X]` to the rational function field
`F(X)`, the corresponding polynomial in `Y` is irreducible of degree `m`.
The root therefore has degree `m` over `F(X)`.

This file formalizes the second half of that passage:

* irreducibility over `F[X]` is transported to `RatFunc F` by Gauss's lemma;
* adjoining a root of the resulting Kummer polynomial gives a concrete
  `KummerRootData` object;
* the root has minimal-polynomial degree exactly `m` and satisfies the
  expected equation `Y^m = f` in the rational-function field.

`AbsoluteIrreducibility` supplies the preceding geometric step: absolute
irreducibility implies irreducibility of the normalized polynomial
`Y^m - f(0)⁻¹ f(X)` over `F[X]`.
-/

variable {F : Type*} [Field F]

/-- `Y^m - f(X)` viewed as a polynomial in `Y` with coefficients in `F[X]`.-/
noncomputable def kummerPolynomial
    (m : ℕ) (f : Polynomial F) : Polynomial (Polynomial F) :=
  X ^ m - C f

/-- The same Kummer polynomial after extending coefficients to `F(X)`.-/
noncomputable def kummerRatFuncPolynomial
    (m : ℕ) (f : Polynomial F) : Polynomial (RatFunc F) :=
  X ^ m - C ((algebraMap (Polynomial F) (RatFunc F)) f)

/--
@isnad1 id=eq.0h3v.s7.8d8177b2cb0b from=translated src=- shape=ca958b40 vocab=798a8392
-/
@[simp]
theorem map_kummerPolynomial
    (m : ℕ) (f : Polynomial F) :
    (kummerPolynomial m f).map
        (algebraMap (Polynomial F) (RatFunc F)) =
      kummerRatFuncPolynomial m f := by
  simp [kummerPolynomial, kummerRatFuncPolynomial]

/--
@isnad1 id=monic.1h3v.s5.da137614a4d4 from=translated src=- shape=b43ac694 vocab=5c1dcd5b
-/
theorem kummerPolynomial_monic
    {m : ℕ} (hm : 0 < m) (f : Polynomial F) :
    (kummerPolynomial m f).Monic := by
  exact Polynomial.monic_X_pow_sub_C f (Nat.ne_of_gt hm)

/--
@isnad1 id=monic.1h3v.s5.6958a37efc62 from=translated src=- shape=5fd30579 vocab=e480e034
-/
theorem kummerRatFuncPolynomial_monic
    {m : ℕ} (hm : 0 < m) (f : Polynomial F) :
    (kummerRatFuncPolynomial m f).Monic := by
  exact Polynomial.monic_X_pow_sub_C
    ((algebraMap (Polynomial F) (RatFunc F)) f)
    (Nat.ne_of_gt hm)

/-- Gauss's lemma: irreducibility in `(F[X])[Y]` implies irreducibility
of the same monic polynomial in `F(X)[Y]`.
@isnad1 id=irreduci.2h3v.s7.ca0af80d8816 from=translated src=- shape=5914ac69 vocab=861cd218
-/
theorem kummerRatFuncPolynomial_irreducible
    {m : ℕ} (hm : 0 < m) {f : Polynomial F}
    (hirr : Irreducible (kummerPolynomial m f)) :
    Irreducible (kummerRatFuncPolynomial m f) := by
  have hmonic : (kummerPolynomial m f).Monic :=
    kummerPolynomial_monic hm f
  rw [← map_kummerPolynomial]
  exact
    (hmonic.irreducible_iff_irreducible_map_fraction_map
      (K := RatFunc F)).mp hirr

/-- A concrete degree-`m` Kummer root over `F(X)`, obtained from
irreducibility of `Y^m - f(X)` over `F[X]`.

This discharges the minimal-polynomial part of `KummerRootInterface`.
The book's absolute-irreducibility assumption supplies the normalized
irreducibility hypothesis through `AbsoluteIrreducibility`.-/
noncomputable def kummerRootDataOfIrreducible
    {m : ℕ} (hm : 0 < m) {f : Polynomial F}
    (hirr : Irreducible (kummerPolynomial m f)) :
    KummerRootData m f := by
  have hPirr : Irreducible (kummerRatFuncPolynomial m f) :=
    kummerRatFuncPolynomial_irreducible hm hirr
  letI : Fact (Irreducible (kummerRatFuncPolynomial m f)) := ⟨hPirr⟩
  have hPmonic : (kummerRatFuncPolynomial m f).Monic :=
    kummerRatFuncPolynomial_monic hm f
  have hPne : kummerRatFuncPolynomial m f ≠ 0 := hPmonic.ne_zero
  refine
    { L := AdjoinRoot (kummerRatFuncPolynomial m f)
      instFieldL := inferInstance
      instAlgebra := inferInstance
      Y := AdjoinRoot.root (kummerRatFuncPolynomial m f)
      minpoly_degree := ?_
      pow_eq := ?_ }
  · have hminpoly :
        minpoly (RatFunc F)
            (AdjoinRoot.root (kummerRatFuncPolynomial m f)) =
          kummerRatFuncPolynomial m f := by
      calc
        minpoly (RatFunc F)
            (AdjoinRoot.root (kummerRatFuncPolynomial m f)) =
            kummerRatFuncPolynomial m f *
              C (kummerRatFuncPolynomial m f).leadingCoeff⁻¹ :=
          AdjoinRoot.minpoly_root hPne
        _ = kummerRatFuncPolynomial m f := by
          simp [hPmonic.leadingCoeff]
    rw [hminpoly]
    change
      (X ^ m - C ((algebraMap (Polynomial F) (RatFunc F)) f)).natDegree = m
    exact Polynomial.natDegree_X_pow_sub_C
  · rw [AdjoinRoot.algebraMap_eq]
    apply sub_eq_zero.mp
    have hroot :=
      (AdjoinRoot.mk_self
        (f := kummerRatFuncPolynomial m f))
    change
      (AdjoinRoot.mk (kummerRatFuncPolynomial m f))
          (X ^ m - C ((algebraMap (Polynomial F) (RatFunc F)) f)) = 0
        at hroot
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C] at hroot
    exact hroot

end LN97
end MagicSquares
