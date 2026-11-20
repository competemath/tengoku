/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Ordering.Obstruction
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Polynomial.NormalForms
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Polynomial.RatFuncReduction
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Polynomial.Gcd
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Polynomial.LaurentPoint
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Polynomial.Positivity
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Polynomial.LegendreLinearAlgebra.Coefficients
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Polynomial.LegendreLinearAlgebra.Remainders
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Polynomial.NonlinearIrreducible.ResidueFields
import Tengoku.LeanRatfuncWittLocalGlobal.RatFuncWittLocalGlobal.Polynomial.NonlinearIrreducible.StandardComplexification
import Tengoku.Seed.Algebra.Squarefree.Basic
import Tengoku.Seed.Analysis.Polynomial.Basic
import Tengoku.Seed.Algebra.Polynomial.Degree.IsMonicOfDegree
import Tengoku.Seed.Algebra.Polynomial.Lifts
import Tengoku.Seed.Algebra.Polynomial.SpecificDegree
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic
import Tengoku.Seed.FieldTheory.RatFunc.AsPolynomial
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Lemmas
import Tengoku.Seed.LinearAlgebra.Dimension.StrongRankCondition
import Tengoku.Seed.Order.Filter.AtTopBot.Basic
import Tengoku.Seed.RingTheory.Polynomial.DegreeLT
import Tengoku.Seed.RingTheory.Polynomial.SmallDegreeVieta
import Tengoku.Seed.Topology.Algebra.Polynomial

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Polynomial Legendre construction

This module contains the polynomial Legendre construction targets, finite
congruence reductions, boundary cases, and point-ordering bridges used by the
local-global reduction.
-/

namespace RatFuncWittLocalGlobal

namespace RatFunc

universe u v

/--
The future polynomial Legendre step, expressed exactly in the shape needed by
the squarefree non-terminal core: after splitting `B` and `C` by their common
factor, construct a nonzero polynomial solution of
`G*r^2 + C₁*q^2 + B₁*d^2 = 0`.-/
def SquarefreeGcdLegendreConstructionNoOrderingObstruction
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ B C : Polynomial R,
    B ≠ 0 →
      C ≠ 0 →
        Squarefree B →
          Squarefree C →
            ¬ NormalizedOrderingObstruction
              (algebraMap (Polynomial R) (RatFunc R) B)
              (algebraMap (Polynomial R) (RatFunc R) C) →
            ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) B)) →
            ¬ IsSquare (-(algebraMap (Polynomial R) (RatFunc R) C)) →
            ∃ s : SquarefreeGcdSplit B C,
              ∃ r q d : Polynomial R,
                (r ≠ 0 ∨ q ≠ 0 ∨ d ≠ 0) ∧
                  s.G * r ^ 2 + s.C₁ * q ^ 2 + s.B₁ * d ^ 2 = 0

/--
The sign hypothesis needed by the Legendre step for the split coefficients:
`G`, `C₁`, and `B₁` do not have a common strict sign in any ordering of
`RatFunc R`.-/
def SquarefreeGcdSplitNoCommonStrictSign
    {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C) :
    Prop :=
  ¬ SameStrictSignOrdering
    (algebraMap (Polynomial R) (RatFunc R) s.G)
    (algebraMap (Polynomial R) (RatFunc R) s.C₁)
    (algebraMap (Polynomial R) (RatFunc R) s.B₁)

/--
@isnad1 id=squarefr.1h4v.s9.34488e7ef224 from=translated src=- shape=de1c9b64 vocab=0b1884d1
-/
theorem squarefreeGcdSplitNoCommonStrictSign_of_not_normalizedOrderingObstruction
    {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C)
    (hno : ¬ NormalizedOrderingObstruction
      (algebraMap (Polynomial R) (RatFunc R) B)
      (algebraMap (Polynomial R) (RatFunc R) C)) :
    SquarefreeGcdSplitNoCommonStrictSign s := by
  intro hsame
  let φ := algebraMap (Polynomial R) (RatFunc R)
  have hC : φ C = φ s.G * φ s.C₁ := by
    simpa [φ, map_mul] using congrArg φ s.hC
  have hB : φ B = φ s.G * φ s.B₁ := by
    simpa [φ, map_mul] using congrArg φ s.hB
  have hCB : NormalizedOrderingObstruction (φ C) (φ B) :=
    normalizedOrderingObstruction_of_sameStrictSign_factors hC hB hsame
  exact hno ((normalizedOrderingObstruction_swap).mpr hCB)

/--
The finite local square-congruence hypotheses in the polynomial Legendre
theorem for the ternary form `A*x^2 + B*y^2 + C*z^2`.-/
def PolynomialLegendreLocalConditions
    {R : Type u} [CommRing R] (A B C : Polynomial R) : Prop :=
  (∀ π : Polynomial R, Irreducible π → π ∣ A → IsSquareMod π (-(B * C))) ∧
    (∀ π : Polynomial R, Irreducible π → π ∣ B → IsSquareMod π (-(A * C))) ∧
      (∀ π : Polynomial R, Irreducible π → π ∣ C → IsSquareMod π (-(A * B)))

/--
A stronger but often easier-to-assemble version of the Legendre congruence
conditions: the required element is square modulo the whole coefficient, not
only modulo each irreducible factor.-/
def PolynomialLegendreWholeModConditions
    {R : Type u} [CommRing R] (A B C : Polynomial R) : Prop :=
  IsSquareMod A (-(B * C)) ∧
    IsSquareMod B (-(A * C)) ∧
      IsSquareMod C (-(A * B))

/--
@isnad1 id=polynomi.1h4v.s5.e050434b0844 from=translated src=- shape=c378a3f0 vocab=57f94714
-/
theorem polynomialLegendreLocalConditions_of_wholeModConditions
    {R : Type u} [CommRing R] {A B C : Polynomial R}
    (hwhole : PolynomialLegendreWholeModConditions A B C) :
    PolynomialLegendreLocalConditions A B C := by
  refine ⟨?_, ?_, ?_⟩
  · intro π _hirr hπA
    exact hwhole.1.of_dvd hπA
  · intro π _hirr hπB
    exact hwhole.2.1.of_dvd hπB
  · intro π _hirr hπC
    exact hwhole.2.2.of_dvd hπC

/--
@isnad1 id=polynomi.7h4v.s8.d2a1940b7fb1 from=translated src=- shape=edd5b3fa vocab=d6b02d59
-/
theorem polynomialLegendreWholeModConditions_of_localConditions
    {R : Type u} [Field R] {A B C : Polynomial R}
    (hA0 : A ≠ 0) (hB0 : B ≠ 0) (hC0 : C ≠ 0)
    (hAsq : Squarefree A) (hBsq : Squarefree B) (hCsq : Squarefree C)
    (hlocal : PolynomialLegendreLocalConditions A B C) :
    PolynomialLegendreWholeModConditions A B C := by
  refine ⟨?_, ?_, ?_⟩
  · exact isSquareMod_of_forall_irreducible_dvd_of_squarefree hA0 hAsq hlocal.1
  · exact isSquareMod_of_forall_irreducible_dvd_of_squarefree hB0 hBsq hlocal.2.1
  · exact isSquareMod_of_forall_irreducible_dvd_of_squarefree hC0 hCsq hlocal.2.2

/-- Whole-modulus congruence conditions for the coefficients from a gcd split.-/
def SquarefreeGcdSplitLegendreWholeModConditions
    {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C) :
    Prop :=
  PolynomialLegendreWholeModConditions s.G s.C₁ s.B₁

/--
@isnad1 id=polynomi.1h4v.s5.444d2cb1a670 from=translated src=- shape=748dbd4b vocab=44f0ca6b
-/
theorem squarefreeGcdSplitLegendreLocalConditions_of_wholeModConditions
    {R : Type u} [Field R] {B C : Polynomial R} {s : SquarefreeGcdSplit B C}
    (hwhole : SquarefreeGcdSplitLegendreWholeModConditions s) :
    PolynomialLegendreLocalConditions s.G s.C₁ s.B₁ :=
  polynomialLegendreLocalConditions_of_wholeModConditions hwhole

/--
@isnad1 id=squarefr.3h4v.s7.0ab1ad9d5f85 from=translated src=- shape=80d4ef30 vocab=4d1a0015
-/
theorem squarefreeGcdSplitLegendreWholeModConditions_of_factor_mod
    {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C)
    (hG : IsSquareMod s.G (-(s.C₁ * s.B₁)))
    (hC₁ : IsSquareMod s.C₁ (-B))
    (hB₁ : IsSquareMod s.B₁ (-C)) :
    SquarefreeGcdSplitLegendreWholeModConditions s := by
  refine ⟨hG, ?_, ?_⟩
  · exact s.isSquareMod_neg_G_mul_B₁_of_neg_B hC₁
  · exact s.isSquareMod_neg_G_mul_C₁_of_neg_C hB₁

/--
@isnad1 id=polynomi.3h4v.s7.c45139dec31c from=translated src=- shape=c1d04297 vocab=99b86942
-/
theorem squarefreeGcdSplitLegendreLocalConditions_of_factor_mod
    {R : Type u} [Field R] {B C : Polynomial R} (s : SquarefreeGcdSplit B C)
    (hG : IsSquareMod s.G (-(s.C₁ * s.B₁)))
    (hC₁ : IsSquareMod s.C₁ (-B))
    (hB₁ : IsSquareMod s.B₁ (-C)) :
    PolynomialLegendreLocalConditions s.G s.C₁ s.B₁ :=
  squarefreeGcdSplitLegendreLocalConditions_of_wholeModConditions
    (squarefreeGcdSplitLegendreWholeModConditions_of_factor_mod s hG hC₁ hB₁)

/--
The reusable polynomial Legendre construction over `R[X]`, stated in the
orientation used by the gcd split.-/
def PolynomialLegendreConstruction
    (R : Type u) [Field R] [LinearOrder R] [IsStrictOrderedRing R] [IsRealClosed R] :
    Prop :=
  ∀ A B C : Polynomial R,
    A ≠ 0 →
      B ≠ 0 →
        C ≠ 0 →
          Squarefree A →
            Squarefree B →
              Squarefree C →
                IsCoprime A B →
                  IsCoprime A C →
                    IsCoprime B C →
                      PolynomialLegendreLocalConditions A B C →
                        ¬ SameStrictSignOrdering
                          (algebraMap (Polynomial R) (RatFunc R) A)
                          (algebraMap (Polynomial R) (RatFunc R) B)
                          (algebraMap (Polynomial R) (RatFunc R) C) →
                        ∃ x y z : Polynomial R,
                          (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0) ∧
                            A * x ^ 2 + B * y ^ 2 + C * z ^ 2 = 0

end RatFunc

end RatFuncWittLocalGlobal
