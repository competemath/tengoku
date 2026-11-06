/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormula
import Tengoku.YamaguchiPapers.Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.NormFormulaCoefficients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# the actual integral closure is a valuation ring

The factorization form of Hensel's lemma forces the endpoint coefficient
estimate for every irreducible polynomial.  Applied to the norm-formula value,
this says that every algebraic element or its inverse is integral over the
base valuation ring.  Thus the actual integral closure, rather than an
assumed target ring, satisfies the valuation-ring dichotomy.
-/

noncomputable section

namespace AlgebraicNumberTheory
namespace Valuations

open scoped Polynomial

/-- A closed unit for the finite norm-formula value is integral over the base
valuation ring, using only the primitive factorization definition's primitive factorization
property.
@isnad1 id=isintegr.3h4v.s7.33d9eb5e7425 from=translated src=- shape=3d87d6bf vocab=2794a10f
-/
theorem normFormula_finiteExtensionNormFormulaValue_isIntegral_of_le_one_of_henselFactorization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L]
    (v : AbsoluteValue K ℝ) (hnonarch : LubinTate.Valuations.NonarchimedeanAbsoluteValue v)
    (hv : ValuationTheory.DiscreteValuationField.HenselFactorizationProperty
      (absoluteValueValuationSubring v hnonarch))
    {x : L} (hx : finiteExtensionNormFormulaValue v x ≤ 1) :
    IsIntegral
      (absoluteValueValuationSubring v hnonarch) x := by
  let V := absoluteValueValuationSubring v hnonarch
  let : Algebra.IsAlgebraic K L := Algebra.IsAlgebraic.of_finite K L
  let : Algebra.IsIntegral K L := Algebra.IsAlgebraic.isIntegral
  have hxint : IsIntegral K x := Algebra.IsIntegral.isIntegral x
  have hconst : v ((minpoly K x).coeff 0) ≤ 1 :=
    (normFormula_finiteExtensionNormFormulaValue_le_one_iff_minpoly_coeff_zero_le_one
      v x).1 hx
  have hcoeff : ∀ i : ℕ, v ((minpoly K x).coeff i) ≤ 1 :=
    normFormula_monic_coeff_abs_le_one_of_const_abs_le_one_of_henselFactorization
      v hnonarch hv (minpoly.irreducible hxint) (minpoly.monic hxint) hconst
  rcases
      exists_polynomial_over_absoluteValueUnitBallSubringAsValuationSubring_of_coeff_abs_le_one
        v hnonarch (minpoly K x) hcoeff with
    ⟨F, hFmap, hFdegree, _hcoeff⟩
  have hφinj : Function.Injective (algebraMap V K) := by
    intro a b hab
    exact Subtype.ext hab
  have hFmonic : F.Monic := by
    apply Polynomial.monic_of_injective hφinj
    rw [hFmap]
    exact minpoly.monic hxint
  have hFdegree_ne : F.natDegree ≠ 0 := by
    rw [hFdegree]
    exact Nat.ne_of_gt (minpoly.natDegree_pos hxint)
  have hroot : (Polynomial.aeval x) F = 0 := by
    have hmaproot :
        (Polynomial.aeval x) (F.map (algebraMap V K)) = 0 := by
      rw [hFmap]
      exact minpoly.aeval K x
    rwa [Polynomial.aeval_map_algebraMap K x F] at hmaproot
  exact IsIntegral.of_aeval_monic hFmonic hFdegree_ne (by
    rw [hroot]
    exact isIntegral_zero)

end Valuations
end AlgebraicNumberTheory

end
