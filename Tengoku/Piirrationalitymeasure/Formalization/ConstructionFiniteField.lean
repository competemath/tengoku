import Tengoku.Piirrationalitymeasure.Formalization.ConstructionPrimeSelection
import Tengoku.Piirrationalitymeasure.Formalization.FiniteFieldLaurent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Exact derivatives and local Laurent vanishing for the general reduced rational function. -/

namespace PiIrrationality

noncomputable def constructionFiniteFieldRational (a b c n p : ℕ) [Fact p.Prime] :
    RatFunc (ZMod p) :=
  algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (deletionNumerator p (a * n) (b * n)) /
    algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (deletionDenominator p (c * n))

/--
@isnad1 id=ex.1h5v.s10.eb22f0d9c4ba from=translated src=- shape=55dd452d vocab=a7c973c6
-/
theorem constructionRemovablePrime_derivative_quotient {a b c n p : ℕ} [Fact p.Prime]
    (hp : constructionRemovablePrime a b c n p) :
    ∃ N D : Polynomial (ZMod p), D ≠ 0 ∧ Polynomial.derivative D = 0 ∧
      constructionFiniteFieldRational a b c n p =
        algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) (Polynomial.derivative N) /
          algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p)) D := by
  let U := deletionNumerator p ((a * n) / p) ((b * n) / p)
  let V := evenPolynomialPrimitive p
    (finiteFieldH p ((a * n) % p) ((b * n) % p) ((c * n) % p))
  let D := (deletionDenominator p ((c * n) / p)) ^ p
  have hD : D ≠ 0 := pow_ne_zero _ (deletionDenominator_ne_zero p _)
  refine ⟨U ^ p * V, D, hD, derivative_pth_power_zmod p _, ?_⟩
  have hdV := evenPolynomialPrimitive_derivative p _
    (constructionRemovablePrime_obstructionFree hp)
  have hcross : deletionNumerator p (a * n) (b * n) * D =
      Polynomial.derivative (U ^ p * V) * deletionDenominator p (c * n) := by
    rw [← pth_power_mul_derivative_eq_derivative_mul, hdV]
    exact deletion_frobenius_cross_multiply p _ _ _
  unfold constructionFiniteFieldRational
  apply (div_eq_div_iff
    (RatFunc.algebraMap_ne_zero (deletionDenominator_ne_zero p _))
    (RatFunc.algebraMap_ne_zero hD)).2
  simpa only [map_mul] using congrArg
    (algebraMap (Polynomial (ZMod p)) (RatFunc (ZMod p))) hcross

/--
@isnad1 id=ex.1h6v.s9.222f1b6efed4 from=translated src=- shape=e4424a3d vocab=a8fb7781
-/
theorem constructionRemovablePrime_local_primitive {a b c n p : ℕ} [Fact p.Prime]
    (hp : constructionRemovablePrime a b c n p) (t : ZMod p) :
    ∃ W : LaurentSeries (ZMod p),
      localLaurent t (constructionFiniteFieldRational a b c n p) =
        LaurentSeries.derivative (ZMod p) W := by
  obtain ⟨N, D, _, hd, hR⟩ := constructionRemovablePrime_derivative_quotient hp
  refine ⟨localPolynomial t N / localPolynomial t D, ?_⟩
  rw [hR, localLaurent_derivative_quotient t N D hd]

/--
@isnad1 id=eq.2h6v.s8.26cebfa2e31b from=translated src=- shape=a290bc9c vocab=9c900f05
-/
theorem constructionRemovablePrime_local_coeff_zero {a b c n p : ℕ} [Fact p.Prime]
    (hp : constructionRemovablePrime a b c n p) (j : ℤ) (hj : (p : ℤ) ∣ j) :
    (localLaurent (-5 : ZMod p) (constructionFiniteFieldRational a b c n p)).coeff
      (-j - 1) = 0 := by
  obtain ⟨W, hW⟩ := constructionRemovablePrime_local_primitive hp (-5)
  rw [hW]
  exact laurent_derivative_coeff_zero W j hj

end PiIrrationality
