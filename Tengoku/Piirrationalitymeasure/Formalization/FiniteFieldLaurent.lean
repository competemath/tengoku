import Tengoku.Piirrationalitymeasure.Formalization.FiniteFieldRational
import Tengoku.Piirrationalitymeasure.Formalization.LaurentDerivative

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
The local Laurent expansion at an arbitrary finite point, applied at `t = -5`
to the finite-field rational function in Lemma 2.2.
-/

namespace PiIrrationality

open HahnSeries

noncomputable def localPolynomial {K : Type*} [Field K] (a : K) :
    Polynomial K →ₐ[K] LaurentSeries K :=
  Polynomial.aeval (single 1 1 + algebraMap K (LaurentSeries K) a)

/--
@isnad1 id=eq.0h2v.s9.523f71969566 from=translated src=- shape=d5ae1903 vocab=77f0f307
-/
theorem localPolynomial_eq_comp {K : Type*} [Field K] (a : K) :
    (localPolynomial a).toRingHom =
      (algebraMap (Polynomial K) (LaurentSeries K)).comp
        (Polynomial.algEquivAevalXAddC a).toRingEquiv.toRingHom := by
  ext x <;> simp [localPolynomial, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
    PowerSeries.algebraMap_apply']

/--
@isnad1 id=injectiv.0h2v.s8.e70146e4b235 from=translated src=- shape=3396dd30 vocab=c4722e11
-/
theorem localPolynomial_injective {K : Type*} [Field K] (a : K) :
    Function.Injective (localPolynomial a) := by
  change Function.Injective (localPolynomial a).toRingHom
  rw [localPolynomial_eq_comp]
  exact (Polynomial.algebraMap_hahnSeries_injective ℤ).comp
    (Polynomial.algEquivAevalXAddC a).injective

/--
@isnad1 id=eq.0h3v.s10.828d9ecb9e68 from=translated src=- shape=a0ed0b01 vocab=89b266e3
-/
theorem localPolynomial_derivative {K : Type*} [Field K] (a : K)
    (P : Polynomial K) :
    laurentDerivation K (localPolynomial a P) =
      localPolynomial a (Polynomial.derivative P) := by
  have hx : laurentDerivation K (single 1 1) = 1 := by
    change LaurentSeries.derivative K (single 1 1) = 1
    simp [LaurentSeries.derivative, LaurentSeries.hasseDeriv_single, single_zero_one]
  unfold localPolynomial
  rw [Derivation.map_aeval, map_add, Derivation.map_algebraMap, hx, add_zero]
  exact smul_eq_mul _ _ |>.trans (mul_one _)

noncomputable def localLaurent {K : Type*} [Field K] (a : K) :
    RatFunc K →+* LaurentSeries K :=
  RatFunc.liftRingHom (localPolynomial a).toRingHom
    (fun _ hf => map_mem_nonZeroDivisors _ (localPolynomial_injective a) hf)

/--
@isnad1 id=eq.0h4v.s10.3dc389e0eade from=translated src=- shape=39245fc7 vocab=4d4f9e5a
-/
theorem localLaurent_div {K : Type*} [Field K] (a : K) (N D : Polynomial K) :
    localLaurent a (algebraMap (Polynomial K) (RatFunc K) N /
      algebraMap (Polynomial K) (RatFunc K) D) =
        localPolynomial a N / localPolynomial a D :=
  RatFunc.liftRingHom_apply_div _ _ _ _

/--
@isnad1 id=eq.1h4v.s11.66235baa3d6f from=translated src=- shape=f5e7447a vocab=a7a581c0
-/
theorem localLaurent_derivative_quotient {K : Type*} [Field K] (a : K)
    (N D : Polynomial K) (hD : Polynomial.derivative D = 0) :
    localLaurent a (algebraMap (Polynomial K) (RatFunc K) (Polynomial.derivative N) /
      algebraMap (Polynomial K) (RatFunc K) D) =
        LaurentSeries.derivative K (localPolynomial a N / localPolynomial a D) := by
  rw [localLaurent_div]
  change _ = laurentDerivation K (localPolynomial a N / localPolynomial a D)
  have hd : laurentDerivation K (localPolynomial a D) = 0 := by
    rw [localPolynomial_derivative, hD, map_zero]
  rw [Derivation.leibniz_div_const _ _ _ hd, localPolynomial_derivative]
  simp only [smul_eq_mul, div_eq_mul_inv, mul_comm]

/--
@isnad1 id=ex.1h3v.s9.4e10052abbcf from=translated src=- shape=1611b3c6 vocab=f91cbcbc
-/
theorem removablePrime_local_primitive {n p : ℕ} [Fact p.Prime]
    (hp : removablePrime n p) (a : ZMod p) :
    ∃ W : LaurentSeries (ZMod p),
      localLaurent a (finiteFieldRational n p) = LaurentSeries.derivative (ZMod p) W := by
  obtain ⟨N, D, _, hd, hR⟩ := removablePrime_derivative_quotient hp
  refine ⟨localPolynomial a N / localPolynomial a D, ?_⟩
  rw [hR, localLaurent_derivative_quotient a N D hd]

/--
@isnad1 id=eq.2h3v.s8.cf18dd248e82 from=translated src=- shape=faaf300e vocab=d32bee5c
-/
theorem removablePrime_local_coeff_zero {n p : ℕ} [Fact p.Prime]
    (hp : removablePrime n p) (j : ℤ) (hj : (p : ℤ) ∣ j) :
    (localLaurent (-5 : ZMod p) (finiteFieldRational n p)).coeff (-j - 1) = 0 := by
  obtain ⟨W, hW⟩ := removablePrime_local_primitive hp (-5)
  rw [hW]
  exact laurent_derivative_coeff_zero W j hj

end PiIrrationality
