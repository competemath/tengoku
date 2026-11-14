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

theorem localPolynomial_eq_comp {K : Type*} [Field K] (a : K) :
    (localPolynomial a).toRingHom =
      (algebraMap (Polynomial K) (LaurentSeries K)).comp
        (Polynomial.algEquivAevalXAddC a).toRingEquiv.toRingHom := by
  ext x <;> simp [localPolynomial, HahnSeries.algebraMap_apply', PowerSeries.algebraMap_eq,
    PowerSeries.algebraMap_apply']

theorem localPolynomial_injective {K : Type*} [Field K] (a : K) :
    Function.Injective (localPolynomial a) := by
  change Function.Injective (localPolynomial a).toRingHom
  rw [localPolynomial_eq_comp]
  exact (Polynomial.algebraMap_hahnSeries_injective ℤ).comp
    (Polynomial.algEquivAevalXAddC a).injective

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

theorem localLaurent_div {K : Type*} [Field K] (a : K) (N D : Polynomial K) :
    localLaurent a (algebraMap (Polynomial K) (RatFunc K) N /
      algebraMap (Polynomial K) (RatFunc K) D) =
        localPolynomial a N / localPolynomial a D :=
  RatFunc.liftRingHom_apply_div _ _ _ _

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

theorem removablePrime_local_primitive {n p : ℕ} [Fact p.Prime]
    (hp : removablePrime n p) (a : ZMod p) :
    ∃ W : LaurentSeries (ZMod p),
      localLaurent a (finiteFieldRational n p) = LaurentSeries.derivative (ZMod p) W := by
  obtain ⟨N, D, _, hd, hR⟩ := removablePrime_derivative_quotient hp
  refine ⟨localPolynomial a N / localPolynomial a D, ?_⟩
  rw [hR, localLaurent_derivative_quotient a N D hd]

theorem removablePrime_local_coeff_zero {n p : ℕ} [Fact p.Prime]
    (hp : removablePrime n p) (j : ℤ) (hj : (p : ℤ) ∣ j) :
    (localLaurent (-5 : ZMod p) (finiteFieldRational n p)).coeff (-j - 1) = 0 := by
  obtain ⟨W, hW⟩ := removablePrime_local_primitive hp (-5)
  rw [hW]
  exact laurent_derivative_coeff_zero W j hj

end PiIrrationality
