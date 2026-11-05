import Tengoku.NsP23.P23.Semigroup.ChosenBasePlainPresentation
import Tengoku.NsP23.P23.Monomial.PlainQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The actual chosen-base polynomial kernel, its finite intrinsic survivor set,
and its ordinary monomial quotient model. No H-L5 is used. -/
namespace P23.Semigroup
noncomputable section
open P23.Monomial

def chosenBasePlainPolynomialQuotientEquiv (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (G : Finset PlainExp) (hI : plainMonomialIdeal ℚ G = chosenBaseDefiningIdeal D i) :
    (TailPoly ℚ ⧸ plainMonomialIdeal ℚ G) ≃ₐ[ℚ] ChosenBaseQuotient (k := ℚ) D i :=
  (Ideal.quotientEquivAlgOfEq ℚ hI).trans (tailPolynomialQuotientEquiv D i)

/--
@isnad1 id=finite.1h3v.s6.b9c9869f7d3a from=translated src=- shape=a837ee86 vocab=82754251
-/
theorem chosenBase_plainSurvivors_finite (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (G : Finset PlainExp) (hI : plainMonomialIdeal ℚ G = chosenBaseDefiningIdeal D i) :
    (plainSurvivors ℚ G).Finite := by
  letI : Module.Finite ℚ (ChosenBaseQuotient (k := ℚ) D i) :=
    (chosenBaseEquivApery (k := ℚ) D i).symm.toLinearEquiv.finiteDimensional
  letI : Module.Finite ℚ (TailPoly ℚ ⧸ plainMonomialIdeal ℚ G) :=
    (chosenBasePlainPolynomialQuotientEquiv D i G hI).symm.toLinearEquiv.finiteDimensional
  exact plainSurvivors_finite ℚ G

/--
@isnad1 id=mem.1h3v.s6.0f43f8d9869e from=translated src=- shape=930ac78f vocab=7b158acf
-/
theorem chosenBase_plain_unit_survives (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (G : Finset PlainExp) (hI : plainMonomialIdeal ℚ G = chosenBaseDefiningIdeal D i) :
    (0 : PlainExp) ∈ plainSurvivors ℚ G := by
  change ¬MvPolynomial.monomial 0 (1 : ℚ) ∈ plainMonomialIdeal ℚ G
  rw [hI]
  intro hm
  have hz := RingHom.mem_ker.mp hm
  have hunit : (1 : ChosenBaseQuotient (k := ℚ) D i) = 0 := by simpa using hz
  let c : ChosenBaseQuotient (k := ℚ) D i →ₐ[ℚ] ℚ :=
    (aperyAugmentationAlgHom (k := ℚ) D i).comp (chosenBaseEquivApery D i).toAlgHom
  have hc := congrArg c hunit
  simpa using hc

/--
@isnad1 id=plainvar.2h3v.s6.877e7b2e565b from=translated src=- shape=5ff66312 vocab=b0725f01
-/
theorem chosenBase_plain_variables_survive (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (G : Finset PlainExp) (hI : plainMonomialIdeal ℚ G = chosenBaseDefiningIdeal D i)
    (hf : (plainSurvivors ℚ G).Finite) :
    PlainVariablesSurvive (plainSurvivorRoots ℚ G hf) := by
  intro j
  apply (plainSurvivorRoots_standard_iff ℚ G hf _).mpr
  change ¬MvPolynomial.monomial (plainUnitVector j) (1 : ℚ) ∈ plainMonomialIdeal ℚ G
  rw [hI]
  intro hm
  change MvPolynomial.X j ∈ chosenBaseDefiningIdeal (k := ℚ) D i at hm
  exact tailVariableChosenBase_ne_zero (k := ℚ) D i j (RingHom.mem_ker.mp hm)

def chosenBasePlainQuotientEquiv (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (G : Finset PlainExp) (hI : plainMonomialIdeal ℚ G = chosenBaseDefiningIdeal D i)
    (hf : (plainSurvivors ℚ G).Finite)
    (hG : G = plainBorderFinset (plainSurvivorRoots ℚ G hf)) :
    ChosenBaseQuotient (k := ℚ) D i ≃ₐ[ℚ] PlainMonomialArtin ℚ (plainSurvivorRoots ℚ G hf) :=
  (tailPolynomialQuotientEquiv D i).symm.trans
    ((Ideal.quotientEquivAlgOfEq ℚ
      ((congrArg (plainMonomialIdeal ℚ) hG).symm.trans hI).symm).trans
      (plainQuotientEquiv ℚ (plainSurvivorRoots ℚ G hf)))

end
end P23.Semigroup
