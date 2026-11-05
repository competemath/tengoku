import Tengoku.NsP23.P23.Monomial.PlainSmallPresentation
import Tengoku.NsP23.P23.OneTie.TwoBorderTypeOne
import Tengoku.NsP23.P23.Semigroup.ChosenBasePlainTrace
import Tengoku.NsP23.P23.Semigroup.ChosenBaseCanonicalQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The small-presentation baseline, without any NG hypothesis. -/
namespace P23.Semigroup
noncomputable section
open scoped BigOperators
open P23.Monomial P23.OneTie P23.Artin P23.Presentation

theorem exists_base_budget_le_one (D : FourGeneratedNumericalSemigroup) :
    ∃ i : Fin 4, D.fourBaseBudget i ≤ 1 := by
  by_contra hn
  push Not at hn
  have hh : (∑ i : Fin 4, 2) ≤ ∑ i : Fin 4, D.fourBaseBudget i :=
    Finset.sum_le_sum (fun i _ => by have := hn i; omega)
  have hb := D.fourBaseBudget_sum_le_four_global
  norm_num at hh
  omega

theorem budget_zero_rho_le_three_semigroupType_eq_one
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hb : D.fourBaseBudget i = 0) (hr : D.semigroupRho ≤ 3) : D.semigroupType = 1 := by
  obtain ⟨G,hI,hcard,hm⟩ := chosenBase_plain_exponentPresentation_of_budget_zero D i hb
  have hf := chosenBase_plainSurvivors_finite D i G hI
  have h0 := chosenBase_plain_unit_survives D i G hI
  let R := plainSurvivorRoots ℚ G hf
  have hR : R.Nonempty := plainSurvivorRoots_nonempty ℚ G hf h0
  have ha : PlainRootAntichain R := plainSurvivorRoots_antichain ℚ G hf
  have hG := plainGenerators_eq_border ℚ G hf (plainGenerators_antichain_of_minimal ℚ G hm)
  let E := chosenBasePlainQuotientEquiv D i G hI hf hG
  have hv : PlainVariablesSurvive R := chosenBase_plain_variables_survive D i G hI hf
  have hc : R.card = 1 := plain_small_minimal_presentation_root_card_one ℚ G hf hv hG
    (by rw [hcard]; exact hr)
  have ht := (plainDirectType_eq_rootCard (k:=ℚ) R hR ha).trans hc
  rw [chosenPlain_type_eq R hR E,chosenBaseType_eq_semigroupType] at ht
  exact ht

theorem budget_one_rho_le_three_semigroupType_eq_one
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hb : D.fourBaseBudget i = 1) (hr : D.semigroupRho ≤ 3) : D.semigroupType = 1 := by
  obtain ⟨B⟩ := budgetOneOneTieNormalization D i hb
  have hge := live_one_tie_border_card_ge_two B.roots B.roots_nonempty
    B.coordinates.liveDomain B.roots_live
  have hcard := B.border_card
  have he : (borderFinset B.roots).card = 2 := by omega
  have ht := live_two_border_quotient_type_eq_one ℚ B.roots B.roots_nonempty
    B.coordinates.liveDomain B.roots_live B.roots_antichain he
  rw [B.canonicalOneTieType_eq_chosenBaseType,chosenBaseType_eq_semigroupType] at ht
  exact ht

theorem semigroupRho_le_three_imp_type_one (D : FourGeneratedNumericalSemigroup)
    (hr : D.semigroupRho ≤ 3) : D.semigroupType = 1 := by
  obtain ⟨i,hi⟩ := exists_base_budget_le_one D
  have he : D.fourBaseBudget i = 0 ∨ D.fourBaseBudget i = 1 := by omega
  rcases he with hz | ho
  · exact budget_zero_rho_le_three_semigroupType_eq_one D i hz hr
  · exact budget_one_rho_le_three_semigroupType_eq_one D i ho hr

theorem semigroupType_ne_one_imp_rho_ge_four (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType ≠ 1) : 4 ≤ D.semigroupRho := by
  by_contra hn
  exact ht (semigroupRho_le_three_imp_type_one D (by omega))

theorem type_two_semigroupRho_ge_four (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 2) : 4 ≤ D.semigroupRho :=
  semigroupType_ne_one_imp_rho_ge_four D (by omega)

theorem type_three_semigroupRho_ge_four (D : FourGeneratedNumericalSemigroup)
    (ht : D.semigroupType = 3) : 4 ≤ D.semigroupRho :=
  semigroupType_ne_one_imp_rho_ge_four D (by omega)

structure SmallPresentationBaseline (D : FourGeneratedNumericalSemigroup) : Prop where
  smallRhoTypeOne : D.semigroupRho ≤ 3 → D.semigroupType = 1
  nonTypeOneRhoFour : D.semigroupType ≠ 1 → 4 ≤ D.semigroupRho
  typeTwoRhoFour : D.semigroupType = 2 → 4 ≤ D.semigroupRho
  typeThreeRhoFour : D.semigroupType = 3 → 4 ≤ D.semigroupRho

theorem smallPresentationBaseline (D : FourGeneratedNumericalSemigroup) :
    SmallPresentationBaseline D where
  smallRhoTypeOne := semigroupRho_le_three_imp_type_one D
  nonTypeOneRhoFour := semigroupType_ne_one_imp_rho_ge_four D
  typeTwoRhoFour := type_two_semigroupRho_ge_four D
  typeThreeRhoFour := type_three_semigroupRho_ge_four D

end
end P23.Semigroup
