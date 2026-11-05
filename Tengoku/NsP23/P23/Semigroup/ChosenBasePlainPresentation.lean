import Tengoku.NsP23.P23.Semigroup.ChosenBaseMinimality
import Tengoku.NsP23.P23.Monomial.PlainMonomialIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Genuine exponent presentation extracted from frozen budget-zero minimality.
No normalization, H-L5 or rho exclusion is applied here. -/
namespace P23.Semigroup
noncomputable section
open P23.Monomial P23.Presentation

theorem chosenBase_plain_exponentPresentation_of_budget_zero
    (D : FourGeneratedNumericalSemigroup) (i : Fin 4)
    (hB : D.fourBaseBudget i = 0) :
    ∃ G : Finset PlainExp, plainMonomialIdeal ℚ G = chosenBaseDefiningIdeal D i ∧
      G.card = D.semigroupRho ∧ HasMinimalGeneratorCard (plainMonomialIdeal ℚ G) G.card := by
  classical
  obtain ⟨H,hspan,hcard,hmono,hmin⟩ :=
    chosenBase_minimalMonomialPresentation_of_budget_zero (k := ℚ) D i hB
  let f : ↥H → PlainExp := fun h => Classical.choose (hmono h.1 h.2)
  have hf (h : ↥H) : MvPolynomial.monomial (f h) (1 : ℚ) = h.1 :=
    (Classical.choose_spec (hmono h.1 h.2)).1.symm
  have hinj : Function.Injective f := by
    intro s t he
    apply Subtype.ext
    rw [← hf s,← hf t,he]
  let G : Finset PlainExp := Finset.univ.image f
  have hi : (fun p => MvPolynomial.monomial p (1 : ℚ)) '' (↑G : Set PlainExp) = ↑H := by
    ext p
    constructor
    · rintro ⟨g,hg,rfl⟩
      obtain ⟨h,_,rfl⟩ := Finset.mem_image.mp hg
      change MvPolynomial.monomial (f h) (1 : ℚ) ∈ H
      rw [hf h]
      exact h.2
    · intro hp
      let h : ↥H := ⟨p,hp⟩
      exact ⟨f h,Finset.mem_image.mpr ⟨h,Finset.mem_univ _,rfl⟩,hf h⟩
  have hI : plainMonomialIdeal ℚ G = chosenBaseDefiningIdeal D i := by
    unfold plainMonomialIdeal
    rw [hi]
    exact hspan
  have hc : G.card = D.semigroupRho := by
    dsimp only [G]
    rw [Finset.card_image_of_injective _ hinj]
    simpa using hcard
  refine ⟨G,hI,hc,?_⟩
  rw [hI,hc]
  exact hmin

end
end P23.Semigroup
