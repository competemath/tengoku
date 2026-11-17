import Tengoku.Seed.MeasureTheory.Group.FundamentalDomain
import Tengoku.Seed.Probability.ConditionalProbability
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul

set_option autoImplicit false

open IsDedekindDomain NumberField MeasureTheory
open AutomorphicForm NumberField.AdelicBox NumberField.AdelicHaar

attribute [local instance] NumberField.AdelicHaar.adeleBorel NumberField.AdelicHaar.borelSpace_adeleBorel
  NumberField.AdelicHaar.isAddHaarMeasure_adelicAddHaar

namespace RS9P

variable (F : Type) [Field F] [NumberField F]

/--
@isnad1 id=countabl.0h1v.s3.e0a6e0d4939d from=translated src=- shape=17207180 vocab=37122745
-/
theorem countable_numberField : Countable F :=
  Countable.of_equiv _ (Module.finBasis ℚ F).equivFun.toEquiv.symm

/--
@isnad1 id=countabl.0h1v.s8.fa58d571fff2 from=translated src=- shape=cae77a92 vocab=b4f98e5c
-/
scoped instance countable_principalSubgroup : Countable ↥(AdeleRing.principalSubgroup (𝓞 F) F) := by
  haveI : Countable F := countable_numberField F
  refine Function.Surjective.countable (f := fun k : F =>
    (⟨algebraMap F (AdeleRing (𝓞 F) F) k, k, rfl⟩ : ↥(AdeleRing.principalSubgroup (𝓞 F) F))) ?_
  rintro ⟨_, k, rfl⟩
  exact ⟨k, rfl⟩

/--
@isnad1 id=eq.1h3v.s9.485fd037d249 from=translated src=- shape=78d572ff vocab=e7608999
-/
theorem setIntegral_adelicBox_comp_add_right (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F), G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u)
    (x : AdeleRing (𝓞 F) F) :
    ∫ u in adelicBox F, G (u + x) ∂(adelicAddHaar (𝓞 F) F) =
      ∫ u in adelicBox F, G u ∂(adelicAddHaar (𝓞 F) F) := by
  set μ := adelicAddHaar (𝓞 F) F with hμ

  have h1 : ∫ u in adelicBox F, G (u + x) ∂μ = ∫ w in (fun u => u + x) '' adelicBox F, G w ∂μ := by
    have hme : MeasurableEmbedding (fun u : AdeleRing (𝓞 F) F => u + x) :=
      (Homeomorph.addRight x).measurableEmbedding
    conv_lhs => rw [← Set.preimage_image_eq (adelicBox F) (add_left_injective x)]
    rw [← hme.setIntegral_map, map_add_right_eq_self]

  have hFD : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F) (adelicBox F) μ :=
    isAddFundamentalDomain_adelicBox F μ
  have hFD' : IsAddFundamentalDomain (AdeleRing.principalSubgroup (𝓞 F) F)
      ((fun u => u + x) '' adelicBox F) μ := by
    refine hFD.image_of_equiv (ν := μ) (Equiv.addRight x) ?_ (Equiv.refl _) ?_
    · simpa using (measurePreserving_add_right μ (-x)).quasiMeasurePreserving
    · intro γ u
      show (γ +ᵥ u) + x = γ +ᵥ (u + x)
      simp only [AddSubgroup.vadd_def, vadd_eq_add, add_assoc]

  have hinv : ∀ (γ : AdeleRing.principalSubgroup (𝓞 F) F) (u : AdeleRing (𝓞 F) F), G (γ +ᵥ u) = G u := by
    rintro ⟨_, β, rfl⟩ u
    exact hG β u
  rw [h1]
  exact hFD'.setIntegral_eq hFD hinv

/--
@isnad1 id=eq.1h3v.s9.c240bb6c5183 from=translated src=- shape=78d572ff vocab=ac889746
-/
theorem integral_cond_adelicBox_comp_add_right (G : AdeleRing (𝓞 F) F → ℂ)
    (hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F), G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u)
    (x : AdeleRing (𝓞 F) F) :
    ∫ u, G (u + x) ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) =
      ∫ u, G u ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F)) := by
  simp only [ProbabilityTheory.cond, integral_smul_measure, setIntegral_adelicBox_comp_add_right F G hG x]

/--
@isnad1 id=eq.2h9v.s11.fd5ded4739df from=translated src=- shape=0d71c010 vocab=cf17418d
-/
theorem whittakerCoefficient_unipotentGL2_mul (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g))
    (α : F) (x : AdeleRing (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α (unipotentGL2 x * g) =
      ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) *
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g := by
  set a := algebraMap F (AdeleRing (𝓞 F) F) α with ha
  set G : AdeleRing (𝓞 F) F → ℂ := fun w => φ (unipotentGL2 w * g) * ψ (-(a * w)) with hGdef
  have hG : ∀ (β : F) (u : AdeleRing (𝓞 F) F), G (algebraMap F (AdeleRing (𝓞 F) F) β + u) = G u := by
    intro β u
    have h1 : ψ (-(a * algebraMap F (AdeleRing (𝓞 F) F) β)) = 1 := by
      rw [ha, ← map_mul, ← map_neg]; exact hψ _
    simp only [hGdef]
    rw [hper β u, mul_add, neg_add, AddChar.map_add_eq_mul, h1, one_mul]
  have hint : ∀ u : AdeleRing (𝓞 F) F,
      φ (unipotentGL2 u * (unipotentGL2 x * g)) * ψ (-(a * u)) = ψ (a * x) * G (u + x) := by
    intro u
    simp only [hGdef]
    rw [← mul_assoc, ← unipotentGL2_add, show -(a * u) = a * x + -(a * (u + x)) by ring,
      AddChar.map_add_eq_mul]
    ring
  show (∫ u, φ (unipotentGL2 u * (unipotentGL2 x * g)) * ψ (-(a * u))
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))) =
    ψ (a * x) * ∫ u, φ (unipotentGL2 u * g) * ψ (-(a * u))
      ∂(ProbabilityTheory.cond (adelicAddHaar (𝓞 F) F) (adelicBox F))
  simp_rw [hint]
  rw [integral_const_mul, integral_cond_adelicBox_comp_add_right F G hG x]

end RS9P
open scoped _root_.P2MW.S_AutomorphicForm_whittakerCoefficient_unipotentGL2_mul.RS9P

/--
@isnad1 id=eq.2h9v.s11.fd5ded4739df from=translated src=- shape=0d71c010 vocab=cf17418d
-/
theorem solution
    (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (ψ : AddChar (AdeleRing (𝓞 F) F) ℂ) (hψ : IsPrincipalInvariantAddChar F ψ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (g : AdelicGL2 (𝓞 F) F)
    (hper : ∀ (β : F) (u : AdeleRing (𝓞 F) F),
      φ (unipotentGL2 (algebraMap F (AdeleRing (𝓞 F) F) β + u) * g) = φ (unipotentGL2 u * g))
    (α : F) (x : AdeleRing (𝓞 F) F) :
    whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α (unipotentGL2 x * g) =
      ψ (algebraMap F (AdeleRing (𝓞 F) F) α * x) *
        whittakerCoefficient F (productionPinsOf F D U gen (adelicBox F)) ψ φ α g :=
  RS9P.whittakerCoefficient_unipotentGL2_mul F D U gen ψ hψ φ g hper α x
