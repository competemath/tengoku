import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_CarrierPins
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_HeckeEigensystem
import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicLevel
import Tengoku.FltAnthropic.Definitions.Def_AbstractHeckeOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open IsDedekindDomain NumberField MulAction NumberField.AdelicLevel
open scoped Pointwise

noncomputable section

namespace AutomorphicForm

section Defs

variable (F : Type) [Field F] [NumberField F]

abbrev RightTranslationGroup : Type _ :=
  DomMulAct ((AdelicGL2 (𝓞 F) F)ᵐᵒᵖ)

def rightTranslationEmbed : AdelicGL2 (𝓞 F) F →* RightTranslationGroup F where
  toFun g := DomMulAct.mk (MulOpposite.op g)
  map_one' := rfl
  map_mul' _ _ := rfl

/--
@isnad1 id=eq.0h4v.s10.df01b696ae14 from=translated src=- shape=38a2705d vocab=636710e1
-/
@[simp] theorem rightTranslationEmbed_smul_apply (g x : AdelicGL2 (𝓞 F) F)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) :
    (rightTranslationEmbed F g • φ) x = φ (x * g) := rfl

def uniformizerIdele (v : HeightOneSpectrum (𝓞 F)) : (AdeleRing (𝓞 F) F)ˣ :=
  Units.map (finIncl (𝓞 F) F) (localUnit (𝓞 F) F v (uniformizerUnit F v))

end Defs

variable {F : Type} [Field F] [NumberField F]

def levelRT (pins : CarrierPins F) (N : Ideal (𝓞 F)) :
    Subgroup (RightTranslationGroup F) :=
  (pins.U N).map (rightTranslationEmbed F)

def IsHeckeEigenfunctionOf (pins : CarrierPins F) (ξ : pins.Z →* ℂˣ)
    (φ : AdelicGL2 (𝓞 F) F → ℂ) (Φ : HeckeEigensystem F ℂ) : Prop :=
  ∃ hmem : φ ∈ fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ),
    ∀ v : HeightOneSpectrum (𝓞 F), ¬ v.asIdeal ∣ Φ.level →
      (∃ hfin : (QuotientGroup.mk ''
            ((levelRT pins Φ.level : Set (RightTranslationGroup F))
              * {rightTranslationEmbed F (pins.gen v)}) :
            Set (RightTranslationGroup F ⧸ levelRT pins Φ.level)).Finite,
        AbstractHeckeOperator.HeckeOperator (R := ℂ)
            (rightTranslationEmbed F (pins.gen v))
            (levelRT pins Φ.level) (levelRT pins Φ.level) hfin ⟨φ, hmem⟩
          = Φ.a v •
            (⟨φ, hmem⟩ : fixedPoints (levelRT pins Φ.level) (AdelicGL2 (𝓞 F) F → ℂ)))
      ∧ ∃ hz : uniformizerIdele F v ∈ pins.Z,
          Φ.b v = (Nat.card ((𝓞 F) ⧸ v.asIdeal) : ℂ)
            * ((ξ ⟨uniformizerIdele F v, hz⟩ : ℂˣ) : ℂ)

namespace IsHeckeEigenfunctionOf

end IsHeckeEigenfunctionOf

end AutomorphicForm

end
