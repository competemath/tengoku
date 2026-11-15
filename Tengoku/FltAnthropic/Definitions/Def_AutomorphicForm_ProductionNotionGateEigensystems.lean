import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_HeckeEigensystem

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open IsDedekindDomain NumberField

noncomputable section

namespace AutomorphicForm

/--
@isnad1 id=infinite.0h0v.s3.cbffaabd07df from=translated src=- shape=ed5d6145 vocab=a43bfcf4
-/
theorem infinite_heightOneSpectrum_ratO : Infinite (HeightOneSpectrum (𝓞 ℚ)) := by
  have hinj : Function.Injective
      (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm :=
    (Rat.HeightOneSpectrum.primesEquiv (R := 𝓞 ℚ)).symm.injective
  exact Infinite.of_injective _ hinj

def zeroSatakeEigensystem : HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := by
    intro h
    have h1 : (1 : 𝓞 ℚ) ∈ (⊥ : Ideal (𝓞 ℚ)) := h ▸ Submodule.mem_top
    exact one_ne_zero (Ideal.mem_bot.mp h1)
  a := fun _ => 0
  b := fun _ => 0

/--
@isnad1 id=eq.0h1v.s4.ef64061075b4 from=translated src=- shape=9b2ee232 vocab=a61370ff
-/
@[simp] theorem zeroSatakeEigensystem_a (v : HeightOneSpectrum (𝓞 ℚ)) :
    zeroSatakeEigensystem.a v = 0 := rfl

/--
@isnad1 id=eq.0h1v.s4.31dcd0f7ff62 from=translated src=- shape=9b2ee232 vocab=609e47f1
-/
@[simp] theorem zeroSatakeEigensystem_b (v : HeightOneSpectrum (𝓞 ℚ)) :
    zeroSatakeEigensystem.b v = 0 := rfl

def principalShapeEigensystem : HeckeEigensystem ℚ ℂ where
  level := ⊤
  level_ne_bot := by
    intro h
    have h1 : (1 : 𝓞 ℚ) ∈ (⊥ : Ideal (𝓞 ℚ)) := h ▸ Submodule.mem_top
    exact one_ne_zero (Ideal.mem_bot.mp h1)
  a := fun _ => 2
  b := fun _ => 1

end AutomorphicForm

end
