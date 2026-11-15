import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicLevel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace NumberField.AdelicLevel

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

def weyl : GL (Fin 2) (AdeleRing R K) :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0],
    by simp [Matrix.one_fin_two],
    by simp [Matrix.one_fin_two]⟩

variable (N : Ideal R)

def principalLevel : Subgroup (GL (Fin 2) (AdeleRing R K)) :=
  levelOne R K N ⊓ (levelOne R K N).map (MulAut.conj (weyl R K)).toMonoidHom

/--
@isnad1 id=le.0h3v.s9.335facc0622c from=translated src=- shape=edd0f222 vocab=ce98e013
-/
theorem principalLevel_le_levelOne : principalLevel R K N ≤ levelOne R K N := inf_le_left

/--
@isnad1 id=iff.0h4v.s13.38bdf8b4ef96 from=translated src=- shape=e0192b52 vocab=cd571c35
-/
theorem mem_principalLevel_iff {g : GL (Fin 2) (AdeleRing R K)} :
    g ∈ principalLevel R K N ↔
      g ∈ levelOne R K N ∧ g ∈ (levelOne R K N).map (MulAut.conj (weyl R K)).toMonoidHom :=
  Iff.rfl

end NumberField.AdelicLevel

end
