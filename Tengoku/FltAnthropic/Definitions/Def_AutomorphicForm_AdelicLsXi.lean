import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open NumberField MeasureTheory Matrix

noncomputable section

namespace AutomorphicForm

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

abbrev AdelicGL2 : Type _ :=
  Matrix.GeneralLinearGroup (Fin 2) (AdeleRing R K)

def globalPoints : Matrix.GeneralLinearGroup (Fin 2) K →* AdelicGL2 R K :=
  Matrix.GeneralLinearGroup.map (algebraMap K (AdeleRing R K))

variable (Z : Subgroup (AdeleRing R K)ˣ) (ξ : Z →* ℂˣ)

variable [MeasureSpace (AdelicGL2 R K)] (D : Set (AdelicGL2 R K))

end AutomorphicForm

end
