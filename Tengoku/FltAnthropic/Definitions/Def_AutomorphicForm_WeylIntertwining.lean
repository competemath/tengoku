import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_AdelicLsXi
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_ConstantTerm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open Matrix MeasureTheory

namespace AutomorphicForm

section WeylElement

variable {K : Type*} [Field K]

def gl2Weyl : GL (Fin 2) K :=
  ⟨!![0, 1; 1, 0], !![0, 1; 1, 0], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two], by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two]⟩

/--
@isnad1 id=eq.0h1v.s8.1894c98cae6f from=translated src=- shape=9c464ae8 vocab=d9e201b9
-/
@[simp] theorem gl2Weyl_val :
    ((gl2Weyl : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; 1, 0] := rfl

/--
@isnad1 id=eq.0h1v.s6.a51fa5aba584 from=translated src=- shape=d34c833a vocab=7767e8b4
-/
theorem gl2Weyl_inv : (gl2Weyl : GL (Fin 2) K)⁻¹ = gl2Weyl := Units.ext rfl

end WeylElement

section Intertwining

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] [MeasurableSpace (NumberField.AdeleRing R K)]

def adelicWeyl : AdelicGL2 R K :=
  globalPoints R K gl2Weyl

def weylIntertwiningIntegral (ν : Measure (NumberField.AdeleRing R K))
    (f : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) : ℂ :=
  ∫ x, f ((adelicWeyl R K)⁻¹ * unipotentGL2 x * g) ∂ν

/--
@isnad1 id=eq.0h5v.s6.3106c84565d7 from=translated src=- shape=4107afe3 vocab=56a95891
-/
theorem weylIntertwiningIntegral_const (ν : Measure (NumberField.AdeleRing R K))
    [IsProbabilityMeasure ν] (c : ℂ) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K ν (fun _ => c) g = c := by
  unfold weylIntertwiningIntegral
  simp [integral_const, measureReal_def]

/--
@isnad1 id=eq.0h4v.s6.77e7a5bfc088 from=translated src=- shape=84c32dd5 vocab=39e94a59
-/
theorem weylIntertwiningIntegral_zero_measure (f : AdelicGL2 R K → ℂ) (g : AdelicGL2 R K) :
    weylIntertwiningIntegral R K 0 f g = 0 := by
  unfold weylIntertwiningIntegral
  simp

end Intertwining

end AutomorphicForm
