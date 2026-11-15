import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicHaar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open NumberField

namespace AutomorphicForm

variable (K : Type) [Field K] [NumberField K]

noncomputable def rightConv (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ :=
  fun g =>
    (letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
     ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K))

/--
@isnad1 id=eq.0h4v.s9.faa4597446d2 from=translated src=- shape=a7bc15e4 vocab=6f7e3a4f
-/
theorem rightConv_apply (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K φ f g =
      (letI := AdelicHaar.glBorel (Fin 2) (𝓞 K) K
       ∫ x, φ (g * x) * f x ∂(AdelicHaar.adelicGLHaar (Fin 2) (𝓞 K) K)) :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.3c0c6ccea956 from=translated src=- shape=8f4ee353 vocab=52e39d5c
-/
theorem rightConv_zero_right (φ : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    rightConv K φ (fun _ => 0) = fun _ => 0 := by
  funext g
  simp [rightConv]

/--
@isnad1 id=eq.0h2v.s8.0885a4a768ed from=translated src=- shape=79f63d79 vocab=52e39d5c
-/
theorem rightConv_zero_left (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) :
    rightConv K (fun _ => 0) f = fun _ => 0 := by
  funext g
  simp [rightConv]

/--
@isnad1 id=eq.0h5v.s10.a9a67ef9caf4 from=translated src=- shape=59ad09c4 vocab=e143a30f
-/
theorem rightConv_comp_mul_left (φ f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ)
    (h g : GL (Fin 2) (AdeleRing (𝓞 K) K)) :
    rightConv K (fun x => φ (h * x)) f g = rightConv K φ f (h * g) := by
  simp only [rightConv, mul_assoc]

end AutomorphicForm
