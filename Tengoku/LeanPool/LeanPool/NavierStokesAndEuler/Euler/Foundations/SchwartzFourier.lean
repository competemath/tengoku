/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module

public import Tengoku

/-!
The Fourier integral bundled with Schwartz regularity. Keeping the underlying function
explicit lets Sobolev norms expose their formula without exposing the analytic proofs
of Fourier inversion and rapid decay.
-/

@[expose] public section

noncomputable section

namespace EulerSobolev

open scoped SchwartzMap FourierTransform ContDiff

variable {V E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

/-- The ordinary Fourier integral with its Schwartz smoothness and decay proofs. -/
def schwartzFourier (f : 𝓢(V, E)) : 𝓢(V, E) where
  toFun := 𝓕 (f : V → E)
  smooth' := by
    have h : ContDiff ℝ ∞ ((𝓕 f : 𝓢(V, E)) : V → E) := (𝓕 f : 𝓢(V, E)).smooth'
    rw [SchwartzMap.fourier_coe] at h
    exact h
  decay' := by
    have h : ∀ k n : ℕ, ∃ C : ℝ, ∀ x : V,
        ‖x‖ ^ k * ‖iteratedFDeriv ℝ n ((𝓕 f : 𝓢(V, E)) : V → E) x‖ ≤ C :=
      (𝓕 f : 𝓢(V, E)).decay'
    rw [SchwartzMap.fourier_coe] at h
    exact h

/-- The bundled Schwartz transform has exactly the ordinary Fourier integral as its values.
@isnad1 id=eq.0h4v.s7.37a07584bc5e from=translated src=- shape=ac0d7582 vocab=feb50e0d
-/
theorem schwartzFourier_apply (f : 𝓢(V, E)) (x : V) :
    schwartzFourier f x = 𝓕 (f : V → E) x := rfl

/-- The ordinary Fourier integral as a continuous linear map on Schwartz functions. -/
def schwartzFourierCLM : 𝓢(V, E) →L[ℂ] 𝓢(V, E) where
  toFun := schwartzFourier
  map_add' := by
    intro f g
    exact (FourierTransform.fourierCLM (F := 𝓢(V, E)) ℂ 𝓢(V, E)).map_add f g
  map_smul' := by
    intro c f
    exact (FourierTransform.fourierCLM (F := 𝓢(V, E)) ℂ 𝓢(V, E)).map_smul c f
  cont := by
    exact (FourierTransform.fourierCLM (F := 𝓢(V, E)) ℂ 𝓢(V, E)).continuous

end EulerSobolev
