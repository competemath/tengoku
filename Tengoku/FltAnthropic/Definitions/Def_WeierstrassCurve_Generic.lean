import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

universe u v

noncomputable section

open MvPolynomial

namespace WeierstrassCurve.Generic

section CommRing

variable (K : Type u) [CommRing K]

def poly : WeierstrassCurve (MvPolynomial (Fin 5) K) :=
  ⟨X 0, X 1, X 2, X 3, X 4⟩

/--
@isnad1 id=eq.0h1v.s5.d82f2b6cfc92 from=translated src=- shape=91f3866f vocab=37daef9b
-/
@[simp] theorem poly_a₁ : (poly K).a₁ = X 0 := rfl
/--
@isnad1 id=eq.0h1v.s5.f2a2912ae28e from=translated src=- shape=91f3866f vocab=0f44845b
-/
@[simp] theorem poly_a₂ : (poly K).a₂ = X 1 := rfl
/--
@isnad1 id=eq.0h1v.s5.3aebda87a107 from=translated src=- shape=91f3866f vocab=800bed44
-/
@[simp] theorem poly_a₃ : (poly K).a₃ = X 2 := rfl
/--
@isnad1 id=eq.0h1v.s5.59a4f34fd4fd from=translated src=- shape=91f3866f vocab=e0884e9f
-/
@[simp] theorem poly_a₄ : (poly K).a₄ = X 3 := rfl
/--
@isnad1 id=eq.0h1v.s5.4c0b56539441 from=translated src=- shape=91f3866f vocab=8c39dd2a
-/
@[simp] theorem poly_a₆ : (poly K).a₆ = X 4 := rfl

variable {K}

section coeffs

variable {A : Type v}

def coeffs (W : WeierstrassCurve A) : Fin 5 → A := ![W.a₁, W.a₂, W.a₃, W.a₄, W.a₆]

/--
@isnad1 id=eq.0h2v.s4.948f21d3db73 from=translated src=- shape=d75d604e vocab=28eca897
-/
@[simp] theorem coeffs_zero (W : WeierstrassCurve A) : coeffs W 0 = W.a₁ := rfl
/--
@isnad1 id=eq.0h2v.s4.430d41918dee from=translated src=- shape=d75d604e vocab=bbd2627f
-/
@[simp] theorem coeffs_one (W : WeierstrassCurve A) : coeffs W 1 = W.a₂ := rfl
/--
@isnad1 id=eq.0h2v.s4.d009d3c77382 from=translated src=- shape=d75d604e vocab=efeec7fe
-/
@[simp] theorem coeffs_two (W : WeierstrassCurve A) : coeffs W 2 = W.a₃ := rfl
/--
@isnad1 id=eq.0h2v.s4.4c248441543b from=translated src=- shape=d75d604e vocab=45e7d5de
-/
@[simp] theorem coeffs_three (W : WeierstrassCurve A) : coeffs W 3 = W.a₄ := rfl
/--
@isnad1 id=eq.0h2v.s4.229f469587b6 from=translated src=- shape=d75d604e vocab=cb88e1f6
-/
@[simp] theorem coeffs_four (W : WeierstrassCurve A) : coeffs W 4 = W.a₆ := rfl

end coeffs

/--
@isnad1 id=eq.0h3v.s8.3a9ffedf9a92 from=translated src=- shape=16c55e9f vocab=b3678919
-/
theorem Δ_poly_map {A : Type v} [CommRing A] (f : MvPolynomial (Fin 5) K →+* A) :
    ((poly K).map f).Δ = f (poly K).Δ :=
  (poly K).map_Δ f

variable {A : Type v} [CommRing A] [Algebra K A]

variable (K) in

def classify (W : WeierstrassCurve A) : MvPolynomial (Fin 5) K →ₐ[K] A :=
  MvPolynomial.aeval (coeffs W)

/--
@isnad1 id=eq.0h4v.s7.d909eaefbe47 from=translated src=- shape=a1d16986 vocab=a5df7080
-/
@[simp] theorem classify_X (W : WeierstrassCurve A) (i : Fin 5) :
    classify K W (X i) = coeffs W i := by
  simp [classify]

/--
@isnad1 id=eq.0h3v.s8.761b4217a9bd from=translated src=- shape=fdc083f1 vocab=c94bbf2d
-/
@[simp] theorem poly_map_classify (W : WeierstrassCurve A) :
    (poly K).map (classify K W : MvPolynomial (Fin 5) K →+* A) = W := by
  rcases W with ⟨a₁, a₂, a₃, a₄, a₆⟩
  simp [poly, WeierstrassCurve.map, coeffs]

theorem eq_classify_of_poly_map_eq (W : WeierstrassCurve A) (f : MvPolynomial (Fin 5) K →ₐ[K] A)
    (hf : (poly K).map (f : MvPolynomial (Fin 5) K →+* A) = W) : f = classify K W := by
  refine MvPolynomial.algHom_ext fun i => ?_
  rw [classify_X]
  subst hf
  fin_cases i <;> rfl

variable (K) in

/--
@isnad1 id=ne.0h1v.s7.e51f4162a6fd from=translated src=- shape=fe3f3ec2 vocab=6adfe863
-/
theorem Δ_poly_ne_zero [Nontrivial K] : (poly K).Δ ≠ 0 := by
  intro h

  have h₁ : (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve K).Δ = 0 := by
    rw [← poly_map_classify (K := K) (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve K), Δ_poly_map, h,
      map_zero]
  have h₂ : (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).Δ = 0 := by
    rw [← poly_map_classify (K := K) (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K), Δ_poly_map, h,
      map_zero]
  simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈] at h₁ h₂
  have e : (1 : K) = 0 := by linear_combination (-11) * h₂ - 8 * h₁
  exact one_ne_zero e

end CommRing

section Field

variable (K : Type u) [Field K]

abbrev FunctionField : Type u := FractionRing (MvPolynomial (Fin 5) K)

abbrev Closure : Type u := AlgebraicClosure (FunctionField K)

def curve : WeierstrassCurve (Closure K) :=
  (poly K).map (algebraMap (MvPolynomial (Fin 5) K) (Closure K))

/--
@isnad1 id=eq.0h1v.s9.102dd166bf30 from=translated src=- shape=a0b599fc vocab=8229828f
-/
theorem curve_def : curve K = (poly K).map (algebraMap (MvPolynomial (Fin 5) K) (Closure K)) := rfl

/--
@isnad1 id=injectiv.0h1v.s10.06d89a5c6cdc from=translated src=- shape=eca9d57e vocab=031020a9
-/
theorem algebraMap_functionField_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin 5) K) (FunctionField K)) :=
  IsFractionRing.injective _ _

/--
@isnad1 id=injectiv.0h1v.s10.3be8eab6648f from=translated src=- shape=cb3c4265 vocab=665fcfb1
-/
theorem algebraMap_closure_injective :
    Function.Injective (algebraMap (MvPolynomial (Fin 5) K) (Closure K)) := by
  rw [IsScalarTower.algebraMap_eq (MvPolynomial (Fin 5) K) (FunctionField K) (Closure K)]
  exact (algebraMap (FunctionField K) (Closure K)).injective.comp
    (algebraMap_functionField_injective K)

/--
@isnad1 id=eq.0h1v.s10.093239d8c5d8 from=translated src=- shape=50712c35 vocab=6227b6eb
-/
theorem Δ_curve : (curve K).Δ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (poly K).Δ :=
  (poly K).map_Δ _

/--
@isnad1 id=ne.0h1v.s7.80ebdfad8e72 from=translated src=- shape=436751ca vocab=16d32172
-/
theorem Δ_curve_ne_zero : (curve K).Δ ≠ 0 := by
  rw [Δ_curve]
  exact (map_ne_zero_iff _ (algebraMap_closure_injective K)).2 (Δ_poly_ne_zero K)

/--
@isnad1 id=isunit.0h1v.s6.54ac55df90d1 from=translated src=- shape=7f6d9421 vocab=648db78e
-/
theorem isUnit_Δ_curve : IsUnit (curve K).Δ :=
  (Δ_curve_ne_zero K).isUnit

/--
@isnad1 id=isellipt.0h1v.s5.9444e2b49804 from=translated src=- shape=aa7e0af4 vocab=f5a3e0c3
-/
instance isElliptic_curve : (curve K).IsElliptic := ⟨isUnit_Δ_curve K⟩

/--
@isnad1 id=eq.0h1v.s10.eb2e73d29c6a from=translated src=- shape=1cd2f205 vocab=c88deb8b
-/
@[simp] theorem curve_a₁ : (curve K).a₁ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 0) := rfl
/--
@isnad1 id=eq.0h1v.s10.d7b45ae9bf3c from=translated src=- shape=1cd2f205 vocab=76427d7a
-/
@[simp] theorem curve_a₂ : (curve K).a₂ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 1) := rfl
/--
@isnad1 id=eq.0h1v.s10.d57dcc7b00a2 from=translated src=- shape=1cd2f205 vocab=5dce8710
-/
@[simp] theorem curve_a₃ : (curve K).a₃ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 2) := rfl
/--
@isnad1 id=eq.0h1v.s10.febe4c87f4c2 from=translated src=- shape=1cd2f205 vocab=2be8ed92
-/
@[simp] theorem curve_a₄ : (curve K).a₄ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 3) := rfl
/--
@isnad1 id=eq.0h1v.s10.f2603bf345b4 from=translated src=- shape=1cd2f205 vocab=b8e52f3a
-/
@[simp] theorem curve_a₆ : (curve K).a₆ = algebraMap (MvPolynomial (Fin 5) K) (Closure K) (X 4) := rfl

/--
@isnad1 id=eq.0h2v.s12.46577dc83f00 from=translated src=- shape=cf6d8136 vocab=bbfefc25
-/
theorem curve_map_algEquiv (σ : Closure K ≃ₐ[FunctionField K] Closure K) :
    (curve K).map (σ : Closure K →+* Closure K) = curve K := by
  rw [curve_def, WeierstrassCurve.map_map]
  congr 1
  ext x
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 5) K) (FunctionField K) (Closure K)]
    exact σ.commutes _
  · simp only [RingHom.coe_comp, Function.comp_apply]
    rw [IsScalarTower.algebraMap_apply (MvPolynomial (Fin 5) K) (FunctionField K) (Closure K)]
    exact σ.commutes _

end Field

end WeierstrassCurve.Generic

end
