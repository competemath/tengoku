import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_exists_charpoly_eq_twist.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_exists_charpoly_eq_twist

set_option autoImplicit false

open Polynomial IsLocalRing

namespace GaloisRepTwist

theorem charpoly_eq_X_sq_sub {A : Type*} [CommRing A] [Nontrivial A] {V : Type*} [AddCommGroup V]
    [Module A V] [Module.Free A V] [Module.Finite A V] (h2 : Module.finrank A V = 2)
    (T : Module.End A V) :
    T.charpoly = X ^ 2 - C (LinearMap.trace A V T) * X + C (LinearMap.det T) := by
  classical
  let b := Module.finBasisOfFinrankEq A V h2
  rw [← LinearMap.charpoly_toMatrix T b, Matrix.charpoly_fin_two, LinearMap.trace_eq_matrix_trace A b,
    LinearMap.det_toMatrix]

end GaloisRepTwist

open GaloisRepTwist in
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A)
    (θ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Aˣ)
    (hθ : ∃ L : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ L ∧
      ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, (∀ x ∈ L, σ x = x) → θ σ = 1) :
    ∃ ρ' : GaloisRepAdic A, ∀ σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ,
      LinearMap.charpoly (ρ'.ρ σ) =
        X ^ 2 - C (((θ σ : Aˣ) : A) * LinearMap.trace A ρ.V (ρ.ρ σ)) * X
          + C (((θ σ : Aˣ) : A) ^ 2 * LinearMap.det (ρ.ρ σ)) := by
  classical
  obtain ⟨L₂, hL₂fin, hL₂⟩ := hθ

  let ρt : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Module.End A ρ.V :=
    { toFun := fun σ => ((θ σ : Aˣ) : A) • ρ.ρ σ
      map_one' := by rw [map_one, map_one, Units.val_one, one_smul]
      map_mul' := fun σ τ => by
        rw [map_mul, map_mul, Units.val_mul, smul_mul_smul_comm] }
  have hρt : ∀ σ, ρt σ = ((θ σ : Aˣ) : A) • ρ.ρ σ := fun σ => rfl

  have hcont : GaloisActionIsAdicContinuous A ρt := by
    intro n
    obtain ⟨L₁, hL₁fin, hL₁⟩ := ρ.isAdicContinuous n
    haveI := hL₁fin
    haveI := hL₂fin
    refine ⟨L₁ ⊔ L₂, IntermediateField.finiteDimensional_sup L₁ L₂, fun σ hσ v => ?_⟩
    have h1 : ∀ x ∈ L₁, σ x = x := fun x hx => hσ x ((le_sup_left : L₁ ≤ L₁ ⊔ L₂) hx)
    have h2 : ∀ x ∈ L₂, σ x = x := fun x hx => hσ x ((le_sup_right : L₂ ≤ L₁ ⊔ L₂) hx)
    have hθ1 : θ σ = 1 := hL₂ σ h2
    rw [hρt, hθ1, Units.val_one, one_smul]
    exact hL₁ σ h1 v
  let ρ' : GaloisRepAdic A :=
    { V := ρ.V
      finrank_eq := ρ.finrank_eq
      ρ := ρt
      isAdicContinuous := hcont }
  refine ⟨ρ', fun σ => ?_⟩
  show LinearMap.charpoly (ρt σ) = _
  rw [charpoly_eq_X_sq_sub ρ.finrank_eq (ρt σ), hρt, map_smul, LinearMap.det_smul, ρ.finrank_eq,
    smul_eq_mul]
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
