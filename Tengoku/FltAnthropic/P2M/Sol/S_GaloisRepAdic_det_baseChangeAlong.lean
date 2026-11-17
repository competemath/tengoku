import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_det_baseChangeAlong.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_det_baseChangeAlong

theorem solution {A : Type} [CommRing A] [IsLocalRing A] {B : Type} [CommRing B] [IsLocalRing B] (φ : A →+* B) (hφ : IsLocalHom φ) (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : ((ρ.baseChangeAlong φ hφ).det σ : B) = φ (ρ.det σ : A) := by
  letI : Algebra A B := φ.toAlgebra
  show LinearMap.det ((ρ.ρ σ).baseChange B) = φ (LinearMap.det (ρ.ρ σ))
  exact LinearMap.det_baseChange (ρ.ρ σ)
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
