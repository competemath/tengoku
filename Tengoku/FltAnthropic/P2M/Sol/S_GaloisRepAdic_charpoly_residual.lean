import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_charpoly_residual.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_charpoly_residual

open Polynomial

theorem solution {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) : LinearMap.charpoly (ρ.residual.ρ σ) = (LinearMap.charpoly (ρ.ρ σ)).map (IsLocalRing.residue A) := LinearMap.charpoly_baseChange (ρ.ρ σ) (IsLocalRing.ResidueField A)
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
