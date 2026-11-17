import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_LocalConditions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRepAdic_toMatrix_sub_one_apply_mem_maximalIdeal_of_residual_isUnramifiedAt

set_option autoImplicit false
open IsLocalRing

/--
@isnad1 id=mem.3h8v.s11.364c03813c3a from=translated src=- shape=be2de7e7 vocab=b53be899
-/
theorem solution
    {A : Type} [CommRing A] [IsLocalRing A] (ρ : GaloisRepAdic A) {q : ℕ} (hunr : ρ.residual.IsUnramifiedAt q)
    (b : Module.Basis (Fin 2) A ρ.V) (P : ValuationSubring (AlgebraicClosure ℚ)) (hP : P.LiesOverPrime q)
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (hσ : σ ∈ P.inertiaSubgroupIn ℚ) (i j : Fin 2) :
    LinearMap.toMatrix b b (ρ.ρ σ) i j - (1 : Matrix (Fin 2) (Fin 2) A) i j ∈ IsLocalRing.maximalIdeal A := by

  have h1 : (ρ.ρ σ).baseChange (IsLocalRing.ResidueField A) = 1 := hunr P hP σ hσ

  have h2 := LinearMap.toMatrix_baseChange (IsLocalRing.ResidueField A) (ρ.ρ σ) b b
  rw [h1, LinearMap.toMatrix_one] at h2
  have h3 := congrFun (congrFun h2 i) j
  rw [Matrix.map_apply, IsLocalRing.ResidueField.algebraMap_eq] at h3

  rw [← IsLocalRing.residue_eq_zero_iff, map_sub, ← h3]
  have h4 : IsLocalRing.residue A ((1 : Matrix (Fin 2) (Fin 2) A) i j) = (1 : Matrix (Fin 2) (Fin 2) (IsLocalRing.ResidueField A)) i j := by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  rw [h4, sub_self]
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
