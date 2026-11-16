import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Adic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
namespace Tengoku.FltAnthropic.GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

def DetIsCyclotomic (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  (p : A) ∈ IsLocalRing.maximalIdeal A ∧
    ∀ (n : ℕ) (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) (a : ℕ),
      (∀ μ : AlgebraicClosure ℚ, μ ^ p ^ n = 1 → σ μ = μ ^ a) →
        LinearMap.det (ρ.ρ σ) - (a : A) ∈ Ideal.span {((p ^ n : ℕ) : A)}

def IsOrdinaryAt (ρ : GaloisRepAdic A) (p : ℕ) : Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime p →
    ∃ L : Submodule A ρ.V,
      (∃ b : Module.Basis (Fin 2) A ρ.V, L = A ∙ b 0) ∧
      (∀ σ ∈ P.decompositionSubgroup ℚ, ∀ v ∈ L, ρ.ρ σ v ∈ L) ∧
      (∀ σ ∈ P.inertiaSubgroupIn ℚ, ∀ v : ρ.V, ρ.ρ σ v - v ∈ L)

def IsUnipotentOnInertiaAt (ρ : GaloisRepAdic A) (q : ℕ) : Prop :=
  ∀ P : ValuationSubring (AlgebraicClosure ℚ), P.LiesOverPrime q →
    ∀ σ ∈ P.inertiaSubgroupIn ℚ, LinearMap.charpoly (ρ.ρ σ) = (Polynomial.X - 1) ^ 2

end Tengoku.FltAnthropic.GaloisRepAdic

namespace GaloisRep

def ordinaryCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => ρ.DetIsCyclotomic p ∧ ρ.IsOrdinaryAt p ∧
    ∀ q : ℕ, q.Prime → q ∉ S → ρ.IsUnramifiedAt q

def minimalOrdinaryCondition (𝒪 : Type) [CommRing 𝒪] (p : ℕ) (S : Finset ℕ) :
    ∀ ⦃A : Type⦄ [CommRing A] [IsLocalRing A] [Algebra 𝒪 A], GaloisRepAdic A → Prop :=
  fun _A _ _ _ ρ => ordinaryCondition 𝒪 p S ρ ∧
    ∀ q ∈ S, q.Prime → q ≠ p → ρ.IsUnipotentOnInertiaAt q

end GaloisRep
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
