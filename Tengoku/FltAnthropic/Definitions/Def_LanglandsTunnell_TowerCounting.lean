import Tengoku.FltAnthropic.Definitions.Def_TaylorWiles_Primes
import Tengoku.Seed.FieldTheory.Galois.IsGaloisGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace LanglandsTunnell

open NumberField Ideal FrobeniusDensity

def oddJ : Finset ℕ := {1, 3, 5, 7}

variable {L : Type*} [Field L] [NumberField L] [IsGalois ℚ L]

open scoped Classical in

noncomputable def labelledCount (σ : L ≃ₐ[ℚ] L) (S₀ : Finset ℕ) (m : Fin 8) (ℓ : ℕ) : ℕ :=
  if ℓ ∈ S₀ then 0 else
  if hℓ : ℓ.Prime then
    {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver
          (𝓞 (FixedPoints.intermediateField
              (Subgroup.zpowers σ) : IntermediateField ℚ L)) |
      Nat.card ((𝓞 (FixedPoints.intermediateField
          (Subgroup.zpowers σ) : IntermediateField ℚ L)) ⧸ 𝔮) = ℓ ∧
      ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver 𝔮)
        (_ : Q.LiesOver (ratPrimeIdeal ℓ)) (_ : Q.inertia (L ≃ₐ[ℚ] L) = ⊥),
        haveI : Finite ((𝓞 L) ⧸ Q) :=
          finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal hℓ)
        arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q = σ ^ (m : ℕ)}.ncard
  else 0

open scoped Classical in

noncomputable def classIndicator (σ : L ≃ₐ[ℚ] L) (ℓ : ℕ) : ℕ :=
  if ∃ _ : ℓ.Prime, ∃ (Q : Ideal (𝓞 L)) (_ : Q.IsPrime) (_ : Q.LiesOver (ratPrimeIdeal ℓ))
        (_ : Q.inertia (L ≃ₐ[ℚ] L) = ⊥),
      haveI : Finite ((𝓞 L) ⧸ Q) :=
        finite_quotient_of_ne_bot (ne_bot_of_liesOver_ratPrimeIdeal ‹ℓ.Prime›)
      IsConj σ (arithFrobAt ℤ (L ≃ₐ[ℚ] L) Q)
  then 1 else 0

/--
@isnad1 id=le.0h3v.s6.df42a9a0f783 from=translated src=- shape=22403d97 vocab=c31c09b0
-/
theorem classIndicator_le_one (σ : L ≃ₐ[ℚ] L) (ℓ : ℕ) : classIndicator σ ℓ ≤ 1 := by
  unfold classIndicator; split <;> simp

end LanglandsTunnell
