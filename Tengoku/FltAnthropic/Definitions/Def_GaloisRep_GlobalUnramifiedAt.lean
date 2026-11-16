import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace GlobalGaloisRep

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

def IsUnramifiedAt {G : Type*} [Monoid G] (ρ : (L ≃ₐ[K] L) →* G) (q : ℕ) : Prop :=
  ∀ A : ValuationSubring L, A.LiesOverPrime q → A.inertiaSubgroupIn K ≤ ρ.ker

/--
@isnad1 id=iff.0h5v.s9.a870115a8630 from=translated src=- shape=79a68291 vocab=557187f5
-/
lemma isUnramifiedAt_iff {G : Type*} [Monoid G] {ρ : (L ≃ₐ[K] L) →* G} {q : ℕ} :
    IsUnramifiedAt ρ q ↔
      ∀ A : ValuationSubring L, A.LiesOverPrime q →
        ∀ σ : L ≃ₐ[K] L, σ ∈ A.inertiaSubgroupIn K → ρ σ = 1 :=
  Iff.rfl

end GlobalGaloisRep
