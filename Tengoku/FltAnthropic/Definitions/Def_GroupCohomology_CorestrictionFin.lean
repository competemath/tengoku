import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_Corestriction2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open CategoryTheory groupCohomology

namespace groupCohomology
namespace Cores

def IsSlotInvariant {G : Type*} [Group G] {X : Type*} {n : ℕ} (U : Subgroup G) (u : (Fin n → G) → X) : Prop :=
  ∀ g s : Fin n → G, (∀ i, s i ∈ U) → u (g * s) = u g

variable {k G : Type} [CommRing k] [Group G] {H : Subgroup G}

def resFin (A : Rep.{0} k G) (n : ℕ) (u : (Fin n → G) → A) : (Fin n → H) → A :=
  fun h => u (fun i => (h i : G))

variable [H.FiniteIndex] (A : Rep.{0} k G) (τ : Transversal H)

attribute [local instance] fintypeQuot

noncomputable def corFin (n : ℕ) (u : (Fin n → H) → A) : (Fin n → G) → A := fun g =>
  ∑ q : G ⧸ H, A.ρ (τ.σ q)
    (u (fun i => (τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g (Fin.castSucc i)))⁻¹
                   * τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g i.succ)))

/--
@isnad1 id=eq.0h8v.s10.a78f43a153a3 from=translated src=- shape=c1fa55b7 vocab=647510a5
-/
lemma corFin_apply (n : ℕ) (u : (Fin n → H) → A) (g : Fin n → G) :
    corFin A τ n u g = ∑ q : G ⧸ H, A.ρ (τ.σ q)
      (u (fun i => (τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g (Fin.castSucc i)))⁻¹
                     * τ.lam ((τ.σ q)⁻¹ * Fin.partialProd g i.succ))) := rfl

end Cores
end groupCohomology
