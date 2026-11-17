import Tengoku.Seed.LinearAlgebra.Determinant
import Tengoku.Seed.LinearAlgebra.Alternating.Basic
import Tengoku.Seed.LinearAlgebra.Multilinear.Basic
import Tengoku.Seed.LinearAlgebra.StdBasis
import Tengoku.Seed.Algebra.Module.Equiv.Basic
import Tengoku.Seed.Data.Nat.Factorial.Basic
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Scalar.FibreObstruction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Proof of Lemma F.4

Uses `FibreObstruction.not_exists_fibre_map` from
`AlternatingAnalytic/Scalar/FibreObstruction.lean`; the definitions below match those in
`FibreObstruction/Basic.lean`.
-/

namespace AlternatingAnalyticChallenge.LemF_4

universe u

variable (κ : Type u) [Field κ] (k : ℕ)

/-- The set `N` of linear forms `ε^a` and `ε^a + ε^b` (`a < b`) on `V = κ^{k+1}`.-/
def coordForms : Set ((Fin (k + 1) → κ) →ₗ[κ] κ) :=
  Set.range (fun a : Fin (k + 1) => LinearMap.proj (R := κ) (φ := fun _ => κ) a) ∪
    {ν | ∃ a b : Fin (k + 1), a < b ∧
      ν = LinearMap.proj (R := κ) (φ := fun _ => κ) a +
        LinearMap.proj (R := κ) (φ := fun _ => κ) b}

/-- `H'_{cd} = {z ∈ κ^k : z_c = z_d}`.-/
def colEq (c d : Fin k) : Submodule κ (Fin k → κ) :=
  LinearMap.ker
    (LinearMap.proj (R := κ) (φ := fun _ => κ) c - LinearMap.proj (R := κ) (φ := fun _ => κ) d)

/-- `C'_s = {z ∈ κ^k : z_s = 0}`.-/
def colZero (s : Fin k) : Submodule κ (Fin k → κ) :=
  LinearMap.ker (LinearMap.proj (R := κ) (φ := fun _ => κ) s)

/-- The finite family `F` of pairs `(Σ, Σ')` from (F.2).-/
def pairFamily : Set (Submodule κ (Fin (k + 1) → κ) × Submodule κ (Fin k → κ)) :=
  {P | ∃ c d : Fin k, c < d ∧ P = (⊤, colEq κ k c d)} ∪
    {P | ∃ ν ∈ coordForms κ k, ∃ s : Fin k, P = (LinearMap.ker ν, colZero κ k s)}

/-- The coordinate projection `g₀ : κ^{k+1} → κ^k` onto the first `k` coordinates.-/
def firstCoords : (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ) :=
  LinearMap.funLeft κ κ Fin.castSucc

/-- The determinant `δ'` on `V' = κ^k`.-/
noncomputable def detV' : (Fin k → κ) [⋀^Fin k]→ₗ[κ] κ :=
  (Pi.basisFun κ (Fin k)).det

/-- Condition (1): `τ(g₀, …, g₀) = δ' ∘ (g₀, …, g₀)`.-/
def FibreCondition1
    (τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
      ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ)) : Prop :=
  τ (fun _ => firstCoords κ k) = (detV' κ k).compLinearMap (firstCoords κ k)

/-- Condition (2): for every `(Σ, Σ') ∈ F`, `τ(g¹, …, gᵏ)` vanishes on `Σ^k` whenever every
`g^r` maps `Σ` into `Σ'`.-/
def FibreCondition2
    (τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
      ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ)) : Prop :=
  ∀ P ∈ pairFamily κ k, ∀ g : Fin k → ((Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ)),
    (∀ r, P.1.map (g r) ≤ P.2) →
      ∀ ξ : Fin k → (Fin (k + 1) → κ), (∀ r, ξ r ∈ P.1) → τ g ξ = 0

/-- Lemma F.4: if `k! = 0` in `κ`, no `k`-linear map
`τ : Hom_κ(κ^{k+1}, κ^k)^k → Alt^k_κ(κ^{k+1}; κ)` satisfies both conditions (1) and (2).-/
theorem not_exists_fibre_map (hk : (k.factorial : κ) = 0) :
    ¬ ∃ τ : MultilinearMap κ (fun _ : Fin k => (Fin (k + 1) → κ) →ₗ[κ] (Fin k → κ))
        ((Fin (k + 1) → κ) [⋀^Fin k]→ₗ[κ] κ),
      FibreCondition1 κ k τ ∧ FibreCondition2 κ k τ := by
  exact AlternatingAnalytic.FibreObstruction.not_exists_fibre_map hk

end AlternatingAnalyticChallenge.LemF_4
