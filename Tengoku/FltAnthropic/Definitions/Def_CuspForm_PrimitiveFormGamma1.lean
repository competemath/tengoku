import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open CongruenceSubgroup ModularFormClass
open scoped MatrixGroups

namespace CuspForm

variable {M : ℕ} {k : ℤ}

def HasNebentypus (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  ∀ γ : SL(2, ℤ), γ ∈ Gamma0 M → ∀ τ : UpperHalfPlane,
    g (γ • τ) =
      ε ((γ 1 1 : ℤ) : ZMod M) *
        ((((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) ^ k * g τ)

def IsEigenformWith (ε : DirichletCharacter ℂ M) (g : CuspForm (Gamma1 M) k) : Prop :=
  qCoeff g 1 = 1 ∧
  (∀ p : ℕ, p.Prime → ¬ p ∣ M → ∀ n : ℕ,
    qCoeff g (p * n) +
        ε (p : ZMod M) * (p : ℂ) ^ (k - 1) * (if p ∣ n then qCoeff g (n / p) else 0) =
      qCoeff g p * qCoeff g n) ∧
  (∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ M → ∀ n : ℕ, qCoeff g (ℓ * n) = qCoeff g ℓ * qCoeff g n) ∧
  HasNebentypus ε g

theorem IsEigenformWith.qCoeff_one {ε : DirichletCharacter ℂ M} {g : CuspForm (Gamma1 M) k}
    (h : IsEigenformWith ε g) : qCoeff g 1 = 1 := h.1

end CuspForm
