import Tengoku.Seed.RingTheory.IntegralClosure.IntegrallyClosed
import Tengoku.Seed.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Tengoku.Seed.RingTheory.Ideal.Maximal
import Tengoku.Seed.Analysis.SpecialFunctions.Complex.Circle
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_GaloisRep
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

noncomputable section

open WeierstrassCurve CuspForm

namespace FLTPrelim

end FLTPrelim

namespace Tengoku.FltAnthropic.FreyPackage

open FLTPrelim

def ModularRepOfLevel (P : FreyPackage) (N : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 N) 2) (W : WeierstrassCurve ℤ)
      (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧ W.IsIntegralModelOf P.freyCurve ∧
    𝔪.IsMaximal ∧ (P.p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ N → ℓ ≠ P.p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

end Tengoku.FltAnthropic.FreyPackage

namespace WeierstrassCurve

def IsResiduallyModularOfLevel (W : WeierstrassCurve ℤ) (p M : ℕ) : Prop :=
  ∃ (f : CuspForm (CongruenceSubgroup.Gamma0 M) 2) (𝔪 : Ideal (integralClosure ℤ ℂ)),
    f.IsNormalizedEigenform ∧ 𝔪.IsMaximal ∧ (p : integralClosure ℤ ℂ) ∈ 𝔪 ∧
    ∀ ℓ : ℕ, ℓ.Prime → W.IsGoodPrimeFor ℓ → ¬ ℓ ∣ M → ℓ ≠ p →
      ∃ a : integralClosure ℤ ℂ, (a : ℂ) = ModularFormClass.qCoeff f ℓ ∧
        a - ((W.apOfModel ℓ : ℤ) : integralClosure ℤ ℂ) ∈ 𝔪

def IsResiduallyModular (W : WeierstrassCurve ℤ) (p : ℕ) : Prop :=
  ∃ M : ℕ, 0 < M ∧ W.IsResiduallyModularOfLevel p M

def IsModularModelOfConductorLevel (W : WeierstrassCurve ℤ) : Prop :=
  ∃ N : ℕ, 0 < N ∧ W.IsModularModelOfLevel N ∧
    ∀ ℓ : ℕ, ℓ.Prime → (ℓ : ℤ) ∣ W.Δ → ℓ ∣ N

theorem IsModularModelOfConductorLevel.isModularModel {W : WeierstrassCurve ℤ}
    (h : W.IsModularModelOfConductorLevel) : W.IsModularModel := by
  obtain ⟨N, hN, hmod, -⟩ := h
  exact ⟨N, hN, hmod⟩

def ModRepIsIrreducible (W : WeierstrassCurve ℤ) (n : ℕ) : Prop :=
  Affine.Point.GaloisRepIsIrreducible (K := AlgebraicClosure ℚ) ℚ
    (W.map (Int.castRingHom ℚ)) n

end WeierstrassCurve

namespace CuspForm

open ModularFormClass

open UpperHalfPlane in

theorem IsNormalizedEigenform.ne_zero {N : ℕ}
    {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNormalizedEigenform) :
    f ≠ 0 := by
  rintro rfl
  have h0 : qCoeff (0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) 1 = 0 := by
    have hcoe : ((0 : CuspForm (CongruenceSubgroup.Gamma0 N) 2) : ℍ → ℂ) = (0 : ℍ → ℂ) := rfl
    rw [qCoeff, hcoe, qExpansion_zero]
    simp
  exact zero_ne_one (h0 ▸ hf.qCoeff_one)

end CuspForm

end
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
