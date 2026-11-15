import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

namespace AutomorphicForm

variable {L : Type*} [Field L]

def sigmaConj (σ : L →+* L) (g δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    Matrix.GeneralLinearGroup (Fin 2) L :=
  g * δ * (Matrix.GeneralLinearGroup.map σ g)⁻¹

def IsSigmaConj (σ : L →+* L) (δ δ' : Matrix.GeneralLinearGroup (Fin 2) L) : Prop :=
  ∃ g, δ' = sigmaConj σ g δ

def sigmaConjClassOf (σ : L →+* L) (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    Set (Matrix.GeneralLinearGroup (Fin 2) L) :=
  {δ' | IsSigmaConj σ δ δ'}

/--
@isnad1 id=eq.0h3v.s7.a26c91493239 from=translated src=- shape=eac0b2a5 vocab=e1b98d8d
-/
theorem sigmaConj_one_left (σ : L →+* L) (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    sigmaConj σ 1 δ = δ := by
  simp [sigmaConj]

/--
@isnad1 id=issigmac.0h3v.s5.54c9faa1cca3 from=translated src=- shape=5778e10f vocab=e60c39b2
-/
theorem IsSigmaConj.refl (σ : L →+* L) (δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    IsSigmaConj σ δ δ :=
  ⟨1, (sigmaConj_one_left σ δ).symm⟩

/--
@isnad1 id=mem.0h3v.s7.27129dcd27fe from=translated src=- shape=dcd93444 vocab=4d1d5e95
-/
theorem mem_sigmaConjClassOf_self (σ : L →+* L)
    (δ : Matrix.GeneralLinearGroup (Fin 2) L) : δ ∈ sigmaConjClassOf σ δ :=
  IsSigmaConj.refl σ δ

/--
@isnad1 id=iff.0h4v.s8.6a2327ed0214 from=translated src=- shape=77044c8e vocab=d0e52787
-/
theorem mem_sigmaConjClassOf_iff (σ : L →+* L)
    (δ δ' : Matrix.GeneralLinearGroup (Fin 2) L) :
    δ' ∈ sigmaConjClassOf σ δ ↔ ∃ g, δ' = sigmaConj σ g δ :=
  Iff.rfl

/--
@isnad1 id=eq.0h3v.s9.caa7e9b8727b from=translated src=- shape=c14d2fa2 vocab=f91c6ab7
-/
theorem sigmaConj_id (g δ : Matrix.GeneralLinearGroup (Fin 2) L) :
    sigmaConj (RingHom.id L) g δ = g * δ * g⁻¹ := by
  have hmap : Matrix.GeneralLinearGroup.map (RingHom.id L) g = g := by
    ext i j
    simp [Matrix.GeneralLinearGroup.map]
  rw [sigmaConj, hmap]

end AutomorphicForm
