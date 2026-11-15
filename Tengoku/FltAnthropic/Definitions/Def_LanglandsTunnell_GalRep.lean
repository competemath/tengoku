import Tengoku.Seed.FieldTheory.Normal.Basic
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Tengoku.Seed.NumberTheory.NumberField.Basic
import Tengoku.Seed.Data.ZMod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace LanglandsTunnell

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

variable {L : Type} [Field L] [NumberField L] [IsGalois ℚ L]
  [Algebra L (AlgebraicClosure ℚ)] [IsScalarTower ℚ L (AlgebraicClosure ℚ)]

noncomputable def galRep (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3)) :
    Γℚ →* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3) :=
  e.toMonoidHom.comp (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L)

/--
@isnad1 id=eq.0h3v.s12.b71b0875ebda from=translated src=- shape=34078611 vocab=dafb877f
-/
@[simp] theorem galRep_apply (e : (L ≃ₐ[ℚ] L) ≃* Matrix.GeneralLinearGroup (Fin 2) (ZMod 3))
    (σ : Γℚ) :
    galRep e σ = e (AlgEquiv.restrictNormalHom (F := ℚ) (K₁ := AlgebraicClosure ℚ) L σ) := rfl

def IsRelDegree {G : Type*} [Group G] (H : Subgroup G) (σ : G) (n : ℕ) : Prop :=
  0 < n ∧ σ ^ n ∈ H ∧ ∀ m : ℕ, 0 < m → m < n → σ ^ m ∉ H

/--
@isnad1 id=isreldeg.0h2v.s4.d09eb3057187 from=translated src=- shape=5e5b3f96 vocab=32ce9c17
-/
theorem isRelDegree_one_top {G : Type*} [Group G] (σ : G) : IsRelDegree (⊤ : Subgroup G) σ 1 :=
  ⟨Nat.one_pos, trivial, fun m _ hm => absurd hm (by omega)⟩

end LanglandsTunnell
