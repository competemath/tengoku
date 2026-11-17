import Tengoku.Seed.RingTheory.Frobenius
import Tengoku.Seed.RingTheory.Ideal.Pointwise
import Tengoku.Seed.FieldTheory.Galois.IsGaloisGroup
import Tengoku.Seed.NumberTheory.RamificationInertia.Galois
import Tengoku.FltAnthropic.Definitions.Def_ArithFrobResidue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ArithFrob_isArithFrobAt_unique.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ArithFrob_isArithFrobAt_unique

set_option autoImplicit false
set_option maxRecDepth 8000
set_option maxHeartbeats 4000000

noncomputable section

namespace LanglandsTunnell
namespace P0RowsLabel

open MulAction
open scoped Pointwise

variable {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
  {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]

theorem isArithFrobAt_unique_impl {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal]
    [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]
    {σ₁ σ₂ : G} (h₁ : IsArithFrobAt A σ₁ P) (h₂ : IsArithFrobAt A σ₂ P)
    (hin : P.inertia G = ⊥) : σ₁ = σ₂ := by
  have e₁ := ArithFrobResidue.stabilizerHom_eq_frobenius ⟨σ₁, h₁.mem_stabilizer⟩ h₁
  have e₂ := ArithFrobResidue.stabilizerHom_eq_frobenius ⟨σ₂, h₂.mem_stabilizer⟩ h₂
  have heq :=
    ArithFrobResidue.stabilizerHom_injective_of_inertia_eq_bot (A := A) hin (e₁.trans e₂.symm)
  exact congrArg Subtype.val heq

variable [Finite G] [Algebra.IsInvariant A B G]

section Membership

variable {C : Type*} [CommRing C] [Algebra C B]

end Membership

end LanglandsTunnell.P0RowsLabel

set_option autoImplicit false
open MulAction
open scoped Pointwise

theorem solution {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    {G : Type*} [Group G] [MulSemiringAction G B] [SMulCommClass G A B]
    {P : Ideal B} [P.IsMaximal] [(P.under A).IsMaximal]
    [Fintype (A ⧸ P.under A)] [Finite (B ⧸ P)]
    {σ₁ σ₂ : G} (h₁ : IsArithFrobAt A σ₁ P) (h₂ : IsArithFrobAt A σ₂ P)
    (hin : P.inertia G = ⊥) : σ₁ = σ₂ := by
  exact LanglandsTunnell.P0RowsLabel.isArithFrobAt_unique_impl h₁ h₂ hin
