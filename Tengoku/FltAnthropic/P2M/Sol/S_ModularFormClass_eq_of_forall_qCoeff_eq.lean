import Tengoku.Seed.NumberTheory.ModularForms.QExpansion
import Tengoku.Seed.NumberTheory.ModularForms.BoundedAtCusp
import Tengoku.Seed.RingTheory.RootsOfUnity.Complex
import Tengoku.Seed.Algebra.Lie.OfAssociative
import Tengoku.Seed.Algebra.Algebra.Rat
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_HeckeOperator
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularFormClass_eq_of_forall_qCoeff_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularFormClass_eq_of_forall_qCoeff_eq

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

namespace M4cP1W2

open ModularForm ModularFormClass

section Matrices

variable (p j : ℕ)

end Matrices

section Regularity

variable {f : ℍ → ℂ} (k : ℤ) (p : ℕ)

end Regularity

section Uniqueness

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

/--
@isnad1 id=hassum.1h5v.s7.2e6044798039 from=translated src=- shape=8910d5e3 vocab=c825276e
-/
theorem hasSum_qCoeff [ModularFormClass F Γ k] (f : F) (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (τ : ℍ) :
    HasSum (fun m ↦ qCoeff f m • Periodic.qParam 1 τ ^ m) (f τ) := by
  haveI : Fact (IsCusp OnePoint.infty Γ) := ⟨Γ.isCusp_of_mem_strictPeriods one_pos hΓ⟩
  exact hasSum_qExpansion one_pos (SlashInvariantFormClass.periodic_comp_ofComplex f hΓ)
    (holo f) (bdd_at_infty f) τ

theorem eq_of_forall_qCoeff_eq [ModularFormClass F Γ k] {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods)
    (h : ∀ n : ℕ, qCoeff f n = qCoeff g n) : f = g := by
  refine DFunLike.ext f g fun τ => ?_
  have hf := hasSum_qCoeff f hΓ τ
  have hg := hasSum_qCoeff g hΓ τ
  simp only [h] at hf
  exact hf.unique hg

end Uniqueness

section QExpAction

variable {p : ℕ} (hp : p ≠ 0)

variable {f : ℍ → ℂ} (hper : Periodic (f ∘ ofComplex) 1) (hhol : MDiff f)
  (hbdd : IsBoundedAtImInfty f)

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

end QExpAction

end M4cP1W2

end

/--
@isnad1 id=eq.2h5v.s7.671a7a324aa3 from=translated src=- shape=59ddcdc7 vocab=3d1e697a
-/
theorem solution {F : Type*} [FunLike F UpperHalfPlane ℂ] {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k] {f g : F} (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (h : ∀ n : ℕ, ModularFormClass.qCoeff f n = ModularFormClass.qCoeff g n) : f = g :=
  M4cP1W2.eq_of_forall_qCoeff_eq hΓ h
