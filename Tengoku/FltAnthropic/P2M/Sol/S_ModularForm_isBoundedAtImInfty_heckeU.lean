import Tengoku.Seed.NumberTheory.ModularForms.QExpansion
import Tengoku.Seed.NumberTheory.ModularForms.BoundedAtCusp
import Tengoku.Seed.RingTheory.RootsOfUnity.Complex
import Tengoku.Seed.Algebra.Lie.OfAssociative
import Tengoku.Seed.Algebra.Algebra.Rat
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_HeckeOperator
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_isBoundedAtImInfty_heckeU.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_isBoundedAtImInfty_heckeU

set_option autoImplicit false

noncomputable section

open Complex Function Filter
open UpperHalfPlane hiding I
open scoped Real MatrixGroups ModularForm Manifold Topology

namespace M4cP1W2

open ModularForm ModularFormClass

section Matrices

variable (p j : ℕ)

/--
@isnad1 id=eq.0h2v.s6.5da266461262 from=translated src=- shape=e17c5257 vocab=ff328639
-/
theorem heckeMatrix_one_zero :
    ((heckeMatrix p j : GL (Fin 2) ℝ) : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp
  · rw [val_heckeMatrix hp]; rfl

end Matrices

section Regularity

variable {f : ℍ → ℂ} (k : ℤ) (p : ℕ)

/--
@isnad1 id=isbounde.1h3v.s4.003e36d63973 from=translated src=- shape=322fb79c vocab=67f871bc
-/
theorem isBoundedAtImInfty_heckeU (hf : IsBoundedAtImInfty f) :
    IsBoundedAtImInfty (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => IsBoundedAtImInfty g)
    (fun _ _ ha hb => ha.add hb) UpperHalfPlane.zero_form_isBoundedAtImInfty
    (fun j _ => hf.slash k (heckeMatrix_one_zero p j))

end Regularity

section Uniqueness

variable {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ}

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
@isnad1 id=isbounde.1h3v.s4.40562f8f4ee8 from=translated src=- shape=ccb25218 vocab=67f871bc
-/
theorem solution {f : UpperHalfPlane → ℂ} (hf : UpperHalfPlane.IsBoundedAtImInfty f) (k : ℤ) (p : ℕ) : UpperHalfPlane.IsBoundedAtImInfty (ModularForm.heckeU k p f) :=
  M4cP1W2.isBoundedAtImInfty_heckeU k p hf
