import Tengoku.Seed.NumberTheory.ModularForms.QExpansion
import Tengoku.Seed.NumberTheory.ModularForms.BoundedAtCusp
import Tengoku.Seed.RingTheory.RootsOfUnity.Complex
import Tengoku.Seed.Algebra.Lie.OfAssociative
import Tengoku.Seed.Algebra.Algebra.Rat
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_HeckeOperator
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Modularity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_mdifferentiable_heckeT.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_mdifferentiable_heckeT

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

/--
@isnad1 id=mdiffere.1h3v.s8.8ad8d51c9bc7 from=translated src=- shape=820fb839 vocab=d0ed2265
-/
theorem mdifferentiable_heckeU (hf : MDiff f) : MDiff (heckeU k p f) :=
  Finset.sum_induction _ (fun g : ℍ → ℂ => MDiff g) (fun _ _ ha hb => ha.add hb)
    mdifferentiable_const (fun _ _ => hf.slash k _)

/--
@isnad1 id=mdiffere.1h3v.s8.625cd6c65b3c from=translated src=- shape=820fb839 vocab=f5e6a066
-/
theorem mdifferentiable_heckeT (hf : MDiff f) : MDiff (heckeT k p f) :=
  (mdifferentiable_heckeU k p hf).add (hf.slash k _)

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
@isnad1 id=mdiffere.1h3v.s7.1f789bd7daae from=translated src=- shape=bd7c73b7 vocab=f5e6a066
-/
theorem solution {f : UpperHalfPlane → ℂ} (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) (k : ℤ) (p : ℕ) : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) (ModularForm.heckeT k p f) :=
  M4cP1W2.mdifferentiable_heckeT k p hf
