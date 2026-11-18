import Tengoku.FltAnthropic.Definitions.Def_FreyPackage_ModMCarrier_Rescale

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_mdifferentiable_slash_heckeDiagMatrix.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_mdifferentiable_slash_heckeDiagMatrix

/--
@isnad1 id=mdiffere.1h3v.s8.f215535d6e6e from=translated src=- shape=0d2fddbd vocab=6ea445e6
-/
theorem solution (d : ℕ) (k : ℤ) {f : UpperHalfPlane → ℂ}
    (hf : MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ) f) :
    MDifferentiable (modelWithCornersSelf ℂ ℂ) (modelWithCornersSelf ℂ ℂ)
      (SlashAction.map k (ModularForm.heckeDiagMatrix d) f) :=
  MDifferentiable.slash hf k (ModularForm.heckeDiagMatrix d)
