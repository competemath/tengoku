import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AdicCompletion_isAdicComplete_map_algebraMap_of_fg.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AdicCompletion_isAdicComplete_map_algebraMap_of_fg

set_option autoImplicit false

universe u

/--
@isnad1 id=isadicco.1h2v.s8.c6b1350c3371 from=translated src=- shape=e8ad8ef9 vocab=8232daf3
-/
theorem solution
    {B : Type u} [CommRing B] (I : Ideal B) (hI : I.FG) :
    IsAdicComplete (I.map (algebraMap B (AdicCompletion I B))) (AdicCompletion I B) := by
  rw [IsAdicComplete.map_algebraMap_iff]
  exact AdicCompletion.isAdicComplete hI
