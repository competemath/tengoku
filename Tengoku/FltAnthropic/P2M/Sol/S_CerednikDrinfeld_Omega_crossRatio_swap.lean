import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Omega_crossRatio_swap.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Omega_crossRatio_swap

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

/--
@isnad1 id=eq.0h5v.s4.409ed94d0a6c from=translated src=- shape=856efcc1 vocab=bcb5cbdb
-/
theorem solution
    {K : Type*} [Field K] (z z₀ x y : K) :
    crossRatio z z₀ x y = crossRatio x y z z₀ := by
  simp only [crossRatio]
  rw [show (x - z) * (y - z₀) = (z - x) * (z₀ - y) by ring, show (x - z₀) * (y - z) = (z - y) * (z₀ - x) by ring]
