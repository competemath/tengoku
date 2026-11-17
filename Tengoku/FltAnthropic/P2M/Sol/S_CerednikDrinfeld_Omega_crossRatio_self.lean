import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_DrinfeldUpperHalfPlane

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Omega_crossRatio_self.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Omega_crossRatio_self

set_option autoImplicit false

open scoped MatrixGroups
open CerednikDrinfeld.Omega

theorem solution
    {K : Type*} [Field K] (z x y : K) (hzx : z ≠ x) (hzy : z ≠ y) :
    crossRatio z z x y = 1 := by
  have h : (z - y) * (z - x) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hzy) (sub_ne_zero.mpr hzx)
  rw [crossRatio, show (z - x) * (z - y) = (z - y) * (z - x) by ring, div_self h]
