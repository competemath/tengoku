import Tengoku.Seed.Tactic.Ring
import Tengoku.Seed.Tactic.NormNum
import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_FreyPackage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FreyPackage_freyCurve_discriminant.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FreyPackage_freyCurve_discriminant

open WeierstrassCurve

theorem solution (P : FreyPackage) :
    P.freyCurve.Δ = (P.a * P.b * P.c) ^ (2 * P.p) / 2 ^ 8 := by
  have h : ((P.c : ℚ)) ^ P.p = (P.a : ℚ) ^ P.p + (P.b : ℚ) ^ P.p := by
    exact_mod_cast P.hFLT.symm
  have key : ((P.a : ℚ) * P.b * P.c) ^ (2 * P.p)
      = ((P.a : ℚ) ^ P.p) ^ 2 * ((P.b : ℚ) ^ P.p) ^ 2 * ((P.a : ℚ) ^ P.p + (P.b : ℚ) ^ P.p) ^ 2 := by
    rw [← h]
    ring
  rw [key]
  simp only [FreyPackage.freyCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
