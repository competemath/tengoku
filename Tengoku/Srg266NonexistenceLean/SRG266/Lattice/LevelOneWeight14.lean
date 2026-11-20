/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.NumberTheory.ModularForms.LevelOne.DimensionFormula

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open ModularGroup ModularForm
open scoped MatrixGroups

theorem levelOne_weight_fourteen_cusp_eq_zero
    (f : CuspForm 𝒮ℒ 14) : f = 0 := by
  have htwo : Module.rank ℂ (ModularForm 𝒮ℒ 2) = 0 :=
    ModularForm.levelOne_weight_two_rank_zero
  have hmap : CuspForm.discriminantEquiv f = 0 :=
    (rank_zero_iff_forall_zero.mp htwo) _
  exact CuspForm.discriminantEquiv.map_eq_zero_iff.mp hmap

end SRG266.Lattice
