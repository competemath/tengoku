/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.GaloisCohomology.Topology.ContinuousH1Lifting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Cocycle lifting implies surjectivity on actual continuous H¹ -/

open CategoryTheory TopRep ContRepresentation

namespace ContinuousCohomology

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

theorem homogeneous_oneCocycle_eq_difference
    (X : TopRep.{u} ℤ G) (z : cocycles X 1) (g h : G) :
    ((homogeneousCochains X).iCycles 1 z).1 g h =
      (crossedHomOfCocycle X z).toFun h - (crossedHomOfCocycle X z).toFun g := by
  let σ := (homogeneousCochains X).iCycles 1 z
  have hz := ConcreteCategory.congr_hom ((homogeneousCochains X).iCycles_d 1 2) z
  have hd := congrArg (fun τ => τ 1 g h) (homogeneousCochains.d_apply X 1 σ)
  have hz' := congrArg (fun τ => τ.1 1 g h) hz
  change (((homogeneousCochains X).d 1 2).hom σ).1 1 g h = 0 at hz'
  rw [hd] at hz'
  simp only [d_succ, d_zero, TopRep.hom_sub,
    ContIntertwiningMap.sub_apply, coind₁ι_toFun, coind₁Map_toFun,
    ContinuousMap.const_apply, ContinuousMap.comp_apply, ConcreteCategory.hom_ofHom,
    ContinuousMap.sub_apply] at hz'
  exact sub_eq_zero.mp hz'

end ContinuousCohomology
