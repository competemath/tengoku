/-
Copyright (c) 2026 Arthur Freitas Ramos et al. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Freitas Ramos, David Barros Hulak, Ruy J. G. B. de Queiroz
-/
module

public import Tengoku.LeanPool.LeanPool.Kurosh.KuroshCoverAction
public import Tengoku.LeanPool.LeanPool.Kurosh.KuroshFreeFiber

/-!
# Kurosh Cover Connected

Adapted for Lean Pool from Arthur742Ramos/KuroshSubgroupTheorem,
commit `911707126c8b9bb0c764bf853008fe1053c0aad9`: imports, API compatibility,
and proof organization were revised.
-/

@[expose] public section

open Set Function
open CategoryTheory
open scoped Pointwise
noncomputable section

/-- Classical equality used locally in this part of the Kurosh construction. -/
local instance GraphCoveringTheory.Kurosh.kuroshCoverConnectedDecidableEq
    (α : Type*) : DecidableEq α := Classical.decEq α

universe u v

namespace GraphCoveringTheory.Kurosh

/--
@isnad1 id=nonempty.0h4v.s8.142719deba09 from=translated src=- shape=f81fe1a4 vocab=001e6292
-/
theorem Internal.coverFreeFactorLoopPath {ι : Type v}
    (G : ι → Type u) [∀ i, Group (G i)] (H : Subgroup (FreeProduct G))
    (x : KuroshFreePart G H) :
    Nonempty (@Quiver.Path (Quiver.Symmetrify (CoverVertex G H)) _
      (coverVertexMk G H (rawBassSerreOrbitRoot G H) 1)
    (coverVertexMk G H (rawBassSerreOrbitRoot G H)
        (treeKuroshFreeInclusion G H x))) := by
  let z : KuroshFreePart G H := x⁻¹
  obtain ⟨q, hq⟩ := Internal.coverFreePath_exists G H
    (a := rawBassSerreOrbitRoot G H)
    (b := rawBassSerreOrbitRoot G H) z
  have hloop : coverPathFreeLoop G H q = x⁻¹ := by
    unfold coverPathFreeLoop
    rw [coverQuotientTreePathHom_root]
    simp only [Groupoid.inv_eq_inv]
    simp only [IsIso.inv_id, Category.comp_id]
    exact hq
  have hvalue : coverPathValue G H q =
      treeKuroshFreeInclusion G H x := by
    calc
      coverPathValue G H q =
          (treeKuroshFreeInclusion G H
            (coverPathFreeLoop G H q))⁻¹ :=
        coverPathValue_formula G H q
      _ = (treeKuroshFreeInclusion G H (x⁻¹))⁻¹ := by rw [hloop]
      _ = treeKuroshFreeInclusion G H x := by simp
  let lp := coverPathLift G H (1 : CoverSource G H) q
  have hp : lp.1 = treeKuroshFreeInclusion G H x := by
    dsimp [lp]
    rw [coverPathLift_value, hvalue]
    simp
  refine ⟨lp.2.cast rfl (congrArg
    (coverVertexMk G H (rawBassSerreOrbitRoot G H)) hp)⟩

end GraphCoveringTheory.Kurosh
