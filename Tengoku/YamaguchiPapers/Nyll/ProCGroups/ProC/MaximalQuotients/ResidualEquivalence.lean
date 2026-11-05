/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.MaximalQuotients.UniversalProperty
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Topologies.QuotientMaps
import Tengoku.Seed.Topology.Algebra.ContinuousMonoidHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuous equivalences of actual residual quotients

A continuous group equivalence carries the pro-C residual core onto the
corresponding core. Applying functoriality in both directions requires only
hereditariness of C, so total disconnectedness is unnecessary.
-/

namespace ProCGroups.ProC

universe u

variable {C : FiniteGroupClass.{u}}
variable {G H : Type u} [Group G] [Group H]
  [TopologicalSpace G] [TopologicalSpace H]
  [IsTopologicalGroup G] [IsTopologicalGroup H]
  [CompactSpace G] [CompactSpace H] [T2Space G] [T2Space H]

/-- A continuous equivalence of compact Hausdorff groups induces an
equivalence of their actual pro-C residual quotients.-/
noncomputable def residualQuotientContinuousMulEquiv
    (hC : FiniteGroupClass.Hereditary C) (e : G ≃ₜ* H) :
    G ⧸ proCResidualCore C G ≃ₜ* H ⧸ proCResidualCore C H := by
  have hforward : (proCResidualCore C G).map e.toMulEquiv.toMonoidHom ≤
      proCResidualCore C H :=
    map_proCResidualCore_le_of_hom hC e.toMulEquiv.toMonoidHom e.continuous_toFun
  have hbackward : (proCResidualCore C H).map e.symm.toMulEquiv.toMonoidHom ≤
      proCResidualCore C G :=
    map_proCResidualCore_le_of_hom hC e.symm.toMulEquiv.toMonoidHom e.symm.continuous_toFun
  have hmap : (proCResidualCore C G).map e.toMulEquiv.toMonoidHom =
      proCResidualCore C H := by
    apply le_antisymm hforward
    intro x hx
    exact ⟨e.symm x, hbackward ⟨x, hx, rfl⟩, e.apply_symm_apply x⟩
  exact QuotientGroup.congrₜ (proCResidualCore C G) (proCResidualCore C H) e hmap

/-- The induced equivalence applies the original equivalence to representatives.
@isnad1 id=eq.1h5v.s10.1d84f41c36f5 from=translated src=- shape=dc0c2050 vocab=cdeb9858
-/
@[simp] theorem residualQuotientContinuousMulEquiv_apply_mk
    (hC : FiniteGroupClass.Hereditary C) (e : G ≃ₜ* H) (x : G) :
    residualQuotientContinuousMulEquiv hC e
        (QuotientGroup.mk' (proCResidualCore C G) x) =
      QuotientGroup.mk' (proCResidualCore C H) (e x) := rfl

end ProCGroups.ProC
