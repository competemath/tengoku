/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.MaximalQuotients.ResidualCore
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.OpenNormalSubgroups.ProCGroup
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Topologies.QuotientMaps
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic
import Tengoku.Seed.Topology.Algebra.ContinuousMonoidHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Residual quotients under inclusion of finite-group classes

Enlarging the finite-group class decreases its residual core. The identity
on the original group therefore induces a continuous surjection from the
larger-class residual quotient onto the smaller-class residual quotient.
This follows directly from the defining families of kernels and requires
neither a formation hypothesis nor compactness.
-/

namespace ProCGroups.ProC

universe u

variable {C D : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Inclusion of finite-group classes reverses inclusion of residual cores.
@isnad1 id=le.0h4v.s5.912e3a818861 from=translated src=- shape=a15835aa vocab=aea9b3e2
-/
theorem proCResidualCore_antitone
    (hCD : ∀ {Q : Type u} [Group Q], C Q → D Q) :
    proCResidualCore D G ≤ proCResidualCore C G := by
  change proCResidualCore D G ≤
    sInf (Set.range fun N : ProCQuotientKernel C G => N.toSubgroup)
  apply le_sInf
  intro N hN
  obtain ⟨NC, rfl⟩ := hN
  let ND : ProCQuotientKernel D G :=
    { toSubgroup := NC.toSubgroup
      isClosed' := NC.isClosed'
      normal := NC.normal
      quotient_hasOpenNormalBasisInClass :=
        NC.quotient_hasOpenNormalBasisInClass.mono hCD }
  change sInf (Set.range fun N : ProCQuotientKernel D G => N.toSubgroup) ≤ ND.toSubgroup
  exact sInf_le (Set.mem_range_self ND)

/-- The identity on the group induces the actual quotient map for an
inclusion of finite-group classes.-/
noncomputable def residualQuotientMapOfClassInclusion
    (hCD : ∀ {Q : Type u} [Group Q], C Q → D Q) :
    G ⧸ proCResidualCore D G →ₜ* G ⧸ proCResidualCore C G :=
  QuotientGroup.mapₜ (proCResidualCore D G) (proCResidualCore C G)
    (ContinuousMonoidHom.id G) (by
      intro x hx
      exact proCResidualCore_antitone hCD hx)

/-- The class-inclusion map retains the original group representative.
@isnad1 id=eq.0h5v.s9.5b81893189e0 from=translated src=- shape=a53240ce vocab=ee89083f
-/
@[simp] theorem residualQuotientMapOfClassInclusion_apply_mk
    (hCD : ∀ {Q : Type u} [Group Q], C Q → D Q) (x : G) :
    residualQuotientMapOfClassInclusion hCD
        (QuotientGroup.mk' (proCResidualCore D G) x) =
      QuotientGroup.mk' (proCResidualCore C G) x := rfl

/-- Every class in the smaller-class quotient has the same representative
in the larger-class quotient.
@isnad1 id=surjecti.0h4v.s8.e4381a18a61f from=translated src=- shape=d3ce6c80 vocab=72fe266d
-/
theorem residualQuotientMapOfClassInclusion_surjective
    (hCD : ∀ {Q : Type u} [Group Q], C Q → D Q) :
    Function.Surjective (residualQuotientMapOfClassInclusion (G := G) hCD) := by
  intro q
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (proCResidualCore C G) q
  exact ⟨QuotientGroup.mk' (proCResidualCore D G) x,
    residualQuotientMapOfClassInclusion_apply_mk hCD x⟩

end ProCGroups.ProC
