/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Topology.Algebra.Category.ProfiniteGrp.Basic
import Tengoku.Seed.Topology.Algebra.Group.Quotient
import Tengoku.Seed.Topology.Algebra.OpenSubgroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Topological profinite completion

This module defines the profinite completion of a topological group using its
open finite-index normal subgroups. The construction records the topology on
the source group, unlike the abstract profinite completion by all finite
quotients.
-/

noncomputable section

open CategoryTheory
open scoped Pointwise

namespace LocalClassFieldTheory

universe u

/-- An open normal subgroup whose quotient has finite cardinality.-/
def OpenFiniteIndexNormalSubgroup (G : Type u) [Group G] [TopologicalSpace G] :=
  { H : OpenNormalSubgroup G // H.toSubgroup.FiniteIndex }

namespace OpenFiniteIndexNormalSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The underlying open normal subgroup.-/
def toOpenNormalSubgroup (H : OpenFiniteIndexNormalSubgroup G) :
    OpenNormalSubgroup G :=
  H.1

/-- The finite-index witness carried by the subtype.
@isnad1 id=finitein.0h2v.s4.3d9d6c0e2dc2 from=translated src=- shape=8f83a4da vocab=05669998
-/
theorem finiteIndex' (H : OpenFiniteIndexNormalSubgroup G) :
    H.toOpenNormalSubgroup.toSubgroup.FiniteIndex :=
  H.2

/-- Finite-index open normal subgroups are determined by their underlying open normal subgroups.
@isnad1 id=eq.1h3v.s5.29fe35baad5f from=translated src=- shape=27c4d4a0 vocab=cd48d015
-/
@[ext]
theorem ext {H K : OpenFiniteIndexNormalSubgroup G}
    (h : H.toOpenNormalSubgroup = K.toOpenNormalSubgroup) : H = K :=
  Subtype.ext h

/-- An indexed open normal subgroup carries its finite-index witness as an instance.-/
instance (H : OpenFiniteIndexNormalSubgroup G) :
    H.toOpenNormalSubgroup.toSubgroup.FiniteIndex :=
  H.finiteIndex'

/-- Open finite-index normal subgroups are ordered by inclusion.-/
instance : PartialOrder (OpenFiniteIndexNormalSubgroup G) :=
  Subtype.partialOrder
    (fun H : OpenNormalSubgroup G => H.toSubgroup.FiniteIndex)

/-- The inclusion preorder makes open finite-index normal subgroups a small thin category.-/
instance : SmallCategory (OpenFiniteIndexNormalSubgroup G) :=
  Preorder.smallCategory _

/-- A morphism of open finite-index normal subgroups induces inclusion of the
underlying subgroups.
@isnad1 id=le.0h4v.s6.811ca01a15d1 from=translated src=- shape=0f04d10a vocab=94cb588e
-/
theorem le_of_hom {H K : OpenFiniteIndexNormalSubgroup G} (f : H ⟶ K) :
    H.toOpenNormalSubgroup.toSubgroup ≤ K.toOpenNormalSubgroup.toSubgroup := by
  have h : H ≤ K := CategoryTheory.leOfHom f
  change H.toOpenNormalSubgroup ≤ K.toOpenNormalSubgroup at h
  exact h

end OpenFiniteIndexNormalSubgroup

variable (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The functor of finite quotients attached to open finite-index normal
subgroups. Inclusion of subgroups induces the corresponding quotient map.-/
def openFiniteQuotientFunctor :
    OpenFiniteIndexNormalSubgroup G ⥤ FiniteGrp where
  obj H := FiniteGrp.of (G ⧸ H.toOpenNormalSubgroup.toSubgroup)
  map := fun hHK => FiniteGrp.ofHom <|
    QuotientGroup.map _ _ (.id _) (by
      simpa using OpenFiniteIndexNormalSubgroup.le_of_hom hHK)
  map_id _ := ConcreteCategory.ext <| QuotientGroup.map_id _
  map_comp f g := ConcreteCategory.ext <|
    (QuotientGroup.map_comp_map _ _ _ (.id _) (.id _)
      (by simpa using OpenFiniteIndexNormalSubgroup.le_of_hom f)
      (by simpa using OpenFiniteIndexNormalSubgroup.le_of_hom g)).symm

/-- The finite-quotient diagram, regarded in profinite groups with the
discrete topology on every finite stage.-/
noncomputable def openFiniteQuotientDiagram :
    OpenFiniteIndexNormalSubgroup G ⥤ ProfiniteGrp :=
  openFiniteQuotientFunctor G ⋙ forget₂ FiniteGrp ProfiniteGrp

/-- The finite profinite quotient attached to an open finite-index normal
subgroup.-/
noncomputable def openFiniteQuotient
    (H : OpenFiniteIndexNormalSubgroup G) : ProfiniteGrp :=
  (openFiniteQuotientDiagram G).obj H

/-- The product of all open finite quotients used to construct the completion.-/
abbrev openFiniteQuotientProduct : ProfiniteGrp :=
  ProfiniteGrp.pi (fun H : OpenFiniteIndexNormalSubgroup G =>
    openFiniteQuotient G H)

/-- The diagonal homomorphism to the product of all open finite quotients.-/
def openFiniteQuotientProductMapMonoidHom :
    G →* openFiniteQuotientProduct G where
  toFun g H := QuotientGroup.mk g
  map_one' := by
    funext H
    rfl
  map_mul' x y := by
    funext H
    rfl

/-- The diagonal map into the product of open finite quotients is continuous.
@isnad1 id=continuo.0h1v.s7.34c7c0582276 from=translated src=- shape=196491a5 vocab=13a0d626
-/
theorem openFiniteQuotientProductMapMonoidHom_continuous :
    Continuous (openFiniteQuotientProductMapMonoidHom G) := by
  apply continuous_pi
  intro H
  apply Continuous.mk
  intro s _
  change IsOpen ((fun g : G => (QuotientGroup.mk g : G ⧸ H.toOpenNormalSubgroup.toSubgroup)) ⁻¹' s)
  rw [← Set.biUnion_preimage_singleton QuotientGroup.mk s]
  refine isOpen_iUnion (fun i => isOpen_iUnion (fun _ => ?_))
  convert IsOpen.leftCoset
    H.toOpenNormalSubgroup.toOpenSubgroup.isOpen' (Quotient.out i)
  ext x
  simp only [Set.mem_preimage, Set.mem_singleton_iff]
  nth_rw 1 [← QuotientGroup.out_eq' i, eq_comm, QuotientGroup.eq]
  exact Iff.symm (Set.mem_smul_set_iff_inv_smul_mem)

/-- The topological profinite completion over open finite quotients, realized
as the closure of the diagonal image in their product.-/
noncomputable def TopologicalProfiniteCompletion : ProfiniteGrp :=
  ProfiniteGrp.ofClosedSubgroup
    { toSubgroup :=
        (MonoidHom.range (openFiniteQuotientProductMapMonoidHom G)).topologicalClosure
      isClosed' := Subgroup.isClosed_topologicalClosure _ }

/-- The canonical continuous homomorphism into the open-quotient completion.-/
def topologicalProfiniteCompletionMap :
    G →ₜ* TopologicalProfiniteCompletion G where
  toFun g :=
    ⟨openFiniteQuotientProductMapMonoidHom G g,
      Subgroup.le_topologicalClosure
        (MonoidHom.range (openFiniteQuotientProductMapMonoidHom G)) ⟨g, rfl⟩⟩
  map_one' := by
    apply Subtype.ext
    exact (openFiniteQuotientProductMapMonoidHom G).map_one
  map_mul' x y := by
    apply Subtype.ext
    exact (openFiniteQuotientProductMapMonoidHom G).map_mul x y
  continuous_toFun :=
    (openFiniteQuotientProductMapMonoidHom_continuous G).subtype_mk _

end LocalClassFieldTheory
