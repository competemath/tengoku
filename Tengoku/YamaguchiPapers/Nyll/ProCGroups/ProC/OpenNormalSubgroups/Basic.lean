/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Topology.Algebra.ContinuousMonoidHom
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Profinite.OpenSubgroups
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Topologies.QuotientMaps
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Basic operations on open normal subgroups

This file develops bundled open normal subgroups, their finite discrete quotients and projections,
maps and comaps, transition morphisms, normal cores, and finite intersections.
-/

open scoped Topology

namespace ProCGroups.ProC

universe u v

variable {G : Type u} [Group G] [TopologicalSpace G]

namespace OpenNormalSubgroup

/-- Open normal subgroups have a top element: the whole group.-/
instance instTopOpenNormalSubgroup : Top (OpenNormalSubgroup G) :=
  ⟨{ toOpenSubgroup := ⊤
     isNormal' := by
       change (⊤ : Subgroup G).Normal
       infer_instance }⟩

/-- The kernel of a continuous homomorphism into a discrete group is an open normal subgroup.-/
def ker {Q : Type v} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →ₜ* Q) : OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup := f.toMonoidHom.ker
      isOpen' := by
        change IsOpen (f ⁻¹' ({1} : Set Q))
        exact (isOpen_discrete _).preimage f.continuous_toFun }
  isNormal' := by
    change f.toMonoidHom.ker.Normal
    infer_instance

/-- The underlying subgroup of OpenNormalSubgroup.kernel is the algebraic kernel.
@isnad1 id=eq.0h3v.s6.8ab30824f8e9 from=translated src=- shape=2c0b80f1 vocab=b42f4798
-/
@[simp, norm_cast]
theorem toSubgroup_ker {Q : Type v} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →ₜ* Q) :
    ((ker f : OpenNormalSubgroup G) : Subgroup G) = f.toMonoidHom.ker :=
  rfl

/-- Membership in the open normal kernel is exactly mapping to \(1\).
@isnad1 id=iff.0h4v.s6.bf87671b6f50 from=translated src=- shape=7d3c5d46 vocab=10725ff7
-/
@[simp]
theorem mem_ker {Q : Type v} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    {f : G →ₜ* Q} {x : G} :
    x ∈ ker f ↔ f x = 1 := by
  rfl

/--
An open surjective continuous homomorphism sends open normal subgroups to open normal subgroups.-/
def map {H : Type v} [Group H] [TopologicalSpace H]
    (f : G →ₜ* H) (hfopen : IsOpenMap f) (hfsurj : Function.Surjective f)
    (U : OpenNormalSubgroup G) : OpenNormalSubgroup H where
  toOpenSubgroup :=
    { toSubgroup := (U : Subgroup G).map f.toMonoidHom
      isOpen' := by
        change IsOpen (f '' ((U : Subgroup G) : Set G))
        exact hfopen _ (openNormalSubgroup_isOpen (G := G) U) }
  isNormal' := by
    change ((U : Subgroup G).map f.toMonoidHom).Normal
    exact Subgroup.Normal.map U.isNormal' f.toMonoidHom hfsurj

/-- The underlying subgroup of the image open normal subgroup is the subgroup image.
@isnad1 id=eq.2h4v.s7.7c50b4fcfe39 from=translated src=- shape=a728e3be vocab=0b284539
-/
@[simp, norm_cast]
theorem toSubgroup_map {H : Type v} [Group H] [TopologicalSpace H]
    (f : G →ₜ* H) (hfopen : IsOpenMap f) (hfsurj : Function.Surjective f)
    (U : OpenNormalSubgroup G) :
    ((map f hfopen hfsurj U : OpenNormalSubgroup H) : Subgroup H) =
      (U : Subgroup G).map f.toMonoidHom :=
  rfl

/-- A multiplicative homeomorphism identifies a quotient with the quotient by the image of an
open normal subgroup.  This is the source-producing transport used to prove that the canonical
pro-`C` object property is invariant under isomorphism.-/
noncomputable def quotientMapContinuousMulEquiv
    {H : Type u} [Group H] [TopologicalSpace H]
    (e : G ≃ₜ* H) (U : OpenNormalSubgroup G) :
    G ⧸ (U : Subgroup G) ≃*
      H ⧸ ((map (ContinuousMonoidHom.toContinuousMonoidHom e)
        (Homeomorph.isOpenMap e.toHomeomorph) e.surjective U : OpenNormalSubgroup H) :
          Subgroup H) := by
  let V : OpenNormalSubgroup H :=
    map (ContinuousMonoidHom.toContinuousMonoidHom e)
      (Homeomorph.isOpenMap e.toHomeomorph) e.surjective U
  have hforward :
      (U : Subgroup G) ≤ (V : Subgroup H).comap e.toMulEquiv.toMonoidHom := by
    intro x hx
    change e x ∈ (U : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom
    exact ⟨x, hx, rfl⟩
  have hbackward :
      (V : Subgroup H) ≤ (U : Subgroup G).comap e.symm.toMulEquiv.toMonoidHom := by
    intro y hy
    change e.symm y ∈ (U : Subgroup G)
    change y ∈ (U : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom at hy
    rcases hy with ⟨x, hx, hxy⟩
    have : e.symm y = x := by
      apply e.injective
      simpa using hxy.symm
    rw [this]
    exact hx
  let forward : G ⧸ (U : Subgroup G) →* H ⧸ (V : Subgroup H) :=
    QuotientGroup.map (U : Subgroup G) (V : Subgroup H)
      e.toMulEquiv.toMonoidHom hforward
  let backward : H ⧸ (V : Subgroup H) →* G ⧸ (U : Subgroup G) :=
    QuotientGroup.map (V : Subgroup H) (U : Subgroup G)
      e.symm.toMulEquiv.toMonoidHom hbackward
  refine
    { toFun := forward
      invFun := backward
      left_inv := ?_
      right_inv := ?_
      map_mul' := forward.map_mul }
  · intro x
    refine QuotientGroup.induction_on x ?_
    intro g
    change QuotientGroup.mk' (U : Subgroup G) (e.symm (e g)) =
      QuotientGroup.mk' (U : Subgroup G) g
    rw [e.symm_apply_apply]
  · intro y
    refine QuotientGroup.induction_on y ?_
    intro h
    change QuotientGroup.mk' (V : Subgroup H) (e (e.symm h)) =
      QuotientGroup.mk' (V : Subgroup H) h
    rw [e.apply_symm_apply]

/-- The canonical quotient projection attached to an open normal subgroup.-/
def quotientProj (U : OpenNormalSubgroup G) : G →ₜ* G ⧸ (U : Subgroup G) where
  toMonoidHom := QuotientGroup.mk' (U : Subgroup G)
  continuous_toFun := continuous_quotient_mk'

/-- Quotients by open normal subgroups of compact groups are finite.
@isnad1 id=finite.0h2v.s5.ff477403ab08 from=translated src=- shape=20d9ac1c vocab=647ec5a7
-/
instance quotientFinite [ContinuousMul G] [CompactSpace G] (U : OpenNormalSubgroup G) :
    Finite (G ⧸ (U : Subgroup G)) :=
  openNormalSubgroup_finiteQuotient (G := G) U

/-- Quotients by open normal subgroups carry the discrete topology.
@isnad1 id=discrete.0h2v.s5.d962c9774521 from=translated src=- shape=315ad9ee vocab=b78d3933
-/
instance quotientDiscrete [ContinuousMul G] (U : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ (U : Subgroup G)) :=
  QuotientGroup.discreteTopology (openNormalSubgroup_isOpen (G := G) U)

/-- The induced pro-\(C\) map agrees with the corresponding finite-quotient construction.
@isnad1 id=eq.0h2v.s7.b6f8cac78216 from=translated src=- shape=1a79315c vocab=a2e598ed
-/
theorem quotientProj_toMonoidHom (U : OpenNormalSubgroup G) :
    (quotientProj U).toMonoidHom = QuotientGroup.mk' (U : Subgroup G) :=
  rfl

/-- The quotient projection sends an element to its quotient class.
@isnad1 id=eq.0h3v.s8.ba91b22107e0 from=translated src=- shape=76c0382b vocab=155011f1
-/
@[simp]
theorem quotientProj_apply (U : OpenNormalSubgroup G) (x : G) :
    quotientProj U x = QuotientGroup.mk' (U : Subgroup G) x :=
  rfl

/-- The quotient projection by an open normal subgroup is surjective.
@isnad1 id=surjecti.0h2v.s7.8b4fd0c3c8fd from=translated src=- shape=f76472f9 vocab=1767a367
-/
@[simp]
theorem quotientProj_surjective (U : OpenNormalSubgroup G) :
    Function.Surjective (quotientProj U) :=
  QuotientGroup.mk'_surjective (U : Subgroup G)

/-- The quotient projection maps an element to \(1\) exactly on the subgroup.
@isnad1 id=iff.0h3v.s8.10a4745fcb05 from=translated src=- shape=700b8f87 vocab=530c6a0b
-/
@[simp]
theorem quotientProj_eq_one_iff {U : OpenNormalSubgroup G} {x : G} :
    quotientProj U x = 1 ↔ x ∈ (U : Subgroup G) := by
  change (QuotientGroup.mk' (U : Subgroup G) x) = 1 ↔ x ∈ (U : Subgroup G)
  exact QuotientGroup.eq_one_iff (N := (U : Subgroup G)) x

/--
Equality under a quotient projection is membership of the quotient difference in the subgroup.
@isnad1 id=iff.0h4v.s8.1975020b8055 from=translated src=- shape=a492e89e vocab=51bb4a69
-/
theorem quotientProj_eq_quotientProj_iff {U : OpenNormalSubgroup G} {x y : G} :
    quotientProj U x = quotientProj U y ↔ x / y ∈ (U : Subgroup G) := by
  change QuotientGroup.mk' (U : Subgroup G) x = QuotientGroup.mk' (U : Subgroup G) y ↔
    x / y ∈ (U : Subgroup G)
  exact QuotientGroup.eq_iff_div_mem (N := (U : Subgroup G)) (x := x) (y := y)

/-- Kernel membership for the quotient projection is subgroup membership.
@isnad1 id=iff.0h3v.s6.bbfc29fb19ed from=translated src=- shape=33c6723f vocab=b2b3a66b
-/
@[simp]
theorem mem_ker_quotientProj [ContinuousMul G] {U : OpenNormalSubgroup G} {x : G} :
    x ∈ ker (quotientProj U) ↔ x ∈ (U : Subgroup G) := by
  exact quotientProj_eq_one_iff (U := U)

/-- The open normal kernel of the quotient projection is the original subgroup.
@isnad1 id=eq.0h2v.s6.d983c7e8fe95 from=translated src=- shape=ceb63846 vocab=a2da8e27
-/
@[simp]
theorem ker_quotientProj [ContinuousMul G] (U : OpenNormalSubgroup G) :
    ((ker (quotientProj U) : OpenNormalSubgroup G) : Subgroup G) = (U : Subgroup G) := by
  exact QuotientGroup.ker_mk' (U : Subgroup G)

/-- Kernels commute with composition of continuous homomorphisms into discrete groups.
@isnad1 id=eq.0h5v.s7.645aaf9d4bac from=translated src=- shape=9758fb0d vocab=b8ed2c64
-/
@[simp]
theorem ker_comp {H : Type v} [Group H] [TopologicalSpace H]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (g : H →ₜ* Q) (f : G →ₜ* H) :
    ker (g.comp f) =
      OpenNormalSubgroup.comap f.toMonoidHom f.continuous_toFun (ker g) := by
  ext x
  rfl

/-- The comap of a kernel is the kernel of the composite.
@isnad1 id=eq.0h5v.s7.ad6b40dfaa4d from=translated src=- shape=513845b0 vocab=b8ed2c64
-/
@[simp]
theorem comap_ker {H : Type v} [Group H] [TopologicalSpace H]
    {Q : Type*} [Group Q] [TopologicalSpace Q] [DiscreteTopology Q]
    (f : G →ₜ* H) (g : H →ₜ* Q) :
    OpenNormalSubgroup.comap f.toMonoidHom f.continuous_toFun (ker g) =
      ker (g.comp f) := by
  simp only [ContinuousMonoidHom.coe_toMonoidHom, ker_comp]

/-- Comapping an open normal subgroup is the kernel of the composite quotient projection.
@isnad1 id=eq.0h4v.s7.5c904e8d496b from=translated src=- shape=fd8fb8e3 vocab=d4a151b8
-/
@[simp]
theorem comap_quotientProj {H : Type v} [Group H] [TopologicalSpace H] [ContinuousMul H]
    (f : G →ₜ* H) (U : OpenNormalSubgroup H) :
    OpenNormalSubgroup.comap f.toMonoidHom f.continuous_toFun U =
      ker ((quotientProj U).comp f) := by
  ext x
  exact (quotientProj_eq_one_iff (U := U)).symm

/-- The natural transition map between quotients by open normal subgroups \(U\le V\).-/
def transition {U V : OpenNormalSubgroup G}
    (hUV : (U : Subgroup G) ≤ (V : Subgroup G)) :
    G ⧸ (U : Subgroup G) →ₜ* G ⧸ (V : Subgroup G) :=
  QuotientGroup.mapₜ (U : Subgroup G) (V : Subgroup G) (ContinuousMonoidHom.id G) (by
    intro x hx
    exact hUV hx)

/-- Transition maps send quotient classes to quotient classes.
@isnad1 id=eq.1h4v.s9.1615800000f3 from=translated src=- shape=d0b01c0d vocab=97e1a27e
-/
@[simp]
theorem transition_mk {U V : OpenNormalSubgroup G}
    (hUV : (U : Subgroup G) ≤ (V : Subgroup G)) (x : G) :
    transition hUV (QuotientGroup.mk' (U : Subgroup G) x) =
      QuotientGroup.mk' (V : Subgroup G) x := by
  rfl

/--
Composing a transition map with the smaller quotient projection gives the larger quotient
projection.
@isnad1 id=eq.1h3v.s8.18c19f0a2bd6 from=translated src=- shape=f6aaaf35 vocab=73bc93b4
-/
@[simp]
theorem transition_comp_quotientProj {U V : OpenNormalSubgroup G}
    (hUV : (U : Subgroup G) ≤ (V : Subgroup G)) :
    (transition hUV).comp (quotientProj U) = quotientProj V := by
  rfl

/-- Transition maps between quotients by nested open normal subgroups are surjective.
@isnad1 id=surjecti.1h3v.s8.bacb31f501a6 from=translated src=- shape=d74c91ba vocab=c9a9eeaf
-/
theorem transition_surjective {U V : OpenNormalSubgroup G}
    (hUV : (U : Subgroup G) ≤ (V : Subgroup G)) :
    Function.Surjective (transition hUV) := by
  intro y
  rcases QuotientGroup.mk'_surjective (V : Subgroup G) y with ⟨x, rfl⟩
  exact ⟨QuotientGroup.mk' (U : Subgroup G) x, rfl⟩

/-- The kernel of the transition map is the image of the larger subgroup in the smaller quotient.
@isnad1 id=eq.1h3v.s8.c03b6f77b19a from=translated src=- shape=9f41e860 vocab=0911a324
-/
@[simp]
theorem ker_transition {U V : OpenNormalSubgroup G}
    [ContinuousMul G]
    (hUV : (U : Subgroup G) ≤ (V : Subgroup G)) :
    ((ker (transition hUV) : OpenNormalSubgroup (G ⧸ (U : Subgroup G))) :
        Subgroup (G ⧸ (U : Subgroup G))) =
      (V : Subgroup G).map (QuotientGroup.mk' (U : Subgroup G)) := by
  change
    (QuotientGroup.map (N := (U : Subgroup G)) (M := (V : Subgroup G))
      (f := MonoidHom.id G) hUV).ker =
      (V : Subgroup G).map (QuotientGroup.mk' (U : Subgroup G))
  exact
    QuotientGroup.ker_map (N := (U : Subgroup G)) (M := (V : Subgroup G))
      (f := MonoidHom.id G) hUV

/--
The normal core of an open subgroup in a compact topological group is an open normal subgroup.-/
def normalCore [ContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    OpenNormalSubgroup G where
  toOpenSubgroup :=
    { toSubgroup := Subgroup.normalCore (U : Subgroup G)
      isOpen' := by
        have hclosed : IsClosed ((U : Subgroup G) : Set G) :=
          openSubgroup_isClosed (G := G) U
        let : (U : Subgroup G).FiniteIndex :=
          Subgroup.finiteIndex_of_finite_quotient (H := (U : Subgroup G))
        exact Subgroup.isOpen_of_isClosed_of_finiteIndex _
          ((U : Subgroup G).normalCore_isClosed hclosed) }
  isNormal' := by
    change (Subgroup.normalCore (U : Subgroup G)).Normal
    infer_instance

/-- The underlying subgroup of \(\mathrm{normalCore}\) is the algebraic normal core.
@isnad1 id=eq.0h2v.s5.34ad48d17698 from=translated src=- shape=2c3f1276 vocab=1aa60b42
-/
@[simp, norm_cast]
theorem toSubgroup_normalCore [ContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    ((normalCore U : OpenNormalSubgroup G) : Subgroup G) =
      Subgroup.normalCore (U : Subgroup G) :=
  rfl

/-- The normal core of an open subgroup is contained in that open subgroup.
@isnad1 id=le.0h2v.s6.4eeef90e34fa from=translated src=- shape=c360cbdb vocab=155f73e2
-/
theorem normalCore_le [ContinuousMul G] [CompactSpace G] (U : OpenSubgroup G) :
    (normalCore U : Subgroup G) ≤ (U : Subgroup G) :=
  Subgroup.normalCore_le (U : Subgroup G)

/-- The infimum of a finite family of open normal subgroups.-/
def finsetInf {ι : Type v} (s : Finset ι) (U : ι → OpenNormalSubgroup G) :
    OpenNormalSubgroup G :=
  s.fold (fun A B => A ⊓ B) ⊤ U

end OpenNormalSubgroup

end ProCGroups.ProC
