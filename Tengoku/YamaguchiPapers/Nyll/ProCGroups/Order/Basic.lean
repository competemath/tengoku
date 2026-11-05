/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ProCGroups.InverseSystems.FiniteStageFactorization
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.OpenNormalSubgroups.FilteredFamilies
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Profinite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The order structure on closed subgroups

This module equips closed subgroups with basic lattice operations, develops continuous images and
preimages, and relates order-theoretic constructions to finite quotients of profinite groups.
-/

open Set
open scoped Topology Pointwise BigOperators

namespace ProCGroups.Order

universe u v w

open ProCGroups.InverseSystems
open ProCGroups.ProC

namespace ClosedSubgroup

variable {G : Type u} [Group G] [TopologicalSpace G]
variable {K : Type v} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]

/-- Closed subgroups have a top element: the whole group.-/
instance instTopClosedSubgroup : Top (ClosedSubgroup G) :=
  ⟨{ toSubgroup := ⊤, isClosed' := isClosed_univ }⟩

/--
Closed subgroups have a bottom element: the trivial subgroup, closed in a \(T_1\) topological
group.-/
instance instBotClosedSubgroup [T1Space G] : Bot (ClosedSubgroup G) :=
  ⟨{ toSubgroup := ⊥
     isClosed' := by
       change IsClosed ({(1 : G)} : Set G)
       exact isClosed_singleton }⟩

/--
The image of a closed subgroup under a continuous homomorphism from a compact domain into a
Hausdorff codomain.-/
noncomputable def map [CompactSpace G] [T2Space K] (H : ClosedSubgroup G)
    (φ : G →* K) (hφ : Continuous φ) : ClosedSubgroup K where
  toSubgroup := (H : Subgroup G).map φ
  isClosed' := by
    let f : H → K := fun x => φ x
    have hcont : Continuous f := hφ.comp continuous_subtype_val
    have hcompact : IsCompact (Set.range f) := isCompact_range hcont
    have hEq : Set.range f = ((H : Subgroup G).map φ : Set K) := by
      ext y
      constructor
      · rintro ⟨x, rfl⟩
        exact (Subgroup.mem_map).2 ⟨x.1, x.2, rfl⟩
      · intro hy
        rcases (Subgroup.mem_map).1 hy with ⟨x, hx, rfl⟩
        exact ⟨⟨x, hx⟩, rfl⟩
    change IsClosed (((H : Subgroup G).map φ : Subgroup K) : Set K)
    rw [← hEq]
    exact hcompact.isClosed

omit [IsTopologicalGroup K] in
/-- The underlying subgroup of the image closed subgroup is the image of the underlying subgroup.-/
@[simp, norm_cast]
theorem toSubgroup_map [CompactSpace G] [T2Space K] (H : ClosedSubgroup G)
    (φ : G →* K) (hφ : Continuous φ) :
    ((map H φ hφ : ClosedSubgroup K) : Subgroup K) = (H : Subgroup G).map φ :=
  rfl

omit [IsTopologicalGroup K] in
/-- Membership in the image closed subgroup is membership in the subgroup map.-/
theorem mem_map [CompactSpace G] [T2Space K] {H : ClosedSubgroup G}
    {φ : G →* K} (hφ : Continuous φ) {y : K} :
    y ∈ map H φ hφ ↔ ∃ x ∈ (H : Subgroup G), φ x = y := by
  rfl

/-- Mapping a closed subgroup along the identity homomorphism gives the same closed subgroup.-/
@[simp]
theorem map_id [CompactSpace G] [T2Space G] (H : ClosedSubgroup G) :
    map H (MonoidHom.id G) continuous_id = H := by
  apply ClosedSubgroup.toSubgroup_injective
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hy
  · intro hx
    exact ⟨x, hx, rfl⟩

omit [IsTopologicalGroup K] in
/-- Images of closed subgroups compose under composition of continuous homomorphisms.-/
theorem map_comp
    {L : Type w} [Group L] [TopologicalSpace L]
    [CompactSpace G] [T2Space K] [CompactSpace K] [T2Space L]
    (H : ClosedSubgroup G) (φ : G →* K) (hφ : Continuous φ)
    (ψ : K →* L) (hψ : Continuous ψ) :
    map (map H φ hφ) ψ hψ = map H (ψ.comp φ) (hψ.comp hφ) := by
  apply ClosedSubgroup.toSubgroup_injective
  ext z
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases (Subgroup.mem_map).1 hy with ⟨x, hx, rfl⟩
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨φ x, (Subgroup.mem_map).2 ⟨x, hx, rfl⟩, rfl⟩

omit [IsTopologicalGroup K] in
/-- The image construction on closed subgroups is monotone.-/
theorem map_mono [CompactSpace G] [T2Space K] {H H' : ClosedSubgroup G}
    (hHH' : (H : Subgroup G) ≤ (H' : Subgroup G))
    (φ : G →* K) (hφ : Continuous φ) :
    ((map H φ hφ : ClosedSubgroup K) : Subgroup K) ≤
      ((map H' φ hφ : ClosedSubgroup K) : Subgroup K) :=
  Subgroup.map_mono hHH'

omit [IsTopologicalGroup K] in
/-- The image of the bottom closed subgroup is the bottom closed subgroup.-/
@[simp]
theorem map_bot [CompactSpace G] [T1Space G] [T2Space K]
    (φ : G →* K) (hφ : Continuous φ) :
    map (⊥ : ClosedSubgroup G) φ hφ = (⊥ : ClosedSubgroup K) := by
  apply ClosedSubgroup.toSubgroup_injective
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    change x ∈ (⊥ : Subgroup G) at hx
    change φ x ∈ (⊥ : Subgroup K)
    rw [Subgroup.mem_bot] at hx ⊢
    simp [hx]
  · intro hy
    change y ∈ (⊥ : Subgroup K) at hy
    refine ⟨1, by simp only [SetLike.mem_coe, one_mem], ?_⟩
    rw [Subgroup.mem_bot] at hy
    simp [hy]

omit [IsTopologicalGroup K] in
/-- The image of the top closed subgroup under a surjective homomorphism is top.-/
theorem map_eq_top_of_surjective [CompactSpace G] [T2Space K] (H : ClosedSubgroup G)
    (φ : G →* K) (hφ : Continuous φ)
    (hφH : ∀ y : K, ∃ x ∈ (H : Subgroup G), φ x = y) :
    map H φ hφ = (⊤ : ClosedSubgroup K) := by
  apply ClosedSubgroup.toSubgroup_injective
  ext y
  constructor
  · intro _
    trivial
  · intro _
    exact hφH y

omit [IsTopologicalGroup K] in
/-- Image containment for closed subgroups is equivalent to containment in the comap.-/
theorem map_le_iff_le_comap [CompactSpace G] [T2Space K]
    {H : ClosedSubgroup G} {L : ClosedSubgroup K}
    {φ : G →* K} (hφ : Continuous φ) :
    ((map H φ hφ : ClosedSubgroup K) : Subgroup K) ≤ (L : Subgroup K) ↔
      (H : Subgroup G) ≤ Subgroup.comap φ (L : Subgroup K) := by
  constructor
  · intro h x hx
    exact h ((Subgroup.mem_map).2 ⟨x, hx, rfl⟩)
  · intro h y hy
    rcases (Subgroup.mem_map).1 hy with ⟨x, hx, rfl⟩
    exact h hx

end ClosedSubgroup

/-- The surjectivity hypothesis for transition maps in a group-valued inverse system.-/
def IsSurjectiveInverseSystem {I : Type v} [Preorder I]
    (S : ProCGroups.InverseSystems.InverseSystem (I := I)) : Prop :=
  ∀ ⦃i j : I⦄ (hij : i ≤ j), Function.Surjective (S.map hij)

/-- The image of a closed subgroup under a projection from a group-valued inverse limit.-/
noncomputable def inverseLimitProjectionImage
    {I : Type v} [Preorder I]
    (S : ProCGroups.InverseSystems.InverseSystem (I := I))
    [∀ i, Group (S.X i)] [ProCGroups.InverseSystems.IsGroupSystem S]
    [∀ i, TopologicalSpace (S.X i)] [∀ i, T2Space (S.X i)]
    [CompactSpace S.inverseLimit]
    (H : ClosedSubgroup S.inverseLimit) (i : I) : ClosedSubgroup (S.X i) :=
  let πi : S.inverseLimit →* S.X i := {
    toFun := fun x => S.projection i x
    map_one' := rfl
    map_mul' := by
      intro x y
      rfl
  }
  have hπi : Continuous (fun x : S.inverseLimit => S.projection i x) := by
    exact (continuous_apply i).comp continuous_subtype_val
  ClosedSubgroup.map H πi hπi

section FiniteQuotientImages

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The image of a closed subgroup in an open-normal finite quotient.-/
noncomputable def quotientImage [CompactSpace G] (H : ClosedSubgroup G)
    (U : OpenNormalSubgroup G) : ClosedSubgroup (G ⧸ (U : Subgroup G)) :=
  ClosedSubgroup.map H (QuotientGroup.mk' (U : Subgroup G)) continuous_quotient_mk'

/-- The subgroup underlying a quotient image is the image of the closed subgroup in the quotient.-/
@[simp, norm_cast]
theorem toSubgroup_quotientImage [CompactSpace G] (H : ClosedSubgroup G)
    (U : OpenNormalSubgroup G) :
    ((quotientImage (G := G) H U : ClosedSubgroup (G ⧸ (U : Subgroup G))) :
      Subgroup (G ⧸ (U : Subgroup G))) =
        (H : Subgroup G).map (QuotientGroup.mk' (U : Subgroup G)) :=
  rfl

/-- Membership in a quotient image is membership in the image of the underlying closed subgroup.-/
@[simp]
theorem mem_quotientImage [CompactSpace G] {H : ClosedSubgroup G}
    {U : OpenNormalSubgroup G} {y : G ⧸ (U : Subgroup G)} :
    y ∈ quotientImage (G := G) H U ↔
      ∃ x ∈ (H : Subgroup G), QuotientGroup.mk' (U : Subgroup G) x = y := by
  rfl

/--
Membership in a closed subgroup of a profinite group can be checked after all open-normal finite
quotients.-/
theorem mem_closedSubgroup_iff_forall_quotientImage_mem
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {H : ClosedSubgroup G} {x : G} :
    x ∈ H ↔
      ∀ U : OpenNormalSubgroup G,
        OpenNormalSubgroup.quotientProj U x ∈
          (quotientImage (G := G) H U : Subgroup (G ⧸ (U : Subgroup G))) := by
  constructor
  · intro hx U
    exact (Subgroup.mem_map).2 ⟨x, hx, rfl⟩
  · intro hx
    have hxOpen :
        ∀ N : Subgroup G, IsOpen (N : Set G) ∧ (H : Subgroup G) ≤ N → x ∈ N := by
      intro N hN
      let V : OpenSubgroup G := ⟨N, hN.1⟩
      rcases exists_openNormalSubgroup_mul_subset_openSubgroup (G := G) H V hN.2 with
        ⟨U, hHU⟩
      have hxImg :
          QuotientGroup.mk' (U : Subgroup G) x ∈
            (quotientImage (G := G) H U : Subgroup (G ⧸ (U : Subgroup G))) := by
        have hxU := hx U
        change QuotientGroup.mk' (U : Subgroup G) x ∈
          (quotientImage (G := G) H U : Subgroup (G ⧸ (U : Subgroup G))) at hxU
        exact hxU
      have hxSup : x ∈ (H : Subgroup G) ⊔ (U : Subgroup G) := by
        have hEq :
            (H : Subgroup G) ⊔ (U : Subgroup G) =
              Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                ((quotientImage (G := G) H U :
                  ClosedSubgroup (G ⧸ (U : Subgroup G))) :
                    Subgroup (G ⧸ (U : Subgroup G))) := by
          calc
            (H : Subgroup G) ⊔ (U : Subgroup G) =
                (H : Subgroup G) ⊔ (QuotientGroup.mk' (U : Subgroup G)).ker := by
                  rw [QuotientGroup.ker_mk']
            _ = Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                  (((H : Subgroup G).map (QuotientGroup.mk' (U : Subgroup G))) :
                    Subgroup (G ⧸ (U : Subgroup G))) := by
                  rw [← Subgroup.comap_map_eq]
            _ = Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                  ((quotientImage (G := G) H U :
                    ClosedSubgroup (G ⧸ (U : Subgroup G))) :
                      Subgroup (G ⧸ (U : Subgroup G))) := by
                  rfl
        rw [hEq]
        exact hxImg
      rcases
          (Subgroup.mem_sup_of_normal_right (s := (H : Subgroup G)) (t := (U : Subgroup G))).1
            hxSup with
        ⟨h, hhH, u, huU, hhu⟩
      have hxV : x ∈ (V : Set G) := hHU ⟨h, hhH, u, huU, hhu⟩
      change x ∈ N at hxV
      exact hxV
    have hxInf :
        x ∈ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ (H : Subgroup G) ≤ N} := by
      simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
      intro N hN
      exact hxOpen N hN
    change x ∈ (H : Subgroup G)
    exact (closedSubgroup_eq_sInf_open (G := G) H).symm ▸ hxInf

/--
Inclusion of closed subgroups of a profinite group can be checked on all open-normal finite
quotients.-/
theorem closedSubgroup_le_iff_forall_quotientImages_le
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {H K : ClosedSubgroup G} :
    (H : Subgroup G) ≤ (K : Subgroup G) ↔
      ∀ U : OpenNormalSubgroup G,
        (quotientImage (G := G) H U : Subgroup (G ⧸ (U : Subgroup G))) ≤
          (quotientImage (G := G) K U : Subgroup (G ⧸ (U : Subgroup G))) := by
  constructor
  · intro hHK U y hy
    rcases (Subgroup.mem_map).1 hy with ⟨x, hx, rfl⟩
    exact (Subgroup.mem_map).2 ⟨x, hHK hx, rfl⟩
  · intro hHK x hx
    exact (mem_closedSubgroup_iff_forall_quotientImage_mem (G := G) (H := K)).2 (by
      intro U
      exact hHK U ((Subgroup.mem_map).2 ⟨x, hx, rfl⟩))

/-- Two closed subgroups are equal if their images agree in every finite quotient.-/
theorem closedSubgroup_eq_of_quotientImages_eq
    [CompactSpace G] [TotallyDisconnectedSpace G]
    {H K : ClosedSubgroup G}
    (hHK : ∀ U : OpenNormalSubgroup G,
      quotientImage (G := G) H U = quotientImage (G := G) K U) :
    H = K := by
  have hle :
      ∀ {A B : ClosedSubgroup G},
        (∀ U : OpenNormalSubgroup G,
          quotientImage (G := G) A U = quotientImage (G := G) B U) →
            (A : Subgroup G) ≤ B := by
    intro A B hAB x hxA
    have hxOpen :
        ∀ N : Subgroup G, IsOpen (N : Set G) ∧ (B : Subgroup G) ≤ N → x ∈ N := by
      intro N hN
      let V : OpenSubgroup G := ⟨N, hN.1⟩
      rcases exists_openNormalSubgroup_mul_subset_openSubgroup (G := G) B V hN.2 with
        ⟨U, hBU⟩
      have hxImgA :
          QuotientGroup.mk' (U : Subgroup G) x ∈ (quotientImage (G := G) A U : Subgroup _) := by
        exact (Subgroup.mem_map).2 ⟨x, hxA, rfl⟩
      have hxImgB :
          QuotientGroup.mk' (U : Subgroup G) x ∈ (quotientImage (G := G) B U : Subgroup _) := by
        rw [← hAB U]
        exact hxImgA
      have hxSup : x ∈ (B : Subgroup G) ⊔ (U : Subgroup G) := by
        have hEq :
            (B : Subgroup G) ⊔ (U : Subgroup G) =
              Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                ((quotientImage (G := G) B U :
                  ClosedSubgroup (G ⧸ (U : Subgroup G))) :
                    Subgroup (G ⧸ (U : Subgroup G))) := by
          calc
            (B : Subgroup G) ⊔ (U : Subgroup G) =
                (B : Subgroup G) ⊔ (QuotientGroup.mk' (U : Subgroup G)).ker := by
                  rw [QuotientGroup.ker_mk']
            _ = Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                  (((B : Subgroup G).map (QuotientGroup.mk' (U : Subgroup G))) :
                    Subgroup (G ⧸ (U : Subgroup G))) := by
                  rw [← Subgroup.comap_map_eq]
            _ = Subgroup.comap (QuotientGroup.mk' (U : Subgroup G))
                  ((quotientImage (G := G) B U :
                    ClosedSubgroup (G ⧸ (U : Subgroup G))) :
                      Subgroup (G ⧸ (U : Subgroup G))) := by
                  rfl
        rw [hEq]
        exact hxImgB
      rcases
          (Subgroup.mem_sup_of_normal_right (s := (B : Subgroup G)) (t := (U : Subgroup G))).1
            hxSup with
        ⟨b, hbB, u, huU, hbu⟩
      have hxV : x ∈ (V : Set G) := hBU ⟨b, hbB, u, huU, hbu⟩
      change x ∈ N at hxV
      exact hxV
    have hxB :
        x ∈ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ (B : Subgroup G) ≤ N} := by
      simp only [Subgroup.mem_sInf, Set.mem_ofPred_eq]
      intro N hN
      exact hxOpen N hN
    exact (closedSubgroup_eq_sInf_open (G := G) B).symm ▸ hxB
  exact le_antisymm (hle hHK) (hle (fun U => (hHK U).symm))

end FiniteQuotientImages

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section CompatibleClosedSubgroupFamilies

variable {I : Type v} [Preorder I]
variable (S : ProCGroups.InverseSystems.InverseSystem (I := I))
variable [∀ i, Group (S.X i)] [ProCGroups.InverseSystems.IsGroupSystem S]
variable [∀ i, IsTopologicalGroup (S.X i)]
variable [∀ i, CompactSpace (S.X i)] [∀ i, T2Space (S.X i)]

/-- The transition map of a group-valued inverse system, viewed as a homomorphism.-/
def inverseSystemStageHom {i j : I} (hij : i ≤ j) : S.X j →* S.X i where
  toFun := S.map hij
  map_one' := ProCGroups.InverseSystems.IsGroupSystem.map_one (S := S) hij
  map_mul' := ProCGroups.InverseSystems.IsGroupSystem.map_mul (S := S) hij

omit [∀ i, IsTopologicalGroup (S.X i)] [∀ i, CompactSpace (S.X i)]
  [∀ i, T2Space (S.X i)] in
/-- The stage homomorphism associated to a group-valued inverse system is continuous.-/
theorem inverseSystemStageHom_continuous {i j : I} (hij : i ≤ j) :
    Continuous (inverseSystemStageHom (S := S) hij) := by
  simpa [inverseSystemStageHom] using (S.continuous_map hij :
    Continuous (fun x : S.X j => S.map hij x))

/--
The inverse system obtained by restricting an ambient inverse system to a compatible family of
closed subgroups.-/
def compatibleClosedSubgroupSystem
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) :
    ProCGroups.InverseSystems.InverseSystem (I := I) where
  X := fun i => L i
  topologicalSpace := fun i => inferInstance
  map := fun {i j} hij x =>
    ⟨S.map hij x.1, by
      have hx :
          S.map hij x.1 ∈
            ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
                (inverseSystemStageHom_continuous (S := S) hij) :
                  ClosedSubgroup (S.X i)) : Subgroup (S.X i)) := by
        exact (Subgroup.mem_map).2 ⟨x.1, x.2, rfl⟩
      rw [hcompat hij] at hx
      exact hx⟩
  continuous_map := fun {i j} hij =>
    Continuous.subtype_mk
      ((inverseSystemStageHom_continuous (S := S) hij).comp continuous_subtype_val) (fun x => by
      have hx :
          S.map hij x.1 ∈
            ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
                (inverseSystemStageHom_continuous (S := S) hij) :
                  ClosedSubgroup (S.X i)) : Subgroup (S.X i)) := by
        exact (Subgroup.mem_map).2 ⟨x.1, x.2, rfl⟩
      rw [hcompat hij] at hx
      exact hx)
  map_id := fun i => by
    funext x
    apply Subtype.ext
    simp only [InverseSystem.map_id_apply, id_eq]
  map_comp := fun {i j k} hij hjk => by
    funext x
    apply Subtype.ext
    simp only [Function.comp_apply, InverseSystem.map_comp_apply]

/-- Each stage of a compatible closed-subgroup system is a group.-/
instance compatibleClosedSubgroupSystem_group
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i)))
    (i : I) :
    Group ((compatibleClosedSubgroupSystem (S := S) L hcompat).X i) := by
  dsimp [compatibleClosedSubgroupSystem]
  infer_instance

/-- A compatible closed-subgroup system is a group-valued inverse system.-/
instance compatibleClosedSubgroupSystem_isGroupSystem
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) :
    ProCGroups.InverseSystems.IsGroupSystem (compatibleClosedSubgroupSystem (S := S) L hcompat)
        where
  map_one := by
    intro i j hij
    apply Subtype.ext
    change S.map hij (1 : S.X j) = 1
    exact ProCGroups.InverseSystems.IsGroupSystem.map_one (S := S) hij
  map_mul := by
    intro i j hij x y
    apply Subtype.ext
    change S.map hij (x.1 * y.1) = S.map hij x.1 * S.map hij y.1
    exact ProCGroups.InverseSystems.IsGroupSystem.map_mul (S := S) hij x.1 y.1
  map_inv := by
    intro i j hij x
    apply Subtype.ext
    change S.map hij x.1⁻¹ = (S.map hij x.1)⁻¹
    exact ProCGroups.InverseSystems.IsGroupSystem.map_inv (S := S) hij x.1

/--
The canonical coordinatewise inclusion of a compatible subgroup system into the ambient system.-/
def compatibleClosedSubgroupInclusion
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) :
    (compatibleClosedSubgroupSystem (S := S) L hcompat).Morphism S where
  map := fun i => Subtype.val
  continuous_map := fun i => by
    dsimp [compatibleClosedSubgroupSystem]
    exact continuous_subtype_val
  comm := fun {i j} hij => by
    funext x
    rfl

/--
The induced homomorphism from the inverse limit of a compatible subgroup family into the ambient
inverse limit.-/
noncomputable def compatibleClosedSubgroupLimHom
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) :
    (compatibleClosedSubgroupSystem (S := S) L hcompat).inverseLimit →* S.inverseLimit where
  toFun :=
    (compatibleClosedSubgroupSystem (S := S) L hcompat).limMap
      (compatibleClosedSubgroupInclusion (S := S) L hcompat)
  map_one' := by
    apply S.ext
    intro i
    rfl
  map_mul' := by
    intro x y
    apply S.ext
    intro i
    rfl

/--
Closed subgroup of the ambient inverse limit obtained from a compatible family of closed
subgroups with surjective transition maps.-/
noncomputable def closedSubgroupFromCompatibleFamily
    (L : ∀ i, ClosedSubgroup (S.X i))
    (hcompat : ∀ {i j : I} (hij : i ≤ j),
      ((ClosedSubgroup.map (L j) (inverseSystemStageHom (S := S) hij)
          (inverseSystemStageHom_continuous (S := S) hij) :
          ClosedSubgroup (S.X i)) : Subgroup (S.X i)) =
        (L i : Subgroup (S.X i))) :
    ClosedSubgroup S.inverseLimit where
  toSubgroup := (compatibleClosedSubgroupLimHom (S := S) L hcompat).range
  isClosed' := by
    let T : InverseSystem (I := I) := compatibleClosedSubgroupSystem (S := S) L hcompat
    let : ∀ i, CompactSpace (T.X i) := fun i =>
      (inferInstance : CompactSpace (L i))
    let : ∀ i, T2Space (T.X i) := fun i =>
      (inferInstance : T2Space (L i))
    let φ : T.inverseLimit →* S.inverseLimit :=
      compatibleClosedSubgroupLimHom (S := S) L hcompat
    have hφcont :
        Continuous (φ : T.inverseLimit → S.inverseLimit) := by
      change Continuous (T.limMap (compatibleClosedSubgroupInclusion (S := S) L hcompat))
      exact T.continuous_limMap (compatibleClosedSubgroupInclusion (S := S) L hcompat)
    change IsClosed (Set.range (φ : T.inverseLimit → S.inverseLimit))
    exact (isCompact_range hφcont).isClosed

end CompatibleClosedSubgroupFamilies

end ProCGroups.Order
