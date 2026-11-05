/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ProCGroups.FiniteGroups.AllFinite
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.InverseSystems.Basic
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.OpenNormalSubgroups.Basic
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Open-normal quotient bases in a finite-group class

`HasOpenNormalBasisInClass C G` says exactly that the identity neighborhoods of `G` have a basis
of open normal subgroups whose quotients lie in `C`. It does not assert compactness, Hausdorffness,
total disconnectedness, or even the topological-group laws.

For an ambient `ProfiniteGrp`, this is precisely the additional property used to define the bundled
category `ProCGrp C`.

The module also packages the class-indexed open normal subgroups, their quotient projections and
transition maps, and the separation consequences of a Hausdorff open-normal basis.
-/

namespace ProCGroups.ProC

universe u v

section

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- The identity-neighborhood basis property for open normal subgroups with quotient in \(C\).

This predicate deliberately carries no profiniteness assumptions. A bundled pro-\(C\) object is an
ambient `ProfiniteGrp` satisfying this additional property, as expressed by `ProCGrp C`.-/
def HasOpenNormalBasisInClass (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] : Prop :=
  ∀ W : Set G, IsOpen W → (1 : G) ∈ W →
    ∃ U : OpenNormalSubgroup G,
      ((U : Subgroup G) : Set G) ⊆ W ∧ C (G ⧸ (U : Subgroup G))

/-- Universe-independent open-normal basis membership. Quotients are tested up to multiplicative
equivalence with a finite group represented in the carrier universe of `C`.-/
def HasOpenNormalBasisInClassAcrossUniverses (C : FiniteGroupClass.{u})
    (G : Type v) [Group G] [TopologicalSpace G] : Prop :=
  ∀ W : Set G, IsOpen W → (1 : G) ∈ W →
    ∃ U : OpenNormalSubgroup G,
      ((U : Subgroup G) : Set G) ⊆ W ∧ C.MemAcrossUniverses (G ⧸ (U : Subgroup G))

/-- In the native universe of `C`, the universe-independent and original basis predicates agree.
@isnad1 id=iff.0h2v.s4.03d3e16a5b58 from=translated src=- shape=58eded28 vocab=67172429
-/
theorem hasOpenNormalBasisInClassAcrossUniverses_iff
    {C : FiniteGroupClass.{u}} {G : Type u} [Group G] [TopologicalSpace G] :
    HasOpenNormalBasisInClassAcrossUniverses C G ↔ HasOpenNormalBasisInClass C G := by
  constructor
  · intro h W hW h1W
    rcases h W hW h1W with ⟨U, hUW, hCU⟩
    exact ⟨U, hUW, (C.memAcrossUniverses_iff).1 hCU⟩
  · intro h W hW h1W
    rcases h W hW h1W with ⟨U, hUW, hCU⟩
    exact ⟨U, hUW, (C.memAcrossUniverses_iff).2 hCU⟩

namespace HasOpenNormalBasisInClass

/--
The existence of an open-normal basis in a class is monotone under enlarging the finite-group
class.
@isnad1 id=hasopenn.1h4v.s5.8a66edded341 from=translated src=- shape=de9fa3a7 vocab=1de54fc2
-/
theorem mono {C D : FiniteGroupClass.{u}} {G : Type u} [Group G] [TopologicalSpace G]
    (hbasis : HasOpenNormalBasisInClass C G)
    (hmono : ∀ {Q : Type u} [Group Q], C Q → D Q) :
    HasOpenNormalBasisInClass D G := by
  intro W hW h1W
  rcases hbasis W hW h1W with ⟨U, hUW, hCU⟩
  exact ⟨U, hUW, hmono hCU⟩

end HasOpenNormalBasisInClass

/--
Open normal subgroups whose quotient lies in the chosen class \(C\). This packages the specified
family as an actual type so later inverse-limit and basis constructions can quantify over it
directly.-/
abbrev OpenNormalSubgroupInClass (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] :=
  {U : OpenNormalSubgroup G // C (G ⧸ (U : Subgroup G))}

namespace OpenNormalSubgroupInClass

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G]

/--
Repackage an open normal subgroup together with a certificate that its quotient lies in \(C\).-/
def ofOpenNormal (U : OpenNormalSubgroup G) (hU : C (G ⧸ (U : Subgroup G))) :
    OpenNormalSubgroupInClass C G :=
  ⟨U, hU⟩

/-- The quotient attached to a normal subgroup in the finite-quotient index family lies in \(C\).
@isnad1 id=pred.0h3v.s7.f28aa3b16a39 from=translated src=- shape=13d7ba81 vocab=5934f70b
-/
theorem quotient_mem (U : OpenNormalSubgroupInClass C G) :
    C (G ⧸ (U.1 : Subgroup G)) :=
  U.2

/-- Move an open-normal-in-class subgroup along an inclusion of finite-group classes.-/
def of_mono {D : FiniteGroupClass.{u}}
    (hmono : ∀ {Q : Type u} [Group Q], C Q → D Q)
    (U : OpenNormalSubgroupInClass C G) :
    OpenNormalSubgroupInClass D G :=
  ⟨U.1, hmono U.2⟩

/-- The top subgroup belongs to any finite-group class containing trivial quotients.-/
def top [FiniteGroupClass.ContainsTrivialQuotients C] :
    OpenNormalSubgroupInClass C G :=
  ⟨⊤, by
    have hsub : Subsingleton (G ⧸ (⊤ : Subgroup G)) := by
      constructor
      intro x y
      rcases QuotientGroup.mk'_surjective (⊤ : Subgroup G) x with ⟨a, rfl⟩
      rcases QuotientGroup.mk'_surjective (⊤ : Subgroup G) y with ⟨b, rfl⟩
      exact QuotientGroup.eq.2 (by simp only [Subgroup.mem_top])
    exact FiniteGroupClass.ContainsTrivialQuotients.of_subsingleton hsub⟩

/-- There is an open-normal-in-class subgroup whenever the class contains trivial quotients.
@isnad1 id=nonempty.0h2v.s4.0a17adbf46a6 from=translated src=- shape=7231addf vocab=f7f738ec
-/
theorem nonempty_of_containsTrivialQuotients [FiniteGroupClass.ContainsTrivialQuotients C] :
    Nonempty (OpenNormalSubgroupInClass C G) :=
  ⟨top (C := C) (G := G)⟩

/-- Every open normal quotient of a compact group lies in the all-finite class.-/
def of_allFinite [ContinuousMul G] [CompactSpace G] (U : OpenNormalSubgroup G) :
    OpenNormalSubgroupInClass FiniteGroupClass.allFinite G :=
  ⟨U, openNormalSubgroup_finiteQuotient (G := G) U⟩

/--
Pull back an open-normal-in-class subgroup along a continuous homomorphism, when the class is
hereditary.-/
noncomputable def comap {H : Type u} [Group H] [TopologicalSpace H]
    (hHer : FiniteGroupClass.Hereditary C) (f : G →ₜ* H)
    (U : OpenNormalSubgroupInClass C H) : OpenNormalSubgroupInClass C G :=
  let N : OpenNormalSubgroup G :=
    OpenNormalSubgroup.comap f.toMonoidHom f.continuous_toFun U.1
  ⟨N, by
    let qmap : G ⧸ (N : Subgroup G) →* H ⧸ (U.1 : Subgroup H) :=
      QuotientGroup.map (N := (N : Subgroup G)) (M := (U.1 : Subgroup H))
        f.toMonoidHom (by
          intro x hx
          exact hx)
    have hqmap_inj : Function.Injective qmap := by
      rw [← MonoidHom.ker_eq_bot_iff qmap]
      ext z
      constructor
      · intro hz
        rcases QuotientGroup.mk'_surjective (N : Subgroup G) z with ⟨x, rfl⟩
        have hxU : f x ∈ (U.1 : Subgroup H) := by
          apply (QuotientGroup.eq_one_iff (N := (U.1 : Subgroup H)) (f x)).1
          simpa [qmap, MonoidHom.mem_ker] using hz
        exact (QuotientGroup.eq_one_iff (N := (N : Subgroup G)) x).2 hxU
      · intro hz
        subst z
        simp only [one_mem]
    exact hHer.of_injective U.2 qmap hqmap_inj⟩

/--
An open surjective continuous homomorphism sends an open-normal-in-class subgroup to an open
normal subgroup when target quotient membership is supplied explicitly. This is the lightweight
bridge; stronger automatic versions can be derived from class closure hypotheses as needed.-/
def mapOpenNormal {H : Type u} [Group H] [TopologicalSpace H]
    (f : G →ₜ* H) (hfopen : IsOpenMap f) (hfsurj : Function.Surjective f)
    (U : OpenNormalSubgroupInClass C G)
    (hC : C (H ⧸ ((OpenNormalSubgroup.map f hfopen hfsurj U.1 : OpenNormalSubgroup H) :
      Subgroup H))) :
    OpenNormalSubgroupInClass C H :=
  ⟨OpenNormalSubgroup.map f hfopen hfsurj U.1, hC⟩

/--
An open surjective continuous homomorphism sends an in-class open normal subgroup to an in-class
open normal subgroup. Formation closure supplies the target quotient membership.-/
def mapOpenNormal_of_formation {H : Type u} [Group H] [TopologicalSpace H]
    (hForm : FiniteGroupClass.Formation C)
    (f : G →ₜ* H) (hfopen : IsOpenMap f) (hfsurj : Function.Surjective f)
    (U : OpenNormalSubgroupInClass C G) :
    OpenNormalSubgroupInClass C H :=
  mapOpenNormal (C := C) (G := G) f hfopen hfsurj U (by
    let M : OpenNormalSubgroup H := OpenNormalSubgroup.map f hfopen hfsurj U.1
    let qmap : G ⧸ (U.1 : Subgroup G) →* H ⧸ (M : Subgroup H) :=
      QuotientGroup.map (N := (U.1 : Subgroup G)) (M := (M : Subgroup H))
        f.toMonoidHom (by
          intro x hx
          exact ⟨x, hx, rfl⟩)
    have hqmap_surj : Function.Surjective qmap :=
      QuotientGroup.map_surjective_of_surjective
        (N := (U.1 : Subgroup G)) (M : Subgroup H) f.toMonoidHom (by
          intro y
          rcases QuotientGroup.mk'_surjective (M : Subgroup H) y with ⟨h, rfl⟩
          rcases hfsurj h with ⟨g, rfl⟩
          exact ⟨g, rfl⟩) (by
          intro x hx
          exact ⟨x, hx, rfl⟩)
    have hquot :
        C ((G ⧸ (U.1 : Subgroup G)) ⧸ qmap.ker) :=
      hForm.quotientClosed qmap.ker U.2
    let e :
        (G ⧸ (U.1 : Subgroup G)) ⧸ qmap.ker ≃*
          H ⧸ (M : Subgroup H) :=
      QuotientGroup.quotientKerEquivOfSurjective qmap hqmap_surj
    exact hForm.isomClosed ⟨e⟩ hquot)

/-- Finite intersections stay in class for a formation.-/
def inf (hForm : FiniteGroupClass.Formation C)
    (U V : OpenNormalSubgroupInClass C G) : OpenNormalSubgroupInClass C G :=
  ⟨U.1 ⊓ V.1,
    FiniteGroupClass.Formation.quotient_inf_mem
      (C := C) (G := G) hForm U.1 V.1 U.2 V.2⟩

/-- The quotient projection attached to an open-normal-in-class subgroup.-/
def quotientProj (U : OpenNormalSubgroupInClass C G) :
    G →ₜ* G ⧸ (U.1 : Subgroup G) :=
  OpenNormalSubgroup.quotientProj U.1

/-- The quotient projection evaluates to the quotient class of the element.
@isnad1 id=eq.0h4v.s10.e743f0bb8b62 from=translated src=- shape=c15fc62d vocab=c46c67e9
-/
@[simp]
theorem quotientProj_apply (U : OpenNormalSubgroupInClass C G) (x : G) :
    quotientProj (C := C) U x = QuotientGroup.mk' (U.1 : Subgroup G) x :=
  rfl

/-- The quotient projection attached to an open-normal-in-class subgroup is surjective.
@isnad1 id=surjecti.0h3v.s9.197d0b9c1cdc from=translated src=- shape=c00c40cd vocab=1dc480fc
-/
@[simp]
theorem quotientProj_surjective (U : OpenNormalSubgroupInClass C G) :
    Function.Surjective (quotientProj (C := C) U) :=
  OpenNormalSubgroup.quotientProj_surjective U.1

/-- The kernel predicate of the quotient projection is membership in the subgroup.
@isnad1 id=iff.0h4v.s10.1c42fcae69f7 from=translated src=- shape=fecb7b57 vocab=f47eaa6b
-/
@[simp]
theorem quotientProj_eq_one_iff {U : OpenNormalSubgroupInClass C G} {x : G} :
    quotientProj (C := C) U x = 1 ↔ x ∈ (U.1 : Subgroup G) :=
  OpenNormalSubgroup.quotientProj_eq_one_iff (U := U.1)

/-- Equality in the quotient attached to an open-normal-in-class subgroup.
@isnad1 id=iff.0h5v.s10.b1e94cf52fdc from=translated src=- shape=d718e309 vocab=1a9a8b7a
-/
theorem quotientProj_eq_quotientProj_iff {U : OpenNormalSubgroupInClass C G} {x y : G} :
    quotientProj (C := C) U x = quotientProj (C := C) U y ↔
      x / y ∈ (U.1 : Subgroup G) :=
  OpenNormalSubgroup.quotientProj_eq_quotientProj_iff (U := U.1)

/-- Kernel membership for the quotient projection attached to an open-normal-in-class subgroup.
@isnad1 id=iff.0h4v.s8.0ca8806f0989 from=translated src=- shape=5ad2988f vocab=9101b669
-/
@[simp]
theorem mem_ker_quotientProj [ContinuousMul G] {U : OpenNormalSubgroupInClass C G} {x : G} :
    x ∈ OpenNormalSubgroup.ker (quotientProj (C := C) U) ↔
      x ∈ (U.1 : Subgroup G) :=
  OpenNormalSubgroup.mem_ker_quotientProj (U := U.1)

/-- The open-normal kernel of the quotient projection is the original subgroup.
@isnad1 id=eq.0h3v.s8.627c2f90448c from=translated src=- shape=b0fa01fa vocab=9c2d7f18
-/
@[simp]
theorem ker_quotientProj [ContinuousMul G] (U : OpenNormalSubgroupInClass C G) :
    ((OpenNormalSubgroup.ker (quotientProj (C := C) U) : OpenNormalSubgroup G) :
      Subgroup G) = (U.1 : Subgroup G) :=
  OpenNormalSubgroup.ker_quotientProj U.1

/--
The canonical transition map between quotients attached to nested open normal subgroups in the
class-indexing family.-/
def map {U V : OpenNormalSubgroupInClass C G}
    (hUV : (V.1 : Subgroup G) ≤ (U.1 : Subgroup G)) :
    G ⧸ (V.1 : Subgroup G) →* G ⧸ (U.1 : Subgroup G) :=
  QuotientGroup.map _ _ (MonoidHom.id G) hUV

/-- These transition maps are the natural quotient epimorphisms.
@isnad1 id=surjecti.1h4v.s10.38584b023709 from=translated src=- shape=1eb0ec43 vocab=ce871590
-/
theorem map_surjective {U V : OpenNormalSubgroupInClass C G}
    (hUV : (V.1 : Subgroup G) ≤ (U.1 : Subgroup G)) :
    Function.Surjective (map (C := C) (G := G) hUV) := by
  intro x
  rcases QuotientGroup.mk'_surjective (U.1 : Subgroup G) x with ⟨g, rfl⟩
  exact ⟨QuotientGroup.mk' (V.1 : Subgroup G) g, rfl⟩

/-- The identity transition map is the identity monoid homomorphism.
@isnad1 id=eq.0h3v.s10.62e34490b7fc from=translated src=- shape=4e60c3f0 vocab=994d6da3
-/
theorem map_id (U : OpenNormalSubgroupInClass C G) :
    map (C := C) (G := G) (le_rfl : (U.1 : Subgroup G) ≤ (U.1 : Subgroup G)) = MonoidHom.id _ := by
  exact QuotientGroup.map_id (N := (U.1 : Subgroup G)) (h := fun _ hx => hx)

/-- Maps induced on topological abelianizations compose as expected.
@isnad1 id=eq.2h5v.s11.f7abe0d04b5b from=translated src=- shape=03337c8f vocab=2f9ae388
-/
theorem map_comp {U V W : OpenNormalSubgroupInClass C G}
    (hUV : (V.1 : Subgroup G) ≤ (U.1 : Subgroup G))
    (hVW : (W.1 : Subgroup G) ≤ (V.1 : Subgroup G)) :
    (map (C := C) (G := G) hUV).comp (map (C := C) (G := G) hVW) =
      map (C := C) (G := G) (hVW.trans hUV) := by
  simpa [map] using QuotientGroup.map_comp_map
    (N := (W.1 : Subgroup G)) (M := (V.1 : Subgroup G)) (O := (U.1 : Subgroup G))
    (f := MonoidHom.id G) (g := MonoidHom.id G) hVW hUV

/--
The continuous transition map between quotients attached to nested open-normal-in-class
subgroups.-/
def transition {U V : OpenNormalSubgroupInClass C G}
    (hUV : (U.1 : Subgroup G) ≤ (V.1 : Subgroup G)) :
    G ⧸ (U.1 : Subgroup G) →ₜ* G ⧸ (V.1 : Subgroup G) :=
  OpenNormalSubgroup.transition (G := G) (U := U.1) (V := V.1) hUV

/-- Transition maps send quotient classes to the corresponding quotient classes.
@isnad1 id=eq.1h5v.s11.2a565ffcda86 from=translated src=- shape=0ad7bd1c vocab=c1391e78
-/
@[simp]
theorem transition_mk {U V : OpenNormalSubgroupInClass C G}
    (hUV : (U.1 : Subgroup G) ≤ (V.1 : Subgroup G)) (x : G) :
    transition (C := C) (G := G) hUV (QuotientGroup.mk' (U.1 : Subgroup G) x) =
      QuotientGroup.mk' (V.1 : Subgroup G) x :=
  OpenNormalSubgroup.transition_mk (G := G) (U := U.1) (V := V.1) hUV x

/--
Composing the transition map with the smaller quotient projection gives the larger quotient
projection.
@isnad1 id=eq.1h4v.s10.10581f0e9ec6 from=translated src=- shape=a95eecd8 vocab=2ba5f0c7
-/
@[simp]
theorem transition_comp_quotientProj {U V : OpenNormalSubgroupInClass C G}
    (hUV : (U.1 : Subgroup G) ≤ (V.1 : Subgroup G)) :
    (transition (C := C) (G := G) hUV).comp (quotientProj (C := C) U) =
      quotientProj (C := C) V :=
  OpenNormalSubgroup.transition_comp_quotientProj (G := G) (U := U.1) (V := V.1) hUV

/-- Transition maps between quotients by nested open-normal-in-class subgroups are surjective.
@isnad1 id=surjecti.1h4v.s10.f7015290809b from=translated src=- shape=63f21df2 vocab=4c851107
-/
theorem transition_surjective {U V : OpenNormalSubgroupInClass C G}
    (hUV : (U.1 : Subgroup G) ≤ (V.1 : Subgroup G)) :
    Function.Surjective (transition (C := C) (G := G) hUV) :=
  OpenNormalSubgroup.transition_surjective (G := G) (U := U.1) (V := V.1) hUV

end OpenNormalSubgroupInClass

section

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/--
The inverse system of quotient groups indexed by open normal subgroups whose quotients lie in
\(C\), ordered by reverse inclusion.-/
def openNormalSubgroupInClassSystem (C : FiniteGroupClass.{u})
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    InverseSystems.InverseSystem (I := OrderDual (OpenNormalSubgroupInClass C G)) where
  X := fun U => G ⧸ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G)
  topologicalSpace := fun _ => inferInstance
  map := fun {U V} hUV =>
    OpenNormalSubgroupInClass.map (C := C) (G := G)
      (U := OrderDual.ofDual U) (V := OrderDual.ofDual V) hUV
  continuous_map := by
    intro U V hUV
    exact continuous_of_discreteTopology
  map_id := by
    intro U
    funext x
    exact congrFun
      (congrArg DFunLike.coe
        (OpenNormalSubgroupInClass.map_id
          (C := C) (G := G) (U := OrderDual.ofDual U))) x
  map_comp := by
    intro U V W hUV hVW
    funext x
    rcases QuotientGroup.mk'_surjective
        ((((OrderDual.ofDual W).1 : OpenNormalSubgroup G) : Subgroup G)) x with ⟨g, rfl⟩
    rfl

/-- Every coordinate of the open-normal-in-class inverse system is a quotient group.-/
instance instGroupOpenNormalSubgroupInClassSystemX
    (U : OrderDual (OpenNormalSubgroupInClass C G)) :
    Group ((openNormalSubgroupInClassSystem C G).X U) :=
  QuotientGroup.Quotient.group
    (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G)

/--
The canonical quotient homomorphisms from \(G\) into the open-normal-subgroup inverse system
whose quotients lie in \(C\).-/
def openNormalSubgroupInClassProj
    (U : OrderDual (OpenNormalSubgroupInClass C G)) :
    G →* G ⧸ (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G) :=
  QuotientGroup.mk' (((OrderDual.ofDual U).1 : OpenNormalSubgroup G) : Subgroup G)

/-- The canonical quotient homomorphisms are compatible with the transition maps.
@isnad1 id=compatib.0h2v.s10.61a8f4c84ece from=translated src=- shape=d5e591ac vocab=2bf0a8a6
-/
theorem openNormalSubgroupInClassProj_compatible :
    (openNormalSubgroupInClassSystem C G).CompatibleMaps
      (fun U : OrderDual (OpenNormalSubgroupInClass C G) =>
        openNormalSubgroupInClassProj (C := C) (G := G) U) := by
  intro U V hUV
  funext g
  rfl

/-- The quotient system attached to open normal subgroups in \(C\) is group-valued.
@isnad1 id=isgroups.0h2v.s6.375baf7e331b from=translated src=- shape=48774b71 vocab=a29062cb
-/
instance instIsGroupSystemOpenNormalSubgroupInClassSystem :
    InverseSystems.IsGroupSystem (openNormalSubgroupInClassSystem C G) where
  map_one := by
    intro i j hij
    change
      OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij 1 = 1
    exact
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij).map_one
  map_mul := by
    intro i j hij x y
    change
      OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij (x * y) =
          OpenNormalSubgroupInClass.map
            (C := C) (G := G)
            (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij x *
          OpenNormalSubgroupInClass.map
            (C := C) (G := G)
            (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij y
    exact
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij).map_mul x y
  map_inv := by
    intro i j hij x
    change
      OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij x⁻¹ =
          (OpenNormalSubgroupInClass.map
            (C := C) (G := G)
            (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij x)⁻¹
    exact
      (OpenNormalSubgroupInClass.map
        (C := C) (G := G)
        (U := OrderDual.ofDual i) (V := OrderDual.ofDual j) hij).map_inv x

omit [IsTopologicalGroup G] in
/-- Each projection from \(G\) to an open-normal-in-class quotient is surjective.
@isnad1 id=surjecti.0h3v.s10.4a3a9df17da8 from=translated src=- shape=d513a32e vocab=d9835cf0
-/
theorem openNormalSubgroupInClassProj_surjective
    (U : OrderDual (OpenNormalSubgroupInClass C G)) :
    Function.Surjective (openNormalSubgroupInClassProj (C := C) (G := G) U) :=
  QuotientGroup.mk'_surjective _

omit [IsTopologicalGroup G] in
/-- The open-normal-in-class index family is directed under reverse inclusion.
@isnad1 id=directed.1h2v.s6.ef9b7cac367b from=translated src=- shape=891ec340 vocab=d19af439
-/
theorem directed_openNormalSubgroupInClass
    (hForm : FiniteGroupClass.Formation C) :
    Directed (α := OrderDual (OpenNormalSubgroupInClass C G)) (· ≤ ·) fun U => U := by
  intro U V
  let W : OpenNormalSubgroupInClass C G :=
    ⟨U.1 ⊓ V.1,
      FiniteGroupClass.Formation.quotient_inf_mem
        (C := C) (G := G) hForm U.1 V.1 U.2 V.2⟩
  refine ⟨OrderDual.toDual W, ?_, ?_⟩
  · change ((W.1 : Subgroup G) ≤ (U.1 : Subgroup G))
    exact inf_le_left
  · change ((W.1 : Subgroup G) ≤ (V.1 : Subgroup G))
    exact inf_le_right

end

variable {C : FiniteGroupClass.{u}}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

namespace HasOpenNormalBasisInClass

omit [IsTopologicalGroup G] in
/-- The open-normal quotient-basis property is preserved by continuous multiplicative
equivalences.
@isnad1 id=hasopenn.1h4v.s5.bb73e918119c from=translated src=- shape=e1a74667 vocab=4dca9229
-/
theorem ofContinuousMulEquiv
    {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    (hG : HasOpenNormalBasisInClass C G) (e : G ≃ₜ* H) :
    HasOpenNormalBasisInClass C H := by
  intro W hW h1W
  have hpreOpen : IsOpen (e ⁻¹' W) := hW.preimage e.continuous
  have hpreOne : (1 : G) ∈ e ⁻¹' W := by
    simpa using h1W
  rcases hG (e ⁻¹' W) hpreOpen hpreOne with ⟨U, hUW, hCU⟩
  let V : OpenNormalSubgroup H :=
    OpenNormalSubgroup.map (ContinuousMonoidHom.toContinuousMonoidHom e)
      (Homeomorph.isOpenMap e.toHomeomorph) e.surjective U
  refine ⟨V, ?_, ?_⟩
  · intro h hh
    change h ∈ (U : Subgroup G).map (ContinuousMonoidHom.toContinuousMonoidHom e).toMonoidHom at hh
    rcases hh with ⟨g, hg, rfl⟩
    exact hUW hg
  · simpa [V] using
      C.mem_of_mulEquiv
        (OpenNormalSubgroup.quotientMapContinuousMulEquiv e U) hCU

omit [IsTopologicalGroup G] in
/-- With isomorphism and quotient closure, the basis property implies that every open-normal
quotient lies in the class.
@isnad1 id=pred.3h3v.s5.db5fe2c49b0e from=translated src=- shape=a84d3b4f vocab=a3601687
-/
theorem hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
    (hIso : FiniteGroupClass.IsomClosed C)
    (hQuot : FiniteGroupClass.QuotientClosed C)
    (hG : HasOpenNormalBasisInClass C G) :
    ∀ U : OpenNormalSubgroup G, C (G ⧸ (U : Subgroup G)) := by
  intro U
  rcases hG (((U : Subgroup G) : Set G))
      (openNormalSubgroup_isOpen (G := G) U) U.one_mem' with
    ⟨V, hVU, hCV⟩
  let q : G ⧸ (V : Subgroup G) →ₜ* G ⧸ (U : Subgroup G) :=
    OpenNormalSubgroup.transition (G := G) hVU
  have hqsurj : Function.Surjective q := OpenNormalSubgroup.transition_surjective (G := G) hVU
  have hQuot :
      C ((G ⧸ (V : Subgroup G)) ⧸ q.toMonoidHom.ker) :=
    hQuot (N := q.toMonoidHom.ker) hCV
  exact hIso ⟨QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom hqsurj⟩ hQuot

omit [IsTopologicalGroup G] in
/-- For a group with an open-normal \(C\)-basis, every open-normal quotient lies in `C` when `C`
is a formation.
@isnad1 id=pred.2h3v.s5.6af9632a799b from=translated src=- shape=92a5c8d7 vocab=a2e8d517
-/
theorem quotient_mem (hForm : FiniteGroupClass.Formation C)
    (hG : HasOpenNormalBasisInClass C G) (U : OpenNormalSubgroup G) :
    C (G ⧸ (U : Subgroup G)) :=
  hasAllOpenNormalQuotientsInClass_of_basis_of_quotientClosed
    hForm.isomClosed hForm.quotientClosed hG U

omit [IsTopologicalGroup G] in
/-- Every open neighborhood of `1` contains an indexed open normal subgroup whose quotient lies
in `C`.
@isnad1 id=ex.3h3v.s6.f91452e85c08 from=translated src=- shape=fb5655a7 vocab=dd312e9d
-/
theorem exists_openNormalSubgroupInClass_sub_open_nhds_of_one (hG : HasOpenNormalBasisInClass C G)
    {W : Set G} (hW : IsOpen W) (h1W : (1 : G) ∈ W) :
    ∃ U : OpenNormalSubgroupInClass C G, (((U.1 : Subgroup G) : Set G)) ⊆ W := by
  rcases hG W hW h1W with ⟨U, hUW, hCU⟩
  exact ⟨⟨U, hCU⟩, hUW⟩

section DiscreteCoset

omit [IsTopologicalGroup G] in
/-- A continuous map to a discrete target is locally fixed on a sufficiently small right coset,
with the small subgroup chosen from the open normal subgroups whose quotients lie in `C`.
@isnad1 id=ex.2h5v.s7.f3a8a25bf079 from=translated src=- shape=5b3b94aa vocab=d2780f1e
-/
theorem exists_openNormalSubgroupInClass_eq_on_right_coset_of_continuous_discrete
    (hG : HasOpenNormalBasisInClass C G)
    [ContinuousMul G]
    {A : Type v} [TopologicalSpace A] [DiscreteTopology A]
    (f : G → A) (hf : Continuous f) (g₀ : G) :
    ∃ U : OpenNormalSubgroupInClass C G,
      ∀ g : G, g * g₀⁻¹ ∈ (U.1 : Subgroup G) → f g = f g₀ := by
  let W : Set G := {x | f (x * g₀) = f g₀}
  have hW : IsOpen W := by
    change IsOpen ((fun x : G => f (x * g₀)) ⁻¹' ({f g₀} : Set A))
    exact isOpen_discrete _ |>.preimage (hf.comp (continuous_id.mul continuous_const))
  have h1W : (1 : G) ∈ W := by
    simp only [Set.mem_ofPred_eq, one_mul, W]
  rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hW h1W with ⟨U, hUW⟩
  refine ⟨U, ?_⟩
  intro g hg
  have hmem : g * g₀⁻¹ ∈ W := hUW hg
  have hrewrite : (g * g₀⁻¹) * g₀ = g := by
    simp only [mul_assoc, inv_mul_cancel, mul_one]
  simpa [W, hrewrite] using hmem

end DiscreteCoset

section Hausdorff

variable [T2Space G]

omit [IsTopologicalGroup G] in
/-- In a Hausdorff group with an open-normal \(C\)-basis, the open normal subgroups whose quotients
lie in `C` have trivial total intersection.
@isnad1 id=eq.1h2v.s6.e4d53f2422d4 from=translated src=- shape=4c0d7060 vocab=ab515af3
-/
theorem iInf_openNormalSubgroupInClass_eq_bot (hG : HasOpenNormalBasisInClass C G) :
    iInf (fun U : OpenNormalSubgroupInClass C G => (U.1 : Subgroup G)) = (⊥ : Subgroup G) := by
  apply le_antisymm
  · intro x hx
    change x = 1
    by_contra hxne
    let W : Set G := ({x} : Set G)ᶜ
    have hW : IsOpen W := by
      simp only [isOpen_compl_iff, Set.finite_singleton, Set.Finite.isClosed, W]
    have h1W : (1 : G) ∈ W := by
      have hx1 : (1 : G) ≠ x := by
        intro h1x
        exact hxne h1x.symm
      simpa [W] using hx1
    rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hW h1W with ⟨U, hUW⟩
    have hxall : ∀ U : OpenNormalSubgroupInClass C G, x ∈ (U.1 : Subgroup G) := by
      simpa [Subgroup.mem_iInf] using hx
    have hxU : x ∈ (U.1 : Subgroup G) := hxall U
    have hxW : x ∈ W := hUW hxU
    exact hxW (by simp only [Set.mem_singleton_iff])
  · exact bot_le

omit [IsTopologicalGroup G] in
/-- Set-theoretic form of the trivial-intersection statement.
@isnad1 id=eq.1h2v.s6.660418b6243f from=translated src=- shape=6ae6cf25 vocab=97a26a04
-/
theorem iInter_openNormalSubgroupInClass_eq_singleton (hG : HasOpenNormalBasisInClass C G) :
    (⋂ U : OpenNormalSubgroupInClass C G, (((U.1 : Subgroup G) : Set G))) = ({1} : Set G) := by
  ext x
  constructor
  · intro hx
    have hx' : x ∈ iInf (fun U : OpenNormalSubgroupInClass C G => (U.1 : Subgroup G)) := by
      simpa [Subgroup.mem_iInf, Set.mem_iInter] using hx
    have hxbot : x ∈ (⊥ : Subgroup G) := by
      simpa [hG.iInf_openNormalSubgroupInClass_eq_bot] using hx'
    simpa using hxbot
  · rintro rfl
    simp only [OpenSubgroup.coe_toSubgroup, Set.mem_iInter, SetLike.mem_coe, one_mem, implies_true]

omit [IsTopologicalGroup G] in
/-- Explicit family form of the open-normal basis and trivial-intersection package.
@isnad1 id=ex.1h2v.s7.4c35f107aacd from=translated src=- shape=e9023d7a vocab=c9f3fbaf
-/
theorem exists_openNormalBasisInClassFamily (hG : HasOpenNormalBasisInClass C G) :
    ∃ ι : Type u, ∃ U : ι → OpenNormalSubgroup G,
      (∀ i, C (G ⧸ (U i : Subgroup G))) ∧
      (∀ W : Set G, IsOpen W → (1 : G) ∈ W →
        ∃ i, (((U i : Subgroup G) : Set G)) ⊆ W) ∧
      iInf (fun i => (U i : Subgroup G)) = (⊥ : Subgroup G) := by
  refine ⟨OpenNormalSubgroupInClass C G, fun i => i.1, ?_, ?_, ?_⟩
  · intro i
    exact i.2
  · intro W hW h1W
    rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one hW h1W with ⟨U, hUW⟩
    exact ⟨U, hUW⟩
  · simpa using hG.iInf_openNormalSubgroupInClass_eq_bot

omit [IsTopologicalGroup G] in
/-- Membership in every open-normal-in-class subgroup forces an element to be trivial.-/
theorem eq_one_of_mem_all_openNormalSubgroupInClass (hG : HasOpenNormalBasisInClass C G) {x : G}
    (hx : ∀ U : OpenNormalSubgroupInClass C G, x ∈ (U.1 : Subgroup G)) :
    x = 1 := by
  have hx' : x ∈ iInf (fun U : OpenNormalSubgroupInClass C G => (U.1 : Subgroup G)) := by
    simpa [Subgroup.mem_iInf] using hx
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [hG.iInf_openNormalSubgroupInClass_eq_bot] using hx'
  simpa using hxbot

omit [IsTopologicalGroup G] in
/-- If `x ≠ 1`, then some open normal subgroup in the class-family omits `x`.
@isnad1 id=ex.2h3v.s6.1e03f94f1caf from=translated src=- shape=d7351765 vocab=2f3c9680
-/
theorem exists_openNormalSubgroupInClass_not_mem (hG : HasOpenNormalBasisInClass C G) {x : G}
    (hx : x ≠ 1) :
    ∃ U : OpenNormalSubgroupInClass C G, x ∉ (U.1 : Subgroup G) := by
  by_contra h
  apply hx
  apply hG.eq_one_of_mem_all_openNormalSubgroupInClass
  intro U
  by_contra hxU
  exact h ⟨U, hxU⟩

omit [IsTopologicalGroup G] in
/-- In a Hausdorff group with an open-normal \(C\)-basis, two elements are equal once they agree in
every quotient by an open normal subgroup whose quotient lies in `C`.-/
theorem eq_of_forall_openNormalSubgroupInClass_quotient_eq (hG : HasOpenNormalBasisInClass C G)
    {x y : G}
    (hxy : ∀ U : OpenNormalSubgroupInClass C G,
      QuotientGroup.mk' (U.1 : Subgroup G) x = QuotientGroup.mk' (U.1 : Subgroup G) y) :
    x = y := by
  have hxy' : x⁻¹ * y = 1 := by
    apply hG.eq_one_of_mem_all_openNormalSubgroupInClass
    intro U
    exact QuotientGroup.eq.1 (hxy U)
  calc
    x = x * 1 := by simp only [mul_one]
    _ = x * (x⁻¹ * y) := by rw [hxy']
    _ = y := by simp only [mul_inv_cancel_left]

omit [IsTopologicalGroup G] in
/-- In a Hausdorff group with an open-normal \(C\)-basis, coordinatewise equality in the canonical
inverse-system projections forces equality in the ambient group.-/
theorem eq_of_forall_openNormalSubgroupInClassProj_eq (hG : HasOpenNormalBasisInClass C G) {x y : G}
    (hxy : ∀ U : OrderDual (OpenNormalSubgroupInClass C G),
      openNormalSubgroupInClassProj (C := C) (G := G) U x =
        openNormalSubgroupInClassProj (C := C) (G := G) U y) :
    x = y := by
  apply hG.eq_of_forall_openNormalSubgroupInClass_quotient_eq
  intro U
  have hU := hxy (OrderDual.toDual U)
  change
    QuotientGroup.mk' (U.1 : Subgroup G) x =
      QuotientGroup.mk' (U.1 : Subgroup G) y at hU
  exact hU

end Hausdorff

/-- For a profinite group, the stronger all-open-normal-quotient condition supplies an open-normal
\(C\)-basis.
@isnad1 id=hasopenn.0h3v.s6.435c4ee9af33 from=translated src=- shape=7f755287 vocab=99b9115d
-/
theorem of_allOpenNormalQuotients [CompactSpace G] [T2Space G]
    [TotallyDisconnectedSpace G]
    (hquot : ∀ U : OpenNormalSubgroup G, C (G ⧸ (U : Subgroup G))) :
    HasOpenNormalBasisInClass C G := by
  intro W hW h1W
  rcases exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hW h1W with ⟨U, hUW⟩
  exact ⟨U, hUW, hquot U⟩

omit [IsTopologicalGroup G] in
/-- An open-normal \(C\)-basis contains at least one subgroup.
@isnad1 id=nonempty.1h2v.s4.99c0304d67ec from=translated src=- shape=b3d84c03 vocab=4e83b33b
-/
theorem openNormalSubgroupInClass_nonempty (hG : HasOpenNormalBasisInClass C G) :
    Nonempty (OpenNormalSubgroupInClass C G) := by
  rcases hG.exists_openNormalSubgroupInClass_sub_open_nhds_of_one
      (W := Set.univ) isOpen_univ (by simp only [Set.mem_univ]) with ⟨U, _⟩
  exact ⟨U⟩

end HasOpenNormalBasisInClass

end

end ProCGroups.ProC
