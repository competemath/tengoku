/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.GroupTheory.SpecificGroups.Cyclic
import Tengoku.Seed.Topology.Algebra.Nonarchimedean.Basic
import Tengoku.Seed.Topology.Instances.ZMod
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Completion.UniversalProperty
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.FiniteGroups.StandardClasses
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.FiniteGeneration.CharacteristicChainsAndIndices
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.Category.Basic
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.OpenNormalSubgroups.LimitPresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Pro C Groups / Free pro-C / Basic

This module defines the free and pointed free pro-\(C\) universal properties,
their converging-set form, and the bundled canonical source data used by later
constructions.
-/

open Set
open scoped Topology

namespace ProCGroups.FreeProC

universe u v w

open ProCGroups
open ProCGroups.FiniteGeneration

section

variable {C : ProCGroups.FiniteGroupClass}

/--
Free pro-\(C\) groups via a strengthened universal property. The lifting property quantifies
over all continuous maps into pro-\(C\) groups, rather than only maps whose image generates the
target.-/
structure IsFreeProCGroup
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ι : X → F) : Prop where
  /--
  Open normal subgroups with quotients in `C` form a neighborhood basis at one in `F`.-/
  hasOpenNormalBasisInClass : ProCGroups.ProC.HasOpenNormalBasisInClass C F
  /-- The canonical map from the generating space into `F` is continuous.-/
  continuous_ι : Continuous ι
  /-- The image of the canonical map topologically generates `F`.-/
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  /--
  Every continuous map from `X` to a pro-`C` target extends to a unique continuous group
  homomorphism from `F`.-/
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G],
    ProCGroups.ProC.HasOpenNormalBasisInClass C (G) →
      ∀ (φ : X → G), Continuous φ →
        ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

namespace IsFreeProCGroup

variable {X : Type u} [TopologicalSpace X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable {ι : X → F}

/--
A map from the chosen generators into a pro-\(C\) target extends to the corresponding continuous
homomorphism from the free pro-\(C\) group.-/
noncomputable def lift (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ) : F →* G :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ))

/-- The universal-property lift has the prescribed values on the chosen generators.-/
theorem lift_spec (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ) :
    Continuous (hι.lift hG φ hφ) ∧ ∀ x, hι.lift hG φ hφ (ι x) = φ x :=
  Classical.choose_spec (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ))

/-- The universal-property lift is unique among continuous maps with the prescribed values.-/
theorem lift_unique (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ)
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.lift hG φ hφ := by
  exact (hι.existsUnique_lift hG φ hφ).unique ⟨hf, hfac⟩ (hι.lift_spec hG φ hφ)

/-- The universal-property lift bundled as a continuous monoid homomorphism.-/
noncomputable def liftHom (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ) : F →ₜ* G where
  toMonoidHom := hι.lift hG φ hφ
  continuous_toFun := (hι.lift_spec hG φ hφ).1

/-- Forgetting continuity from liftHom gives the underlying universal-property lift.-/
@[simp] theorem liftHom_toMonoidHom (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ) :
    (hι.liftHom hG φ hφ).toMonoidHom = hι.lift hG φ hφ :=
  rfl

/--
The lift homomorphism from a free pro-\(C\) group evaluates according to the chosen generator
map.-/
@[simp] theorem liftHom_apply (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ) (x : X) :
    hι.liftHom hG φ hφ (ι x) = φ x :=
  (hι.lift_spec hG φ hφ).2 x

/-- The lift homomorphism is uniquely determined by its values on the generators.-/
theorem liftHom_unique (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : Continuous φ)
    {f : F →ₜ* G} (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.liftHom hG φ hφ := by
  ext y
  exact congrArg (fun g : F →* G => g y)
    (hι.lift_unique hG φ hφ f.continuous_toFun hfac)

/--
Continuous homomorphisms out of a free pro-\(C\) group are determined by their values on the
chosen generators.-/
theorem hom_ext (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    {f g : F →* G} (hf : Continuous f) (hg : Continuous g)
    (hfg : ∀ x, f (ι x) = g (ι x)) :
    f = g := by
  let φ : X → G := fun x => f (ι x)
  have hφ : Continuous φ := hf.comp hι.continuous_ι
  exact
    (hι.existsUnique_lift hG φ hφ).unique
      ⟨hf, fun _ => rfl⟩ ⟨hg, fun x => (hfg x).symm⟩

/-- Two universal-property lifts are equal when they agree on all generators.-/
theorem lift_eq_of_forall (hι : IsFreeProCGroup (C := C) ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    {φ ψ : X → G} (hφ : Continuous φ) (hψ : Continuous ψ)
    (h : ∀ x, φ x = ψ x) :
    hι.lift hG φ hφ = hι.lift hG ψ hψ := by
  apply hι.hom_ext hG
    (hι.lift_spec hG φ hφ).1
    (hι.lift_spec hG ψ hψ).1
  intro x
  calc
    hι.lift hG φ hφ (ι x) = φ x := (hι.lift_spec hG φ hφ).2 x
    _ = ψ x := h x
    _ = hι.lift hG ψ hψ (ι x) := ((hι.lift_spec hG ψ hψ).2 x).symm

/-- The lift of the canonical generator map to the same free pro-\(C\) group is the identity.-/
@[simp] theorem lift_id (hι : IsFreeProCGroup (C := C) ι) :
    hι.lift hι.hasOpenNormalBasisInClass ι hι.continuous_ι = MonoidHom.id F := by
  symm
  exact hι.lift_unique hι.hasOpenNormalBasisInClass ι hι.continuous_ι continuous_id (by
    intro x
    rfl)

/-- An endomorphism of a free pro-\(C\) group fixing the generators is the identity.-/
theorem endomorphism_eq_id (hι : IsFreeProCGroup (C := C) ι)
    {f : F →* F} (hf : Continuous f) (hfac : ∀ x, f (ι x) = ι x) :
    f = MonoidHom.id F := by
  exact hι.hom_ext hι.hasOpenNormalBasisInClass hf continuous_id hfac

/-- Composition of free pro-\(C\) lifts is again the lift of the composed generator map.-/
theorem lift_comp (hι : IsFreeProCGroup (C := C) ι)
    {G H : Type u}
    [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [CompactSpace H] [T2Space H] [TotallyDisconnectedSpace H]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (hH : ProCGroups.ProC.HasOpenNormalBasisInClass C (H))
    (φ : X → G) (hφ : Continuous φ)
    (ψ : G →* H) (hψ : Continuous ψ) :
    ψ.comp (hι.lift hG φ hφ) =
      hι.lift hH (fun x => ψ (φ x)) (hψ.comp hφ) := by
  apply hι.lift_unique hH (fun x => ψ (φ x)) (hψ.comp hφ)
    (hψ.comp (hι.lift_spec hG φ hφ).1)
  intro x
  simp only [MonoidHom.coe_comp, Function.comp_apply, (hι.lift_spec hG φ hφ).2 x]

end IsFreeProCGroup

end

section

variable {C : ProCGroups.FiniteGroupClass}

/-- A family converges to `1` when it tends to `1` along the cofinite filter.-/
def FamilyConvergesToOne
    {X : Type v}
    {G : Type u} [Group G] [TopologicalSpace G]
    (μ : X → G) : Prop :=
  Filter.Tendsto μ Filter.cofinite (𝓝 1)

/-- The weaker condition obtained by testing family convergence only against open subgroups.-/
def FamilyConvergesToOneAlongOpenSubgroups
    {X : Type v}
    {G : Type u} [Group G] [TopologicalSpace G]
    (μ : X → G) : Prop :=
  ∀ U : OpenSubgroup G, {x : X | μ x ∉ (U : Set G)}.Finite

namespace FamilyConvergesToOne

variable {X : Type v}
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- Genuine family convergence implies convergence along open subgroups.-/
theorem to_alongOpenSubgroups {μ : X → G}
    (hμ : FamilyConvergesToOne (G := G) μ) :
    FamilyConvergesToOneAlongOpenSubgroups (G := G) μ := by
  intro U
  have hU : (U : Set G) ∈ 𝓝 (1 : G) :=
    U.isOpen.mem_nhds U.one_mem
  have heventually : ∀ᶠ x : X in Filter.cofinite, μ x ∈ U :=
    hμ.eventually hU
  change {x : X | μ x ∈ U} ∈ Filter.cofinite at heventually
  rw [Filter.mem_cofinite] at heventually
  simpa only [Set.compl_ofPred, SetLike.mem_coe] using heventually

/-- Convergence is preserved by a continuous homomorphism.-/
theorem comp
    {H : Type*} [TopologicalSpace H] [Group H]
    {μ : X → G}
    (hμ : FamilyConvergesToOne (G := G) μ) (f : G →ₜ* H) :
    FamilyConvergesToOne (G := H) (fun x => f (μ x)) := by
  change Filter.Tendsto (f.toContinuousMap ∘ μ) Filter.cofinite (𝓝 1)
  have hf1 : f.toContinuousMap (1 : G) = 1 := f.map_one
  simpa only [hf1] using (f.continuous.tendsto (1 : G)).comp hμ

/-- Families indexed by a finite type converge to `1`.-/
theorem of_finite_domain [Finite X] (μ : X → G) :
    FamilyConvergesToOne (G := G) μ := by
  rw [FamilyConvergesToOne, Filter.tendsto_def]
  intro W _
  rw [Filter.mem_cofinite]
  exact Set.toFinite _

/-- On an infinite index type in a `T₁` space, a constant family converges to `1` exactly when
its value is `1`. In particular, the old open-subgroup-only counterexample is rejected.-/
theorem const_iff [Infinite X] [T1Space G] (g : G) :
    FamilyConvergesToOne (G := G) (fun _ : X => g) ↔ g = 1 := by
  simp only [FamilyConvergesToOne, tendsto_const_nhds_iff]

end FamilyConvergesToOne

namespace FamilyConvergesToOneAlongOpenSubgroups

variable {X : Type v}
variable {G : Type u} [Group G] [TopologicalSpace G]

/-- A family converging to `1` has range converging to `1` as a set.-/
theorem range {μ : X → G} (hμ : FamilyConvergesToOneAlongOpenSubgroups (G := G) μ) :
    Generation.ConvergesToOneAlongOpenSubgroups (G := G) (Set.range μ) := by
  intro U
  have hsubset :
      Set.range μ \ (U : Set G) ⊆ μ '' {x : X | μ x ∉ (U : Set G)} := by
    rintro y ⟨⟨x, rfl⟩, hxU⟩
    exact ⟨x, hxU, rfl⟩
  exact (hμ U).image μ |>.subset hsubset

/-- Convergence to `1` is preserved by a continuous homomorphism.-/
theorem comp
    {H : Type*} [TopologicalSpace H] [Group H]
    {μ : X → G}
    (hμ : FamilyConvergesToOneAlongOpenSubgroups (G := G) μ) (f : G →ₜ* H) :
    FamilyConvergesToOneAlongOpenSubgroups (G := H) (fun x => f (μ x)) := by
  intro U
  have hfinite := hμ (U.comap f.toMonoidHom f.continuous)
  have hset :
      {x : X | μ x ∉ (U.comap f.toMonoidHom f.continuous : Set G)} =
        {x : X | f (μ x) ∉ (U : Set H)} := by
    ext x
    exact not_congr
      (OpenSubgroup.mem_comap (H := U) (f := f.toMonoidHom)
        (hf := f.continuous) (x := μ x))
  exact hset ▸ hfinite

/-- Range convergence implies family convergence for injectively indexed families.-/
theorem of_set_of_injective {μ : X → G}
    (hμ : Generation.ConvergesToOneAlongOpenSubgroups (G := G) (Set.range μ))
    (hinj : Function.Injective μ) :
    FamilyConvergesToOneAlongOpenSubgroups (G := G) μ := by
  intro U
  have himage :
      μ '' {x : X | μ x ∉ (U : Set G)} = Set.range μ \ (U : Set G) := by
    ext y
    constructor
    · rintro ⟨x, hxU, rfl⟩
      exact ⟨⟨x, rfl⟩, hxU⟩
    · rintro ⟨⟨x, rfl⟩, hxU⟩
      exact ⟨x, hxU, rfl⟩
  let : Finite (μ '' {x : X | μ x ∉ (U : Set G)}) := by
    rw [himage]
    exact (hμ U).to_subtype
  exact Finite.Set.finite_of_finite_image {x : X | μ x ∉ (U : Set G)} (by
    intro a _ b _ hab
    exact hinj hab)

/-- Families indexed by a finite type converge to `1`.-/
theorem of_finite_domain [Finite X] (μ : X → G) :
    FamilyConvergesToOneAlongOpenSubgroups (G := G) μ := by
  intro U
  exact Set.finite_univ.subset (by intro x _; trivial)

/-- In a nonarchimedean group, open subgroups detect genuine family convergence.-/
theorem to_familyConvergesToOne [NonarchimedeanGroup G] {μ : X → G}
    (hμ : FamilyConvergesToOneAlongOpenSubgroups (G := G) μ) :
    FamilyConvergesToOne (G := G) μ := by
  rw [FamilyConvergesToOne, Filter.tendsto_def]
  intro W hW
  obtain ⟨U, hUW⟩ := NonarchimedeanGroup.is_nonarchimedean W hW
  rw [Filter.mem_cofinite]
  change {x : X | μ x ∉ W}.Finite
  exact (hμ U).subset (by
    intro x hxW hxU
    exact hxW (hUW hxU))

end FamilyConvergesToOneAlongOpenSubgroups

/-- For nonarchimedean groups, genuine family convergence is equivalent to the
open-subgroup test.-/
theorem familyConvergesToOne_iff_alongOpenSubgroups
    {X : Type v} {G : Type u} [Group G] [TopologicalSpace G]
    [NonarchimedeanGroup G] {μ : X → G} :
    FamilyConvergesToOne (G := G) μ ↔
      FamilyConvergesToOneAlongOpenSubgroups (G := G) μ :=
  ⟨FamilyConvergesToOne.to_alongOpenSubgroups,
    FamilyConvergesToOneAlongOpenSubgroups.to_familyConvergesToOne⟩

/-- An open-subgroup-convergent family whose image topologically generates the target; here
convergence means finiteness outside every open subgroup.-/
structure ConvergingGeneratingMap
    (X : Type v)
    (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] where
  /-- The family of elements of `G`, indexed by `X`.-/
  toFun : X → G
  /--
  Outside every open subgroup of `G`, the family has only finitely many terms; thus it converges
  to one in the open-subgroup sense.-/
  convergesToOneAlongOpenSubgroups : FamilyConvergesToOneAlongOpenSubgroups (G := G) toFun
  /-- The range of the family topologically generates `G`.-/
  generates : Generation.TopologicallyGenerates (G := G) (Set.range toFun)

namespace ConvergingGeneratingMap

variable {X Y : Type v}
variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- A convergent generating map coerces to its underlying map into the group.-/
instance instCoeFunConvergingGeneratingMap :
    CoeFun (ConvergingGeneratingMap X G) (fun _ => X → G) where
  coe φ := φ.toFun

/-- The stored function of a convergent generating map agrees with its function coercion.-/
@[simp] theorem toFun_eq_coe (φ : ConvergingGeneratingMap X G) :
    φ.toFun = (φ : X → G) := rfl

/-- Reindexing along an equivalence preserves family convergence and generation.-/
def reindex (φ : ConvergingGeneratingMap X G) (e : Y ≃ X) :
    ConvergingGeneratingMap Y G where
  toFun := fun y => φ (e y)
  convergesToOneAlongOpenSubgroups := by
    intro U
    have hsubset :
        {y : Y | φ (e y) ∉ (U : Set G)} ⊆
          e.symm '' {x : X | φ x ∉ (U : Set G)} := by
      intro y hy
      exact ⟨e y, hy, by simp only [Equiv.symm_apply_apply]⟩
    exact (φ.convergesToOneAlongOpenSubgroups U).image e.symm |>.subset hsubset
  generates := by
    have hrange : Set.range (fun y : Y => φ (e y)) = Set.range (φ : X → G) := by
      ext z
      constructor
      · rintro ⟨y, rfl⟩
        exact ⟨e y, rfl⟩
      · rintro ⟨x, rfl⟩
        exact ⟨e.symm x, by simp only [Equiv.apply_symm_apply]⟩
    simpa [hrange] using φ.generates

/-- The range of a convergent generating map generates the group and converges to one along open
subgroups.-/
theorem generatesAndConvergesToOneAlongOpenSubgroups (φ : ConvergingGeneratingMap X G) :
    Generation.GeneratesAndConvergesToOneAlongOpenSubgroups (G := G) (Set.range (φ : X → G)) :=
  ⟨φ.generates, φ.convergesToOneAlongOpenSubgroups.range⟩

end ConvergingGeneratingMap

/-- A pointed pro-`C` group with unique lifts only for pointed maps whose images topologically
generate their targets.

This is intentionally not the unrestricted pointed-free universal property.-/
structure IsEpimorphicallyPointedFreeProCGroupOn
    (X : Type u) [TopologicalSpace X] (x0 : X)
    (F : Type u) [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ι : X → F) : Prop where
  /--
  Open normal subgroups with quotients in `C` form a neighborhood basis at one in `F`.-/
  hasOpenNormalBasisInClass : ProCGroups.ProC.HasOpenNormalBasisInClass C F
  /-- The canonical pointed map into `F` is continuous.-/
  continuous_ι : Continuous ι
  /-- The distinguished source point `x0` is sent to the identity of `F`.-/
  map_base : ι x0 = 1
  /-- The image of the canonical pointed map topologically generates `F`.-/
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  /--
  Every continuous, basepoint-preserving map whose image generates a pro-`C` target extends to
  a unique continuous group homomorphism from `F`.-/
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G],
    ProCGroups.ProC.HasOpenNormalBasisInClass C (G) →
      ∀ (φ : X → G), Continuous φ → φ x0 = 1 →
        Generation.TopologicallyGenerates (G := G) (Set.range φ) →
          ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

/-- A pro-`C` group with unique lifts only for open-subgroup-convergent families whose images
topologically generate their targets. The convergence hypothesis is
`FamilyConvergesToOneAlongOpenSubgroups`, not the unqualified filter predicate.

The `Epimorphically` qualifier records the missing unrestricted mapping property.-/
structure IsEpimorphicallyFreeProCGroupOnConvergingSet
    (X : Type v)
    (F : Type u) [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    (ι : X → F) : Prop where
  /--
  Open normal subgroups with quotients in `C` form a neighborhood basis at one in `F`.-/
  hasOpenNormalBasisInClass : ProCGroups.ProC.HasOpenNormalBasisInClass C F
  /--
  The canonical generator family has only finitely many terms outside each open subgroup of
  `F`.-/
  convergesToOneAlongOpenSubgroups : FamilyConvergesToOneAlongOpenSubgroups (G := F) ι
  /-- The canonical converging family topologically generates `F`.-/
  generates_range : Generation.TopologicallyGenerates (G := F) (Set.range ι)
  /--
  Every converging family that topologically generates a pro-`C` target extends to a unique
  continuous group homomorphism from `F`.-/
  existsUnique_lift :
    ∀ {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G],
    ProCGroups.ProC.HasOpenNormalBasisInClass C (G) →
      ∀ (φ : X → G), FamilyConvergesToOneAlongOpenSubgroups (G := G) φ →
        Generation.TopologicallyGenerates (G := G) (Set.range φ) →
          ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x

/-- The canonical map of a free pro-`C` group on a topological space is injective whenever the
predicate supplies enough separating pro-`C` targets.-/
theorem freeProCGroupOn_injective
    {X : Type u} [TopologicalSpace X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι : IsFreeProCGroup (C := C) ι)
    (hsep :
      ∀ ⦃x y : X⦄, x ≠ y →
        ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
          (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
    ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧
            ∃ φ : X → A, Continuous φ ∧
              Generation.TopologicallyGenerates (G := A) (Set.range φ) ∧ φ x ≠ φ y) :
    Function.Injective ι := by
  intro x y hEq
  by_contra hxy
  rcases hsep hxy with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A, _instTDA,
      hA, φ, hφ, hgenφ, hφxy⟩
  rcases hι.existsUnique_lift hA φ hφ with ⟨f, hf, _huniq⟩
  have hcontr : φ x = φ y := by
    simpa [hf.2 x, hf.2 y] using congrArg f hEq
  exact hφxy hcontr

/-- Under an explicit nontrivial cyclic pro-`C` target hypothesis, the identity does not lie in
the image of the topological basis of a free pro-`C` group.-/
theorem one_not_mem_range_of_freeProCGroupOn
    {X : Type u} [TopologicalSpace X] [Nonempty X]
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι : IsFreeProCGroup (C := C) ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
        (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
    ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    (1 : F) ∉ Set.range ι := by
  intro h1
  rcases h1 with ⟨x, hx⟩
  rcases hnontrivial with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A, _instTDA,
      hA, a, ha1, hgena⟩
  let φ : X → A := fun _ => a
  have hφ : Continuous φ := continuous_const
  have hrange : Set.range φ = ({a} : Set A) := by
    ext b
    constructor
    · rintro ⟨y, rfl⟩
      simp only [mem_singleton_iff, φ]
    · intro hb
      rw [Set.mem_singleton_iff] at hb
      subst b
      exact ⟨Classical.choice ‹Nonempty X›, rfl⟩
  have hgenφ : Generation.TopologicallyGenerates (G := A) (Set.range φ) := by
    simpa [hrange] using hgena
  rcases hι.existsUnique_lift hA φ hφ with ⟨f, hf, _huniq⟩
  have haeq : a = 1 := by
    simpa [φ, hx] using (hf.2 x).symm
  exact ha1 haeq

/-- Under an explicit nontrivial cyclic pro-`C` target hypothesis, the identity does not lie in a
basis converging to `1`.-/
theorem one_not_mem_range_of_epimorphicallyFreeProCGroupOnConvergingSet
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
        (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
    ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    (1 : F) ∉ Set.range ι := by
  classical
  intro h1
  rcases h1 with ⟨x, hx⟩
  rcases hnontrivial with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A, _instTDA,
      hA, a, ha1, hgena⟩
  let φ : X → A := fun z => if z = x then a else 1
  have hφconv : FamilyConvergesToOneAlongOpenSubgroups (G := A) φ := by
    intro U
    have hsubset : {z : X | φ z ∉ (U : Set A)} ⊆ ({x} : Set X) := by
      intro z hz
      by_cases hzx : z = x
      · simp only [hzx, mem_singleton_iff]
      · exfalso
        exact hz (by simp only [hzx, ↓reduceIte, SetLike.mem_coe, one_mem, φ])
    exact (Set.finite_singleton x).subset hsubset
  have hφgen : Generation.TopologicallyGenerates (G := A) (Set.range φ) := by
    have hsub : ({a} : Set A) ⊆ Set.range φ := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨x, by simp only [↓reduceIte, φ]⟩
    exact Generation.topologicallyGenerates_mono (G := A) hgena hsub
  rcases hι.existsUnique_lift hA φ hφconv hφgen with ⟨f, hf, _⟩
  have haeq : a = 1 := by
    simpa [φ, hx] using (hf.2 x).symm
  exact ha1 haeq

/-- Under the same nontrivial cyclic-target hypothesis, the basis map for a free pro-`C` group on
a set converging to `1` is injective.-/
theorem epimorphicallyFreeProCGroupOnConvergingSet_injective
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    (hnontrivial :
      ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
        (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
    ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧ ∃ a : A, a ≠ 1 ∧
          Generation.TopologicallyGenerates (G := A) ({a} : Set A)) :
    Function.Injective ι := by
  classical
  intro x y hEq
  by_contra hxy
  rcases hnontrivial with
    ⟨A, _instGroupA, _instTopA, _instTopGroupA, _instCompactA, _instT2A, _instTDA,
      hA, a, ha1, hgena⟩
  have hyx : y ≠ x := by
    intro hyx'
    exact hxy hyx'.symm
  let φ : X → A := fun z => if z = x then a else 1
  have hφconv : FamilyConvergesToOneAlongOpenSubgroups (G := A) φ := by
    intro U
    have hsubset : {z : X | φ z ∉ (U : Set A)} ⊆ ({x} : Set X) := by
      intro z hz
      by_cases hzx : z = x
      · simp only [hzx, mem_singleton_iff]
      · exfalso
        exact hz (by simp only [hzx, ↓reduceIte, SetLike.mem_coe, one_mem, φ])
    exact (Set.finite_singleton x).subset hsubset
  have hφgen : Generation.TopologicallyGenerates (G := A) (Set.range φ) := by
    have hsub : ({a} : Set A) ⊆ Set.range φ := by
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst z
      exact ⟨x, by simp only [↓reduceIte, φ]⟩
    exact Generation.topologicallyGenerates_mono (G := A) hgena hsub
  rcases hι.existsUnique_lift hA φ hφconv hφgen with ⟨f, hf, _⟩
  have hfa : f (ι x) = a := by
    simpa [φ] using hf.2 x
  have hf1 : f (ι y) = 1 := by
    simpa [φ, hyx] using hf.2 y
  have haeq : a = 1 := by
    rw [← hfa, ← hf1]
    exact congrArg f hEq
  exact ha1 haeq

/-- A nontrivial cyclic topological group has a nontrivial singleton topological generator.-/
theorem exists_nontrivial_singleton_topologicalGenerator
    {A : Type u} [Group A] [TopologicalSpace A] [IsTopologicalGroup A]
    [IsCyclic A] [Nontrivial A] :
    ∃ a : A, a ≠ 1 ∧ Generation.TopologicallyGenerates (G := A) ({a} : Set A) := by
  obtain ⟨a, ha⟩ := IsCyclic.exists_generator (α := A)
  have ha1 : a ≠ 1 := by
    intro hEq
    have hallOne : ∀ x : A, x = 1 := by
      intro x
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (ha x)
      simpa [hEq] using hn.symm
    exact not_subsingleton A ⟨fun x y => by rw [hallOne x, hallOne y]⟩
  refine ⟨a, ha1, ?_⟩
  rw [Generation.TopologicallyGenerates]
  apply top_unique
  intro x _
  exact Subgroup.le_topologicalClosure _ <| by
    simpa [Subgroup.zpowers_eq_closure] using ha x

/-- A concrete finite-group class containing a nontrivial finite cyclic group admits a
nontrivial topologically cyclic pro-`C` model.-/
theorem exists_nontrivial_topologicallyCyclic_proC_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (hquot : ProCGroups.FiniteGroupClass.QuotientClosed C)
    (hcyc :
      ∃ (A : Type u) (_ : Group A) (_ : Finite A),
        C A ∧ IsCyclic A ∧ Nontrivial A) :
    ∃ (A : Type u) (_ : Group A) (_ : TopologicalSpace A) (_ : IsTopologicalGroup A)
      (_ : CompactSpace A) (_ : T2Space A) (_ : TotallyDisconnectedSpace A),
      ProCGroups.ProC.HasOpenNormalBasisInClass C A ∧
        ∃ a : A, a ≠ 1 ∧ Generation.TopologicallyGenerates (G := A) ({a} : Set A) := by
  rcases hcyc with ⟨A, _instGroupA, _instFiniteA, hCA, hAcyc, hAnontriv⟩
  let _ : TopologicalSpace A := ⊥
  let _ : DiscreteTopology A := ⟨rfl⟩
  have hAProC : ProCGroups.ProC.HasOpenNormalBasisInClass C A := by
    exact ProCGroups.ProC.HasOpenNormalBasisInClass.of_finite_discrete
      (C := C) (G := A) hquot hCA
  rcases exists_nontrivial_singleton_topologicalGenerator (A := A) with ⟨a, ha1, hgena⟩
  exact
    ⟨A, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance,
      hAProC, a, ha1, hgena⟩

/--
If a continuous homomorphism has range containing a topological generating set, then it is
surjective between profinite groups.-/
theorem surjective_hom_of_rangeContainsGeneratingSet
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [CompactSpace F]
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    {ι : X → G}
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range ι))
    {σ : F →* G} (hσ : Continuous σ)
    (hsub : Set.range ι ⊆ (σ.range : Set G)) :
    Function.Surjective σ := by
  have hσgen : Generation.TopologicallyGenerates (G := G) ((σ.range : Set G)) :=
    Generation.topologicallyGenerates_mono (G := G) hgen hsub
  have hσclosed : IsClosed ((σ.range : Set G)) := by
    simpa using (isCompact_range hσ).isClosed
  have hσclosure_le : (σ.range : Subgroup G).topologicalClosure ≤ σ.range :=
    Subgroup.topologicalClosure_minimal _ le_rfl hσclosed
  have hσclosure_top : (σ.range : Subgroup G).topologicalClosure = ⊤ := by
    have htop :
        (Subgroup.closure (σ.range : Set G)).topologicalClosure = (⊤ : Subgroup G) := by
      simpa [Generation.TopologicallyGenerates] using hσgen
    have hclosure_eq : (σ.range : Subgroup G) = Subgroup.closure (σ.range : Set G) := by
      simpa using (Subgroup.closure_eq (σ.range)).symm
    rw [hclosure_eq]
    exact htop
  have hσrange_top : σ.range = ⊤ := by
    apply top_unique
    intro z hz
    have hz' : z ∈ ((σ.range : Subgroup G).topologicalClosure : Set G) := by
      rw [hσclosure_top]
      simp only [Subgroup.coe_top, mem_univ]
    exact hσclosure_le hz'
  intro z
  have hz : z ∈ (σ.range : Set G) := by
    simp only [hσrange_top, Subgroup.coe_top, mem_univ]
  simpa using hz

/-- A fixed free pro-`C` group on a set converging to `1` admits a continuous epimorphism onto any
profinite pro-`C` target generated by the image of its basis.-/
theorem exists_epimorphicallyFreeProCGroupOnConvergingSet_surjecting
    {X : Type u}
    {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
    [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
    {ι : X → F}
    (hF : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G))
    (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    ∃ ψ : F →* G, Continuous ψ ∧ Function.Surjective ψ ∧ ∀ x, ψ (ι x) = φ x := by
  rcases hF.existsUnique_lift hG φ hφ hgen with ⟨ψ, hψ, _⟩
  have hsub : Set.range φ ⊆ (ψ.range : Set G) := by
    rintro z ⟨x, rfl⟩
    exact ⟨ι x, hψ.2 x⟩
  have hψsurj : Function.Surjective ψ :=
    surjective_hom_of_rangeContainsGeneratingSet
      hgen hψ.1 hsub
  exact ⟨ψ, hψ.1, hψsurj, hψ.2⟩

/-- The pro-`C` completion of the abstract free group on a finite basis is free pro-`C` on that
basis.-/
theorem proCCompletionOfAbstractFreeGroup_is_free
    {X : Type u} [Finite X]
    [TopologicalSpace (FreeGroup X)] [IsTopologicalGroup (FreeGroup X)]
    [DiscreteTopology (FreeGroup X)]
    {Fhat : Type u} [Group Fhat] [TopologicalSpace Fhat] [IsTopologicalGroup Fhat]
    [CompactSpace Fhat] [T2Space Fhat] [TotallyDisconnectedSpace Fhat]
    {ι : FreeGroup X →ₜ* Fhat}
    (hι : ProCGroups.Completion.IsProCCompletion C (FreeGroup X) Fhat ι) :
    IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X Fhat
      (fun x => ι (FreeGroup.of x)) := by
  refine ⟨hι.hasOpenNormalBasisInClass, ?_, ?_, ?_⟩
  · exact FamilyConvergesToOneAlongOpenSubgroups.of_finite_domain (G := Fhat)
      (fun x : X => ι (FreeGroup.of x))
  · have himage :
        ι '' Set.range (FreeGroup.of : X → FreeGroup X) =
          Set.range (fun x : X => ι (FreeGroup.of x)) := by
      calc
        ι '' Set.range (FreeGroup.of : X → FreeGroup X) =
            Set.range ((⇑ι) ∘ (FreeGroup.of : X → FreeGroup X)) :=
          (Set.range_comp ι (FreeGroup.of : X → FreeGroup X)).symm
        _ = Set.range (fun x : X => ι (FreeGroup.of x)) := by rfl
    have hclosure :
        Subgroup.closure (Set.range fun x : X => ι (FreeGroup.of x)) =
          ι.toMonoidHom.range := by
      calc
        Subgroup.closure (Set.range fun x : X => ι (FreeGroup.of x))
            = Subgroup.map ι.toMonoidHom
                (Subgroup.closure (Set.range (FreeGroup.of : X → FreeGroup X))) := by
              simpa [himage] using
                (ι.toMonoidHom.map_closure (Set.range (FreeGroup.of : X → FreeGroup X))).symm
        _ = ι.toMonoidHom.range := by
          rw [FreeGroup.closure_range_of X, MonoidHom.range_eq_map]
    rw [Generation.TopologicallyGenerates, hclosure]
    rw [SetLike.ext'_iff, Subgroup.topologicalClosure_coe, Subgroup.coe_top]
    simpa [DenseRange, MonoidHom.coe_range, dense_iff_closure_eq] using hι.denseRange
  · intro G _ _ _ _ _ _ hG φ _hφ hgen
    let φfree : FreeGroup X →ₜ* G :=
      { toMonoidHom := FreeGroup.lift φ
        continuous_toFun := by
          simpa using (continuous_of_discreteTopology : Continuous (FreeGroup.lift φ)) }
    let φhat : Fhat →ₜ* G := hι.lift hG φfree
    refine ⟨φhat.toMonoidHom, ?_, ?_⟩
    · refine ⟨φhat.continuous_toFun, ?_⟩
      intro x
      have hfac := congrArg (fun ψ : FreeGroup X →ₜ* G => ψ (FreeGroup.of x))
        (hι.lift_spec hG φfree)
      have hfree : φfree (FreeGroup.of x) = φ x := by
        change FreeGroup.lift φ (FreeGroup.of x) = φ x
        simp only [FreeGroup.lift_apply_of]
      exact hfac.trans hfree
    · intro g hg
      let gCont : Fhat →ₜ* G := { toMonoidHom := g, continuous_toFun := hg.1 }
      have hfac' : gCont.comp ι = φfree := by
        apply ContinuousMonoidHom.toMonoidHom_injective
        ext x
        change g (ι (FreeGroup.of x)) = FreeGroup.lift φ (FreeGroup.of x)
        exact (hg.2 x).trans (by simp only [FreeGroup.lift_apply_of])
      exact congrArg ContinuousMonoidHom.toMonoidHom (hι.lift_unique hG φfree hfac')

namespace IsEpimorphicallyFreeProCGroupOnConvergingSet

variable {X : Type v}
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable {F' : Type u} [Group F'] [TopologicalSpace F'] [IsTopologicalGroup F']
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable [CompactSpace F'] [T2Space F'] [TotallyDisconnectedSpace F']
variable {ι : X → F}

/-- The lift supplied by the corresponding free pro-`C` universal property.-/
noncomputable def lift
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    F →* G :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ hgen))

/-- The universal-property lift has the prescribed values on the chosen generators.-/
theorem lift_spec
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    Continuous (hι.lift hG φ hφ hgen) ∧
      ∀ x, hι.lift hG φ hφ hgen (ι x) = φ x :=
  Classical.choose_spec (ExistsUnique.exists (hι.existsUnique_lift hG φ hφ hgen))

/-- The universal-property lift is unique among continuous maps with the prescribed values.-/
theorem lift_unique
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ))
    {f : F →* G} (hf : Continuous f) (hfac : ∀ x, f (ι x) = φ x) :
    f = hι.lift hG φ hφ hgen := by
  exact
    (hι.existsUnique_lift hG φ hφ hgen).unique ⟨hf, hfac⟩
      (hι.lift_spec hG φ hφ hgen)

/-- For a concrete finite-group class, the generated-target universal property of a free
pro-`C` group on a converging set extends any target map that converges to `1`.  This formulation
supports retractions that collapse all but finitely many basis elements.-/
theorem existsUnique_lift_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C G)
    (φ : X → G) (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ) :
    ∃! f : F →* G, Continuous f ∧ ∀ x, f (ι x) = φ x := by
  classical
  let K : ClosedSubgroup G := Generation.closedSubgroupGenerated (G := G) (Set.range φ)
  let : CompactSpace ↥(K : Subgroup G) := by
    exact
      (show IsClosed (((K : Subgroup G) : Set G)) from
          K.2).isClosedEmbedding_subtypeVal.compactSpace
  let φK : X → ↥(K : Subgroup G) := Generation.closedSubgroupGeneratedMap (G := G) φ
  have hφKconv : FamilyConvergesToOneAlongOpenSubgroups (G := ↥(K : Subgroup G)) φK := by
    intro U
    have hU_nhds : ((U : Subgroup ↥(K : Subgroup G)) : Set ↥(K : Subgroup G)) ∈
        𝓝 (1 : ↥(K : Subgroup G)) :=
      U.isOpen'.mem_nhds U.one_mem'
    rcases
        (mem_nhds_subtype ((K : Subgroup G) : Set G) (1 : ↥(K : Subgroup G))
          ((U : Subgroup ↥(K : Subgroup G)) : Set ↥(K : Subgroup G))).1 hU_nhds with
      ⟨W₀, hW₀_nhds, hW₀U⟩
    rcases mem_nhds_iff.mp hW₀_nhds with ⟨W, hWU₀, hWopen, h1W⟩
    rcases hG W hWopen h1W with ⟨V, hVW, _hCV⟩
    have hsub :
        {x : X | φK x ∉ (U : Set ↥(K : Subgroup G))} ⊆
          {x : X | φ x ∉ ((V.toOpenSubgroup : OpenSubgroup G) : Set G)} := by
      intro x hx hxV
      exact hx (hW₀U (by
        change φ x ∈ W₀
        exact hWU₀ (hVW hxV)))
    exact (hφ V.toOpenSubgroup).subset hsub
  have hφKgen :
      Generation.TopologicallyGenerates (G := ↥(K : Subgroup G)) (Set.range φK) := by
    simpa [φK] using
      (Generation.closedSubgroupGeneratedMap_topologicallyGenerates (G := G) φ)
  have hK : ProCGroups.ProC.HasOpenNormalBasisInClass C ↥(K : Subgroup G) :=
    ProCGroups.ProC.HasOpenNormalBasisInClass.of_closedSubgroup hIso hSub hG K
  rcases hι.existsUnique_lift hK φK hφKconv hφKgen with ⟨fK, hfK, huniqK⟩
  let incl : ↥(K : Subgroup G) →* G := (K : Subgroup G).subtype
  let f : F →* G := incl.comp fK
  refine ⟨f, ⟨?_, ?_⟩, ?_⟩
  · exact continuous_subtype_val.comp hfK.1
  · intro x
    exact congrArg Subtype.val (hfK.2 x)
  · intro g hg
    have hgK_mem : ∀ y : F, g y ∈ (K : Subgroup G) := by
      intro y
      have hy :
          y ∈ (Generation.closedSubgroupGenerated (G := F) (Set.range ι) : Subgroup F) := by
        change y ∈ ((Subgroup.closure (Set.range ι)).topologicalClosure : Subgroup F)
        rw [hι.generates_range]
        simp only [Subgroup.mem_top]
      have hgy :=
        Generation.map_mem_closedSubgroupGenerated_image
          (G := F) (H := G)
          ({ toMonoidHom := g, continuous_toFun := hg.1 } : F →ₜ* G)
          (X := Set.range ι) hy
      have himage :
          (({ toMonoidHom := g, continuous_toFun := hg.1 } : F →ₜ* G) ''
              Set.range ι) = Set.range φ := by
        ext z
        constructor
        · rintro ⟨y, ⟨x, rfl⟩, rfl⟩
          exact ⟨x, (hg.2 x).symm⟩
        · rintro ⟨x, rfl⟩
          exact ⟨ι x, ⟨x, rfl⟩, hg.2 x⟩
      change
        g y ∈ Generation.closedSubgroupGenerated
          (({ toMonoidHom := g, continuous_toFun := hg.1 } : F →ₜ* G) ''
            Set.range ι) at hgy
      rw [himage] at hgy
      exact hgy
    let gK : F →* ↥(K : Subgroup G) :=
      { toFun := fun y => ⟨g y, hgK_mem y⟩
        map_one' := by
          apply Subtype.ext
          simp only [map_one, OneMemClass.coe_one]
        map_mul' := by
          intro a b
          apply Subtype.ext
          simp only [map_mul, MulMemClass.mk_mul_mk]}
    have hgKcont : Continuous gK := by
      exact Continuous.subtype_mk hg.1 (fun y => (gK y).2)
    have hgKfac : ∀ x, gK (ι x) = φK x := by
      intro x
      apply Subtype.ext
      exact hg.2 x
    have hgK_eq : gK = fK := huniqK gK ⟨hgKcont, hgKfac⟩
    ext y
    exact congrArg Subtype.val (congrArg (fun f : F →* ↥(K : Subgroup G) => f y) hgK_eq)

/-- Continuous-homomorphism form of
`existsUnique_lift_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass`.-/
theorem existsUnique_liftHom_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
    (C : ProCGroups.FiniteGroupClass.{u})
    (hIso : ProCGroups.FiniteGroupClass.IsomClosed C)
    (hSub : ProCGroups.FiniteGroupClass.SubgroupClosed C)
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C G)
    (φ : X → G) (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ) :
    ∃! f : F →ₜ* G, ∀ x, f (ι x) = φ x := by
  rcases existsUnique_lift_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
      C hIso hSub hι hG φ hφ with
    ⟨f, hf, huniq⟩
  let fc : F →ₜ* G :=
    { toMonoidHom := f
      continuous_toFun := hf.1 }
  refine ⟨fc, hf.2, ?_⟩
  intro g hg
  apply ContinuousMonoidHom.toMonoidHom_injective
  exact huniq g.toMonoidHom ⟨g.continuous, hg⟩

/-- In a free pro-`Σ` group with nonempty `Σ`, a free generator has no positive torsion.-/
theorem generator_pow_ne_one_of_sigma
    {σ : Set ℕ} (hσ : ∃ p, p ∈ σ ∧ Nat.Prime p)
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := (ProCGroups.FiniteGroupClass.sigmaGroup σ)) X F ι)
    (i : X) (N : ℕ) (hN : 0 < N) :
    (ι i) ^ N ≠ 1 := by
  classical
  rcases hσ with ⟨p, hpσ, hp⟩
  let M := p ^ (N + 1)
  have hMpos : 0 < M := pow_pos hp.pos (N + 1)
  have hsigmaM : ProCGroups.FiniteGroupClass.IsSigmaNumber σ M :=
    ProCGroups.FiniteGroupClass.IsSigmaNumber.prime_pow_of_mem
      (sigma := σ) (p := p) (k := N + 1) hpσ hp
  let T := ULift.{u} (Multiplicative (ZMod M))
  let : NeZero M := ⟨Nat.ne_of_gt hMpos⟩
  let φ : X → T :=
    fun j => if j = i then ULift.up (Multiplicative.ofAdd (1 : ZMod M)) else 1
  have hφconv : FamilyConvergesToOneAlongOpenSubgroups (G := T) φ := by
    intro U
    refine (Set.finite_singleton i).subset ?_
    intro j hj
    by_cases hji : j = i
    · simp only [hji, Set.mem_singleton_iff]
    · have hφj : φ j = 1 := by simp only [hji, ↓reduceIte, φ]
      have hmem : φ j ∈ (U : Set T) := by simp only [hφj, SetLike.mem_coe, one_mem]
      exact False.elim (hj hmem)
  have hTclass : ProCGroups.FiniteGroupClass.sigmaGroup σ T :=
    ProCGroups.FiniteGroupClass.sigmaGroup_cyclicZMod (sigma := σ) hMpos hsigmaM
  have hT :
      ProCGroups.ProC.HasOpenNormalBasisInClass
        (ProCGroups.FiniteGroupClass.sigmaGroup σ) T :=
    ProCGroups.ProC.HasOpenNormalBasisInClass.of_finite_discrete
      (C := ProCGroups.FiniteGroupClass.sigmaGroup σ)
      (G := T)
      (ProCGroups.FiniteGroupClass.sigmaGroup_quotientClosed σ)
      hTclass
  rcases hι.existsUnique_liftHom_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
      (ProCGroups.FiniteGroupClass.sigmaGroup σ)
      (ProCGroups.FiniteGroupClass.sigmaGroup_isomClosed σ)
      (ProCGroups.FiniteGroupClass.sigmaGroup_subgroupClosed σ)
      hT φ hφconv with
    ⟨f, hf, _⟩
  intro hpow
  have hf_pow : f ((ι i) ^ N) = 1 := by simp only [hpow, map_one]
  have hcalc : f ((ι i) ^ N) = ULift.up (Multiplicative.ofAdd (N : ZMod M)) := by
    calc
      f ((ι i) ^ N) = (f (ι i)) ^ N := by simp only [map_pow]
      _ = (φ i) ^ N := by rw [hf i]
      _ = (ULift.up (Multiplicative.ofAdd (1 : ZMod M))) ^ N := by simp only [↓reduceIte, φ]
      _ = ULift.up (Multiplicative.ofAdd (N : ZMod M)) := by
        apply ULift.ext
        change (Multiplicative.ofAdd (1 : ZMod M)) ^ N =
          Multiplicative.ofAdd (N : ZMod M)
        change Multiplicative.ofAdd ((N : ℕ) • (1 : ZMod M)) =
          Multiplicative.ofAdd (N : ZMod M)
        simp only [nsmul_eq_mul, mul_one]
  have hlt_pow : N < p ^ (N + 1) :=
    lt_of_lt_of_le
      (Nat.lt_pow_self (n := N) (a := p) hp.one_lt)
      (Nat.pow_le_pow_right hp.pos (Nat.le_succ N))
  have hNmod : (N : ZMod M) ≠ 0 := by
    intro hzero
    have hdiv : M ∣ N := (ZMod.natCast_eq_zero_iff N M).mp hzero
    exact (Nat.not_dvd_of_pos_of_lt hN hlt_pow) hdiv
  have hofAdd_ne : ULift.up (Multiplicative.ofAdd (N : ZMod M)) ≠ (1 : T) := by
    intro h
    have hdown : Multiplicative.ofAdd (N : ZMod M) = 1 := congrArg ULift.down h
    have hz : (N : ZMod M) = 0 := by
      change Multiplicative.ofAdd (N : ZMod M) =
        Multiplicative.ofAdd (0 : ZMod M) at hdown
      exact Multiplicative.ofAdd.injective hdown
    exact hNmod hz
  exact hofAdd_ne (hcalc.symm.trans hf_pow)

/-- Integer-power form of `generator_pow_ne_one_of_sigma`.-/
theorem generator_zpow_ne_one_of_sigma
    {σ : Set ℕ} (hσ : ∃ p, p ∈ σ ∧ Nat.Prime p)
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := (ProCGroups.FiniteGroupClass.sigmaGroup σ)) X F ι)
    (i : X) (n : ℤ) (hn : n ≠ 0) :
    (ι i) ^ n ≠ 1 := by
  intro hzn
  have hnat_pos : 0 < n.natAbs := Int.natAbs_pos.mpr hn
  have hnat_ne :
      (ι i) ^ n.natAbs ≠ 1 :=
    hι.generator_pow_ne_one_of_sigma hσ i n.natAbs hnat_pos
  apply hnat_ne
  by_cases hnonneg : 0 ≤ n
  · have hnat : (n.natAbs : ℤ) = n := Int.natAbs_of_nonneg hnonneg
    simpa [zpow_natCast, hnat] using hzn
  · have hneg : n < 0 := lt_of_not_ge hnonneg
    have hnat : (n.natAbs : ℤ) = -n := Int.ofNat_natAbs_of_nonpos hneg.le
    have hzn' : (ι i) ^ (-n) = 1 := by
      calc
        (ι i) ^ (-n) = ((ι i) ^ n)⁻¹ := by rw [zpow_neg]
        _ = 1 := by simp only [hzn, inv_one]
    simpa [zpow_natCast, hnat] using hzn'

/-- The continuous homomorphism supplied by the free pro-`C` universal property.-/
noncomputable def liftHom
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) :
    F →ₜ* G where
  toMonoidHom := hι.lift hG φ hφ hgen
  continuous_toFun := (hι.lift_spec hG φ hφ hgen).1

/-- Bundled version of `liftHom`, taking a converging generating map as a single argument.-/
noncomputable def liftConvergingGeneratingMap
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : ConvergingGeneratingMap X G) :
    F →ₜ* G :=
  hι.liftHom hG φ φ.convergesToOneAlongOpenSubgroups φ.generates

/-- The bundled lift has the prescribed value on each generator.-/
@[simp] theorem liftConvergingGeneratingMap_apply
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : ConvergingGeneratingMap X G) (x
        : X) :
    hι.liftConvergingGeneratingMap hG φ (ι x) = φ x := by
  change hι.lift hG φ φ.convergesToOneAlongOpenSubgroups φ.generates (ι x) = φ x
  exact (hι.lift_spec hG φ φ.convergesToOneAlongOpenSubgroups φ.generates).2 x

/-- `liftHom` has the prescribed value on each generator.-/
@[simp] theorem liftHom_apply
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι)
    {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]
    (hG : ProCGroups.ProC.HasOpenNormalBasisInClass C (G)) (φ : X → G)
    (hφ : FamilyConvergesToOneAlongOpenSubgroups (G := G) φ)
    (hgen : Generation.TopologicallyGenerates (G := G) (Set.range φ)) (x : X) :
    hι.liftHom hG φ hφ hgen (ι x) = φ x :=
  (hι.lift_spec hG φ hφ hgen).2 x

section FiniteSupportRetracts

variable {C : ProCGroups.FiniteGroupClass.{u}}
variable [hVar : Fact (ProCGroups.FiniteGroupClass.Variety C)]
variable {X : Type v} [DecidableEq X]
variable {F : Type u} [Group F] [TopologicalSpace F] [IsTopologicalGroup F]
variable [CompactSpace F] [T2Space F] [TotallyDisconnectedSpace F]
variable {ι : X → F}

/-- The unique continuous endomorphism of a free pro-`C` group that keeps the finite set `S`
of basis elements and sends the remaining basis elements to `1`.-/
theorem existsUnique_collapseToFinset_of_finiteGroupClass
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    ∃! φ : F →ₜ* F, ∀ x, φ (ι x) = if x ∈ S then ι x else 1 := by
  have hconv :
      FamilyConvergesToOneAlongOpenSubgroups (G := F) (fun x => if x ∈ S then ι x else 1) := by
    intro U
    classical
    refine S.finite_toSet.subset ?_
    intro x hx
    by_cases hxS : x ∈ S
    · exact hxS
    · exfalso
      exact hx (by simp only [hxS, ↓reduceIte, SetLike.mem_coe, one_mem])
  exact
    hι.existsUnique_liftHom_of_convergesToOneAlongOpenSubgroups_of_finiteGroupClass
      C C.isomClosed hVar.out.subgroupClosed
      hι.hasOpenNormalBasisInClass (fun x => if x ∈ S then ι x else 1) hconv

/-- The finite-support retraction of a free pro-`C` group onto the closed subgroup generated by a
finite set of basis elements.-/
noncomputable def collapseToFinset
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    F →ₜ* F :=
  Classical.choose (ExistsUnique.exists (hι.existsUnique_collapseToFinset_of_finiteGroupClass S))

/-- Collapsing to a finite set fixes the selected generators.-/
@[simp] theorem collapseToFinset_apply_mem
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S : Finset X} {x : X} (hx : x ∈ S) :
    hι.collapseToFinset S (ι x) = ι x := by
  simpa [hx, collapseToFinset] using
    (Classical.choose_spec
      (ExistsUnique.exists (hι.existsUnique_collapseToFinset_of_finiteGroupClass S)) x)

/-- Collapsing to a finite set sends every unselected generator to the identity.-/
@[simp] theorem collapseToFinset_apply_not_mem
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S : Finset X} {x : X} (hx : x ∉ S) :
    hι.collapseToFinset S (ι x) = 1 := by
  simpa [hx, collapseToFinset] using
    (Classical.choose_spec
      (ExistsUnique.exists (hι.existsUnique_collapseToFinset_of_finiteGroupClass S)) x)

/-- Collapsing twice to the same finite set is the same as collapsing once.-/
@[simp] theorem collapseToFinset_idempotent
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    (hι.collapseToFinset S).comp (hι.collapseToFinset S) =
      hι.collapseToFinset S := by
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ S
  · simp only [ContinuousMonoidHom.comp_toFun, hx, collapseToFinset_apply_mem]
  · simp only [ContinuousMonoidHom.comp_toFun, hx, not_false_eq_true,
      collapseToFinset_apply_not_mem, map_one]

/-- A homomorphism that kills every basis element outside `S` is unchanged after precomposition
with the finite-support retraction.-/
theorem comp_collapseToFinset_eq_of_eq_one_outside
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {G : Type w} [Group G] [TopologicalSpace G] [T2Space G]
    (φ : F →ₜ* G) (S : Finset X)
    (hφ : ∀ x, x ∉ S → φ (ι x) = 1) :
    φ.comp (hι.collapseToFinset S) = φ := by
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  by_cases hx : x ∈ S
  · simp only [ContinuousMonoidHom.comp_toFun, hx, collapseToFinset_apply_mem]
  · simp only [ContinuousMonoidHom.comp_toFun, hx, not_false_eq_true,
      collapseToFinset_apply_not_mem, map_one,
  hφ x hx]

/-- The map from the free pro-`C` group onto the range of its finite-support retraction.-/
noncomputable def collapseToFinsetRange
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    F →ₜ* ↥((hι.collapseToFinset S : F →* F).range) :=
  { toMonoidHom := (hι.collapseToFinset S : F →* F).rangeRestrict
    continuous_toFun :=
      (hι.collapseToFinset S).continuous.subtype_mk (fun x => ⟨x, rfl⟩) }

/-- The inclusion of the range of a finite-support retraction back into the ambient free group.-/
noncomputable def collapseToFinsetInclusion
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    ↥((hι.collapseToFinset S : F →* F).range) →ₜ* F :=
  { toMonoidHom := ((hι.collapseToFinset S : F →* F).range).subtype
    continuous_toFun := continuous_subtype_val }

/-- The range of the finite-support retraction, viewed as the finite-basis retract.-/
abbrev FinsetSupportRetract
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) : Type u :=
  ↥((hι.collapseToFinset S : F →* F).range)

/-- The finite basis of the finite-support retract.-/
noncomputable def finsetSupportBasis
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    (S : Finset X) :
    S → hι.FinsetSupportRetract S := by
  intro x
  refine ⟨ι x.1, ?_⟩
  exact ⟨ι x.1, hι.collapseToFinset_apply_mem x.2⟩

/-- If `S ⊆ T`, then collapsing first to `T` and then to `S` is the same as
collapsing directly to `S`. This is the basic compatibility relation for the finite-basis
projections.-/
theorem collapseToFinset_small_comp_large_of_subset
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S T : Finset X} (hST : S ⊆ T) :
    (hι.collapseToFinset S).comp (hι.collapseToFinset T) =
      hι.collapseToFinset S := by
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  by_cases hxS : x ∈ S
  · have hxT : x ∈ T := hST hxS
    simp only [ContinuousMonoidHom.comp_toFun, hxT, collapseToFinset_apply_mem, hxS]
  · by_cases hxT : x ∈ T
    · simp only [ContinuousMonoidHom.comp_toFun, hxT, collapseToFinset_apply_mem, hxS,
        not_false_eq_true,
collapseToFinset_apply_not_mem]
    · simp only [ContinuousMonoidHom.comp_toFun, hxT, not_false_eq_true,
        collapseToFinset_apply_not_mem, map_one,
hxS]

/-- If `S ⊆ T`, then collapsing to `S` and then to `T` is again the collapse to `S`.
Equivalently, the finite-support image for `S` is fixed by every larger finite-support
projection.-/
theorem collapseToFinset_large_comp_small_of_subset
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S T : Finset X} (hST : S ⊆ T) :
    (hι.collapseToFinset T).comp (hι.collapseToFinset S) =
      hι.collapseToFinset S := by
  apply Generation.continuousMonoidHom_ext_of_topologicallyGenerates hι.generates_range
  rintro _ ⟨x, rfl⟩
  by_cases hxS : x ∈ S
  · have hxT : x ∈ T := hST hxS
    simp only [ContinuousMonoidHom.comp_toFun, hxS, collapseToFinset_apply_mem, hxT]
  · simp only [ContinuousMonoidHom.comp_toFun, hxS, not_false_eq_true,
      collapseToFinset_apply_not_mem, map_one]

/-- The transition map from the finite-support retract for `T` to the one for `S`, for
`S ⊆ T`. It is the projection obtained by including the `T`-retract into the ambient free
pro-`C` group and then collapsing to `S`.-/
noncomputable def finsetSupportTransition
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S T : Finset X} :
    hι.FinsetSupportRetract T →ₜ* hι.FinsetSupportRetract S :=
  { toMonoidHom := (hι.collapseToFinsetRange S).toMonoidHom.comp
      (hι.collapseToFinsetInclusion T).toMonoidHom
    continuous_toFun :=
      (hι.collapseToFinsetRange S).continuous.comp
        (hι.collapseToFinsetInclusion T).continuous }

/-- The transition from a larger finite support to a smaller one preserves the basis elements
indexed by the smaller support.-/
@[simp] theorem finsetSupportTransition_apply_basis
    (hι :
      IsEpimorphicallyFreeProCGroupOnConvergingSet
        (C := C) X F ι)
    {S T : Finset X} (hST : S ⊆ T) (x : S) :
    hι.finsetSupportTransition (S := S) (T := T)
        (hι.finsetSupportBasis T ⟨x.1, hST x.2⟩) =
      hι.finsetSupportBasis S x := by
  apply Subtype.ext
  change hι.collapseToFinset S (ι x.1) = ι x.1
  exact hι.collapseToFinset_apply_mem x.2

end FiniteSupportRetracts

/-- The lift of the canonical generator map to the same free pro-`C` group is the identity.-/
@[simp 900] theorem lift_id
    (hι : IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) X F ι) :
    hι.lift hι.hasOpenNormalBasisInClass ι hι.convergesToOneAlongOpenSubgroups
        hι.generates_range = MonoidHom.id F := by
  symm
  exact hι.lift_unique hι.hasOpenNormalBasisInClass ι hι.convergesToOneAlongOpenSubgroups
      hι.generates_range continuous_id
    (by intro x; rfl)

end IsEpimorphicallyFreeProCGroupOnConvergingSet

/-- Packaged carrier with the epimorphic convergent-family lifting property.-/
structure EpimorphicallyFreeProCGroupOnConvergingSetData
    (C : ProCGroups.FiniteGroupClass) where
  /-- The index type of the distinguished converging generating family.-/
  basis : Type u
  /-- The bundled pro-`C` group generated by the distinguished family.-/
  carrier : ProCGrp C
  /-- The distinguished family of elements of the bundled carrier.-/
  inclusion : basis → carrier
  /--
  The inclusion is convergent and generating, and satisfies the epimorphic free pro-`C`
  universal property.-/
  isEpimorphicallyFree :
    IsEpimorphicallyFreeProCGroupOnConvergingSet (C := C) basis carrier inclusion

end

end ProCGroups.FreeProC
