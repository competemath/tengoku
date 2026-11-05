/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.Seed.Topology.Algebra.Group.Quotient
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.Topologies.ContinuousMulEquiv

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuous maps between group quotients

This file develops algebraic and continuous equivalences induced by surjective homomorphisms,
lifts and maps between quotient groups, congruences between quotients, and restrictions to
preimages of subgroups.
-/

open scoped Topology

universe u v

namespace ProCGroups

namespace QuotientGroup

section Algebra

variable {G : Type u} {H : Type v} [Group G] [Group H]

/--
The comap of a quotient subgroup is determined by the representative-level map when the kernel
condition holds.
@isnad1 id=eq.2h5v.s6.f9256df5b7f7 from=translated src=- shape=710a452b vocab=802e3a73
-/
theorem comap_eq_of_map_eq_of_ker_le
    (f : G →* H) {N : Subgroup G} {M : Subgroup H}
    (hmap : N.map f = M) (hker : f.ker ≤ N) :
    M.comap f = N := by
  calc
    M.comap f = (N.map f).comap f := by simp only [hmap]
    _ = N ⊔ f.ker := by simpa using (Subgroup.comap_map_eq (f := f) (H := N))
    _ = N := sup_eq_left.2 hker

/--
Under the kernel condition, the induced quotient map has trivial kernel for the corresponding
representative-level map.-/
private theorem map_ker_eq_bot_of_map_eq_of_ker_le
    (f : G →* H) {N : Subgroup G} {M : Subgroup H} [N.Normal] [M.Normal]
    (hNM : N ≤ M.comap f) (hmap : N.map f = M) (hker : f.ker ≤ N) :
    (QuotientGroup.map (N := N) (M := M) (f := f) hNM).ker = ⊥ := by
  have hcomap : M.comap f = N := comap_eq_of_map_eq_of_ker_le f hmap hker
  calc
    (QuotientGroup.map (N := N) (M := M) (f := f) hNM).ker =
        Subgroup.map (QuotientGroup.mk' N) (Subgroup.comap f M) := by
          simpa using QuotientGroup.ker_map (N := N) (M := M) (f := f) hNM
    _ = Subgroup.map (QuotientGroup.mk' N) N := by simp only [hcomap,
        _root_.QuotientGroup.map_mk'_self]
    _ = ⊥ := by
      refine (Subgroup.map_eq_bot_iff (f := QuotientGroup.mk' N) (H := N)).2 ?_
      intro x hx
      simpa using hx

/--
A surjective homomorphism induces an isomorphism on quotients whenever it maps the source normal
subgroup onto the target normal subgroup and its kernel is contained in the source normal
subgroup.-/
noncomputable def mapMulEquivOfSurjective
    (f : G →* H) {N : Subgroup G} {M : Subgroup H} [N.Normal] [M.Normal]
    (hf : Function.Surjective f) (hmap : N.map f = M) (hker : f.ker ≤ N) :
    G ⧸ N ≃* H ⧸ M := by
  have hNM : N ≤ M.comap f := by
    intro x hx
    change f x ∈ M
    simpa [hmap] using (show f x ∈ N.map f from ⟨x, hx, rfl⟩)
  let φ : G ⧸ N →* H ⧸ M :=
    QuotientGroup.map (N := N) (M := M) (f := f) hNM
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective M y
    rcases hf h with ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk' N g, rfl⟩
  have hkerφ : φ.ker = ⊥ := by
    dsimp [φ]
    exact map_ker_eq_bot_of_map_eq_of_ker_le (f := f) hNM hmap hker
  have hinj : Function.Injective φ :=
    (MonoidHom.ker_eq_bot_iff (f := φ)).1 hkerφ
  exact MulEquiv.ofBijective φ ⟨hinj, hsurj⟩

/-- A surjective homomorphism induces the expected multiplicative equivalence on quotient groups.
@isnad1 id=eq.3h6v.s9.44571313e73a from=translated src=- shape=59595a1f vocab=d2457057
-/
@[simp] theorem mapMulEquivOfSurjective_apply_mk
    (f : G →* H) {N : Subgroup G} {M : Subgroup H} [N.Normal] [M.Normal]
    (hf : Function.Surjective f) (hmap : N.map f = M) (hker : f.ker ≤ N) (g : G) :
    mapMulEquivOfSurjective (G := G) (H := H) f hf hmap hker (QuotientGroup.mk' N g) =
      QuotientGroup.mk' M (f g) := by
  rfl

end Algebra

section Topology

variable {G : Type u} {H : Type v}
variable [Group G] [TopologicalSpace G]
variable [Group H] [TopologicalSpace H]

/-- The lifted continuous quotient map is induced by the quotient universal property.-/
def liftₜ
    (N : Subgroup G) [N.Normal] (f : G →ₜ* H)
    (hN : N ≤ f.toMonoidHom.ker) :
    G ⧸ N →ₜ* H := by
  let φ : G ⧸ N →* H := QuotientGroup.lift N f.toMonoidHom hN
  have hcomp : Continuous (fun x : G => φ (QuotientGroup.mk' N x)) := by
    simpa [φ, QuotientGroup.lift_mk'] using f.continuous_toFun
  have hcont : Continuous φ :=
    (QuotientGroup.isQuotientMap_mk (G := G) (N := N)).continuous_iff.2 hcomp
  exact
    { toMonoidHom := φ
      continuous_toFun := hcont }

/-- The continuous homomorphism induced on quotients by a continuous homomorphism.-/
def mapContinuousMonoidHom
    (f : G →ₜ* H) {N : Subgroup G} {M : Subgroup H} [N.Normal] [M.Normal]
    (hNM : N ≤ M.comap f.toMonoidHom) :
    G ⧸ N →ₜ* H ⧸ M := by
  let φ : G ⧸ N →* H ⧸ M :=
    QuotientGroup.map (N := N) (M := M) (f := f.toMonoidHom) hNM
  have hcomp : Continuous (fun x : G => φ (QuotientGroup.mk' N x)) := by
    dsimp [φ]
    exact continuous_quotient_mk'.comp f.continuous_toFun
  have hcont : Continuous φ :=
    (QuotientGroup.isQuotientMap_mk (G := G) (N := N)).continuous_iff.2 hcomp
  exact
    { toMonoidHom := φ
      continuous_toFun := hcont }

/-- Continuous version of the quotient-group map.-/
def mapₜ
    (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal]
    (f : G →ₜ* H) (hNM : N ≤ M.comap f.toMonoidHom) :
    G ⧸ N →ₜ* H ⧸ M :=
  mapContinuousMonoidHom (G := G) (H := H) f (N := N) (M := M) hNM

/-- Continuous equivalence between quotients induced by a continuous multiplicative equivalence.-/
noncomputable def congrₜ
    (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal]
    (e : G ≃ₜ* H) (h : N.map e.toMulEquiv.toMonoidHom = M) :
    G ⧸ N ≃ₜ* H ⧸ M := by
  let eAlg : G ⧸ N ≃* H ⧸ M :=
    QuotientGroup.congr (G' := N) (H' := M) e.toMulEquiv h
  refine
    { toMulEquiv := eAlg
      continuous_toFun := ?_
      continuous_invFun := ?_ }
  · refine (QuotientGroup.isQuotientMap_mk N).continuous_iff.2 ?_
    change Continuous fun x : G => QuotientGroup.mk' M (e x)
    exact continuous_quotient_mk'.comp e.continuous_toFun
  · refine (QuotientGroup.isQuotientMap_mk M).continuous_iff.2 ?_
    have hsymm : M.map e.symm.toMulEquiv.toMonoidHom = N :=
      (Subgroup.map_symm_eq_iff_map_eq (K := N) (H := M) (e := e.toMulEquiv)).mpr h
    change Continuous fun y : H => QuotientGroup.mk' N (e.symm y)
    exact continuous_quotient_mk'.comp e.symm.continuous_toFun

/--
Continuous version of the quotient-group multiplicative equivalence induced by a surjective map.
The inverse is continuous by compact-to-Hausdorff automatic continuity, so the result is a
topological-group isomorphism when the source quotient is compact and the target quotient is
Hausdorff.-/
noncomputable def mapContinuousMulEquivOfSurjective
    (f : G →ₜ* H) {N : Subgroup G} {M : Subgroup H} [N.Normal] [M.Normal]
    [CompactSpace (G ⧸ N)] [T2Space (H ⧸ M)]
    (hf : Function.Surjective f) (hmap : N.map f.toMonoidHom = M)
    (hker : f.toMonoidHom.ker ≤ N) :
    G ⧸ N ≃ₜ* H ⧸ M := by
  have hNM : N ≤ M.comap f.toMonoidHom := by
    intro x hx
    change f x ∈ M
    rw [← hmap]
    exact ⟨x, hx, rfl⟩
  let φ := mapContinuousMonoidHom (G := G) (H := H) f (N := N) (M := M) hNM
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective M y
    rcases hf h with ⟨g, rfl⟩
    exact ⟨QuotientGroup.mk' N g, rfl⟩
  have hkerφ : φ.toMonoidHom.ker = ⊥ := by
    dsimp [φ, mapContinuousMonoidHom]
    exact map_ker_eq_bot_of_map_eq_of_ker_le (f := f.toMonoidHom) hNM hmap hker
  have hinj : Function.Injective φ :=
    (MonoidHom.ker_eq_bot_iff (f := φ.toMonoidHom)).1 hkerφ
  exact ContinuousMulEquiv.ofBijectiveCompactToT2
    φ.toMonoidHom φ.continuous_toFun ⟨hinj, hsurj⟩

/--
The lifted continuous quotient map evaluates on quotient classes by applying the underlying map
to representatives.
@isnad1 id=eq.1h5v.s8.1b60bbd1022f from=translated src=- shape=c277e5d5 vocab=f642dd9d
-/
@[simp] theorem liftₜ_apply_mk
    (N : Subgroup G) [N.Normal] (f : G →ₜ* H)
    (hN : N ≤ f.toMonoidHom.ker) (g : G) :
    liftₜ (G := G) (H := H) N f hN (QuotientGroup.mk' N g) = f g := by
  rfl

/-- The monoid homomorphism underlying `liftₜ` is the usual quotient lift.
@isnad1 id=eq.1h4v.s7.10028fd64cab from=translated src=- shape=039360ba vocab=14cafca5
-/
@[simp] theorem liftₜ_toMonoidHom
    (N : Subgroup G) [N.Normal] (f : G →ₜ* H)
    (hN : N ≤ f.toMonoidHom.ker) :
    (liftₜ (G := G) (H := H) N f hN).toMonoidHom =
      QuotientGroup.lift N f.toMonoidHom hN := by
  rfl

/-- The induced continuous monoid homomorphism sends a quotient class to the class of its image.
@isnad1 id=eq.1h6v.s9.dbfecc309966 from=translated src=- shape=c7fceb1c vocab=a614f7f1
-/
@[simp] theorem mapContinuousMonoidHom_apply_mk
    (f : G →ₜ* H) {N : Subgroup G} {M : Subgroup H} [N.Normal] [M.Normal]
    (hNM : N ≤ M.comap f.toMonoidHom) (g : G) :
    mapContinuousMonoidHom (G := G) (H := H) f (N := N) (M := M) hNM
        (QuotientGroup.mk' N g) =
      QuotientGroup.mk' M (f g) := by
  rfl

/-- The continuous quotient map sends the class of \(g\) to the class of \(f(g)\).
@isnad1 id=eq.1h6v.s9.64e22b0be1c3 from=translated src=- shape=5b5a2943 vocab=477e07de
-/
@[simp] theorem mapₜ_apply_mk
    (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal]
    (f : G →ₜ* H) (hNM : N ≤ M.comap f.toMonoidHom) (g : G) :
    mapₜ (G := G) (H := H) N M f hNM (QuotientGroup.mk' N g) =
      QuotientGroup.mk' M (f g) := by
  rfl

/-- The monoid homomorphism underlying `mapₜ` is the usual map between quotient groups.
@isnad1 id=eq.1h5v.s8.2a9133c74df8 from=translated src=- shape=13dbbf2b vocab=20adef8e
-/
@[simp] theorem mapₜ_toMonoidHom
    (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal]
    (f : G →ₜ* H) (hNM : N ≤ M.comap f.toMonoidHom) :
    (mapₜ (G := G) (H := H) N M f hNM).toMonoidHom =
      QuotientGroup.map (N := N) (M := M) (f := f.toMonoidHom) hNM := by
  rfl

/--
The continuous quotient congruence map evaluates on quotient classes by applying the underlying
map to representatives.
@isnad1 id=eq.1h6v.s9.c174c3c4e8e5 from=translated src=- shape=ade41a85 vocab=ea053bf0
-/
@[simp] theorem congrₜ_apply_mk
    (N : Subgroup G) (M : Subgroup H) [N.Normal] [M.Normal]
    (e : G ≃ₜ* H) (h : N.map e.toMulEquiv.toMonoidHom = M) (g : G) :
    congrₜ (G := G) (H := H) N M e h (QuotientGroup.mk' N g) =
      QuotientGroup.mk' M (e g) := by
  rfl

/--
The induced continuous multiplicative equivalence sends a quotient class to the class of its
image.
@isnad1 id=eq.3h6v.s9.a788ecfbc3c3 from=translated src=- shape=ab4f3e21 vocab=a2806797
-/
@[simp 900] theorem mapContinuousMulEquivOfSurjective_apply_mk
    (f : G →ₜ* H) {N : Subgroup G} {M : Subgroup H} [N.Normal] [M.Normal]
    [CompactSpace (G ⧸ N)] [T2Space (H ⧸ M)]
    (hf : Function.Surjective f) (hmap : N.map f.toMonoidHom = M)
    (hker : f.toMonoidHom.ker ≤ N) (g : G) :
    mapContinuousMulEquivOfSurjective (G := G) (H := H) f hf hmap hker
        (QuotientGroup.mk' N g) =
      QuotientGroup.mk' M (f g) := by
  rfl

end Topology

end QuotientGroup

namespace ContinuousMonoidHom

section RestrictPreimage

variable {G : Type u} {Q : Type v}
variable [TopologicalSpace G] [Group G] [IsTopologicalGroup G]
variable [TopologicalSpace Q] [Group Q] [IsTopologicalGroup Q]

/-- A continuous homomorphism restricts to the preimage of a subgroup of the target.-/
def restrictPreimage (f : G →ₜ* Q) (H : Subgroup Q) :
    (H.comap f.toMonoidHom) →ₜ* H := by
  refine
    { toMonoidHom :=
        { toFun := fun x => ⟨f x.1, x.2⟩
          map_one' := by
            ext
            simp only [_root_.ContinuousMonoidHom.coe_toMonoidHom, OneMemClass.coe_one, map_one]
          map_mul' := by
            intro x y
            ext
            exact f.map_mul x.1 y.1}
      continuous_toFun := by
        have hcont : Continuous (fun x : H.comap f.toMonoidHom => f x.1) :=
          f.continuous.comp continuous_subtype_val
        exact hcont.subtype_mk (by intro x; exact x.2) }

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] in
/-- The restriction to a subgroup preimage is surjective if the original map is surjective.
@isnad1 id=surjecti.1h4v.s9.deeed05e1863 from=translated src=- shape=3986b191 vocab=bc50210b
-/
theorem restrictPreimage_surjective (f : G →ₜ* Q) (hf : Function.Surjective f)
    (H : Subgroup Q) :
    Function.Surjective (restrictPreimage f H) := by
  intro y
  rcases hf y.1 with ⟨x, hx⟩
  refine ⟨⟨x, ?_⟩, ?_⟩
  · change f x ∈ H
    simp only [hx, SetLike.coe_mem]
  · exact Subtype.ext hx

omit [IsTopologicalGroup G] [IsTopologicalGroup Q] in
/-- The kernel of the restriction to a subgroup preimage is detected by the ambient map.
@isnad1 id=iff.0h5v.s9.44ede232f0f8 from=translated src=- shape=648163d3 vocab=2b8b0b9e
-/
theorem restrictPreimage_eq_one_iff {f : G →ₜ* Q} {H : Subgroup Q}
    {x : H.comap f.toMonoidHom} :
    restrictPreimage f H x = 1 ↔ f x.1 = 1 := by
  constructor
  · intro hx
    exact congrArg Subtype.val hx
  · intro hx
    exact Subtype.ext hx

/--
If the restricted map sends \(N\) onto \(M\) and its kernel is contained in \(N\), then the
induced quotient map is an isomorphism.-/
noncomputable def preimageSubgroupQuotientMulEquivOfSurjective
    (f : G →ₜ* Q) (hf : Function.Surjective f) (H : Subgroup Q)
    {N : Subgroup (H.comap f.toMonoidHom)} {M : Subgroup H} [N.Normal] [M.Normal]
    (hmap : N.map (restrictPreimage f H).toMonoidHom = M)
    (hker : (restrictPreimage f H).toMonoidHom.ker ≤ N) :
    (H.comap f.toMonoidHom) ⧸ N ≃* H ⧸ M :=
  QuotientGroup.mapMulEquivOfSurjective
    (restrictPreimage f H).toMonoidHom
    (restrictPreimage_surjective f hf H) hmap hker

end RestrictPreimage

end ContinuousMonoidHom

end ProCGroups
