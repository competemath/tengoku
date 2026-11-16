/-
Copyright (c) 2025 Nailin Guan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nailin Guan, Yongle Hu
-/
module

public import Tengoku.ZanelloLc.FormalDeps.Port.Mathlib.RingTheory.CohenMacaulay.Basic
public import Tengoku.ZanelloLc.FormalDeps.Port.Mathlib.RingTheory.RegularLocalRing.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Maximal Cohen Macaulay Module

The definition of maximal Cohen Macaulay module.

# Main definition and results

* `isCohenMacaulayLocalRing_of_isRegularLocalRing` : regular local ring is Cohen Macaulay

* `free_of_isMaximalCohenMacaulay_of_isRegularLocalRing` : maximal Cohen Macaulay module over
  regular local ring is free.

-/

@[expose] public section
namespace Tengoku.ZanelloLc end Tengoku.ZanelloLc open Tengoku.ZanelloLc 
universe v' v u' u

variable {R : Type u} [CommRing R]

open IsLocalRing

/-- A `R`-module is maximal Cohen Macaulay if `IsLocalRing.depth M = ringKrullDim R`.-/
class ModuleCat.IsMaximalCohenMacaulay [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) : Prop where
  depth_eq_dim : IsLocalRing.depth M = ringKrullDim R

lemma _root_.Tengoku.ZanelloLc.isMaximalCohenMacaulay_def [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) : M.IsMaximalCohenMacaulay ↔ IsLocalRing.depth M = ringKrullDim R :=
  ⟨fun ⟨h⟩ ↦ h, fun h ↦ ⟨h⟩⟩

/-
--need subsingleton imply depth eq top
instance [IsNoetherianRing R] [IsLocalRing R] [Small.{v} R]
    (M : ModuleCat.{v} R) [M.IsMaximalCohenMacaulay] : Nontrivial M := sorry
-/

lemma _root_.Tengoku.ZanelloLc.isField_of_isRegularLocalRing_of_dimension_zero [IsRegularLocalRing R]
    (h : ringKrullDim R = 0) : IsField R := by
  rw [IsLocalRing.isField_iff_maximalIdeal_eq, ← Submodule.spanRank_eq_zero_iff_eq_bot]
  have := (isRegularLocalRing_iff R).mp ‹_›
  simp only [h, Nat.cast_eq_zero] at this
  have fg : (maximalIdeal R).FG := (isNoetherianRing_iff_ideal_fg R).mp inferInstance _
  simpa [Submodule.fg_iff_spanRank_eq_spanFinrank.mpr fg] using this

local instance (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] (x : R) :
    Module.Finite (R ⧸ Ideal.span {x}) (QuotSMulTop x M) := by
  let f : M →ₛₗ[Ideal.Quotient.mk (Ideal.span {x})] (QuotSMulTop x M) := {
    __ := Submodule.mkQ _
    map_smul' r m := rfl }
  exact Module.Finite.of_surjective f (Submodule.mkQ_surjective _)

open Pointwise in
lemma _root_.Tengoku.ZanelloLc.free_of_quotSMulTop_free [IsLocalRing R] [IsNoetherianRing R] (M : Type*) [AddCommGroup M]
    [Module R M] [Module.Finite R M] {x : R} (mem : x ∈ maximalIdeal R) (reg : IsSMulRegular M x)
    (free : Module.Free (R ⧸ Ideal.span {x}) (QuotSMulTop x M)) : Module.Free R M := by
  let I := Module.Free.ChooseBasisIndex (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let fin : Fintype I := Module.Free.ChooseBasisIndex.fintype _ _
  have : Module.Finite R (I →₀ R) := by simp [Fintype.finite fin]
  let b := Module.Free.chooseBasis (R ⧸ Ideal.span {x}) (QuotSMulTop x M)
  let b' : QuotSMulTop x M ≃ₗ[R] I →₀ R ⧸ Ideal.span {x} := {
    __ := b.1
    map_smul' r m := by simp}
  let f := b'.symm.toLinearMap.comp (Finsupp.mapRange.linearMap (Submodule.mkQ (Ideal.span {x})))
  rcases Module.projective_lifting_property (Submodule.mkQ (x • (⊤ : Submodule R M))) f
    (Submodule.mkQ_surjective _) with ⟨g, hg⟩
  have surjf : Function.Surjective f := by
    dsimp only [f, LinearMap.coe_comp, Function.comp_apply]
    apply b'.symm.surjective.comp
    intro y
    obtain ⟨z, hz⟩ := Finsupp.mapRange_surjective _ rfl
      (Submodule.mkQ_surjective (Ideal.span {x})) y
    use z
    ext i
    exact DFunLike.congr_fun hz i
  have lejac : Ideal.span {x} ≤ (⊥ :Ideal R).jacobson :=
    le_trans ((Ideal.span_singleton_le_iff_mem (maximalIdeal R)).mpr mem)
    (IsLocalRing.maximalIdeal_le_jacobson _)
  have surjg : Function.Surjective g := by
    rw [← LinearMap.range_eq_top, ← top_le_iff]
    apply Submodule.le_of_le_smul_of_le_jacobson_bot (Module.finite_def.mp ‹_›) lejac
    rw [top_le_iff, sup_comm, ← Submodule.map_mkQ_eq_top, ← LinearMap.range_comp,
      Submodule.ideal_span_singleton_smul x ⊤, hg]
    exact LinearMap.range_eq_top_of_surjective f surjf
  have kerf : LinearMap.ker f = x • (⊤ : Submodule R (I →₀ R)) := by
    simp only [LinearEquiv.ker_comp, f]
    ext y
    simp only [Finsupp.ker_mapRange, Submodule.ker_mkQ, Finsupp.mem_submodule_iff]
    refine ⟨fun h ↦ ?_, fun h i ↦ ?_⟩
    · simp only [Ideal.mem_span_singleton', mul_comm] at h
      rw [← Finsupp.univ_sum_single y]
      refine Submodule.sum_mem _ (fun i _ ↦ ?_)
      rcases h i with ⟨z, hz⟩
      simpa only [← hz, ← Finsupp.smul_single'] using
        Submodule.smul_mem_pointwise_smul (Finsupp.single i z) x ⊤ trivial
    · rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp h with ⟨z, _, eq⟩
      simpa [← eq] using Ideal.IsTwoSided.mul_mem_of_left (z i) (Ideal.mem_span_singleton_self x)
  have injg : Function.Injective g := by
    rw [← LinearMap.ker_eq_bot]
    have fg : (LinearMap.ker g).FG := IsNoetherian.noetherian (LinearMap.ker g)
    apply Submodule.eq_bot_of_le_smul_of_le_jacobson_bot (Ideal.span {x}) _ fg _ lejac
    rw [Submodule.ideal_span_singleton_smul]
    intro y hy
    have : y ∈ x • (⊤ : Submodule R (I →₀ R)) := by simp [← kerf, ← hg, LinearMap.mem_ker.mp hy]
    rcases (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp this with ⟨z, _, hz⟩
    simp only [← hz, LinearMap.mem_ker, map_smul] at hy
    have := LinearMap.mem_ker.mpr (IsSMulRegular.right_eq_zero_of_smul reg hy)
    simpa [hz] using Submodule.smul_mem_pointwise_smul z x _ this
  exact Module.Free.of_equiv (LinearEquiv.ofBijective g ⟨injg, surjg⟩)

end
-- Tengoku: root names of this library moved to Tengoku.ZanelloLc so they do not collide with other libraries (generated)
