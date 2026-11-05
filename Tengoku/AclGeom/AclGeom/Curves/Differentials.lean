/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.Specialty

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Weil differentials

A Weil differential of level `D` is a `k`-linear functional on the
adeles vanishing on `A(D) + F` — an element of the dual annihilator of
the bounded subspace, so of dimension `i(D)`. Multiplication by a field
element shifts the level by a principal divisor and is injective on
differentials, which bounds the degrees of the levels of a fixed
nonzero differential: `L(D − D₀)` injects into the level-`D₀`
differentials. Together with the join-splitting of adele spaces this
produces a maximal level — the divisor of the differential, whose class
is the canonical class.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P5).
-/

namespace AclGeom

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

section Multiplication

variable (k) in
/-- Pointwise multiplication by a field element on place-indexed
families.-/
noncomputable def adeleMulMap (f : F) :
    ((P : Place k F) → F) →ₗ[k] ((P : Place k F) → F) :=
  LinearMap.pi fun P ↦ (LinearMap.mulLeft k f).comp (LinearMap.proj P)

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
@[simp]
theorem adeleMulMap_apply (f : F) (α : (P : Place k F) → F)
    (P : Place k F) : adeleMulMap k f α P = f * α P := rfl

/-- Multiplication maps `A(D + div f)` into `A(D)`.-/
theorem adeleMulMap_mem_adeleSpace {f : F} (hf : f ≠ 0)
    {D : Divisor k F} {α : (P : Place k F) → F}
    (hα : α ∈ adeleSpace (D + divisorOf k f)) :
    adeleMulMap k f α ∈ adeleSpace D := by
  intro P
  rcases eq_or_ne (α P) 0 with h0 | h0
  · exact Or.inl (by rw [adeleMulMap_apply, h0, mul_zero])
  have h1 := (hα P).resolve_left h0
  rw [Finsupp.add_apply, divisorOf_apply hf] at h1
  refine Or.inr ?_
  rw [adeleMulMap_apply, P.ord_mul hf h0]
  omega

/-- Multiplication preserves the adeles: the new exceptional places are
poles of the multiplier.-/
theorem adeleMulMap_mem_adeleSubmodule (f : F)
    {α : (P : Place k F) → F} (hα : α ∈ adeleSubmodule k F) :
    adeleMulMap k f α ∈ adeleSubmodule k F := by
  rcases eq_or_ne f 0 with rfl | hf0
  · refine Set.Finite.subset Set.finite_empty fun P hP ↦ ?_
    simp only [Set.mem_ofPred_eq, adeleMulMap_apply, zero_mul] at hP
    exact absurd rfl hP.1
  refine Set.Finite.subset
    (hα.union (finite_setOf_one_lt_valuation hf0)) fun P hP ↦ ?_
  simp only [Set.mem_ofPred_eq, adeleMulMap_apply] at hP
  obtain ⟨hne, hlt⟩ := hP
  have hα0 : α P ≠ 0 := fun h ↦ hne (by rw [h, mul_zero])
  rw [P.ord_mul hf0 hα0] at hlt
  simp only [Set.mem_union, Set.mem_ofPred_eq]
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2⟩ := hcon
  have h3 := h1 hα0
  have h4 : 0 ≤ P.ord f := (P.ord_nonneg_iff hf0).2 h2
  omega

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- Multiplication fixes the diagonal.-/
theorem adeleMulMap_diagonal (f g : F) :
    adeleMulMap k f (adeleDiagonal k F g) = adeleDiagonal k F (f * g) :=
  rfl

/-- Multiplication as an endomorphism of the adele module.-/
noncomputable def adeleSMul (f : F) :
    ↥(adeleSubmodule k F) →ₗ[k] ↥(adeleSubmodule k F) :=
  LinearMap.codRestrict _
    ((adeleMulMap k f).comp (adeleSubmodule k F).subtype)
    fun α ↦ adeleMulMap_mem_adeleSubmodule f α.2

@[simp]
theorem adeleSMul_coe (f : F) (α : ↥(adeleSubmodule k F)) :
    (adeleSMul f α : (P : Place k F) → F) = adeleMulMap k f ↑α := rfl

theorem adeleSMul_add (f g : F) :
    adeleSMul (k := k) (F := F) (f + g) = adeleSMul f + adeleSMul g := by
  refine LinearMap.ext fun α ↦ Subtype.ext (funext fun P ↦ ?_)
  change (f + g) * ((α : (Q : Place k F) → F) P) =
    f * ((α : (Q : Place k F) → F) P) +
      g * ((α : (Q : Place k F) → F) P)
  ring

theorem adeleSMul_smul (c : k) (f : F) :
    adeleSMul (k := k) (F := F) (c • f) = c • adeleSMul f := by
  refine LinearMap.ext fun α ↦ Subtype.ext (funext fun P ↦ ?_)
  change (c • f) * ((α : (Q : Place k F) → F) P) =
    c • (f * ((α : (Q : Place k F) → F) P))
  rw [Algebra.smul_def, Algebra.smul_def]
  ring

end Multiplication

section Differentials

/-- **Weil differentials of level `D`**: functionals on the adeles
vanishing on `A(D) + F` — the dual annihilator of the bounded
subspace.-/
noncomputable def weilDifferentialsAt (D : Divisor k F) :
    Submodule k (Module.Dual k ↥(adeleSubmodule k F)) :=
  (boundedSubmodule D).dualAnnihilator

theorem mem_weilDifferentialsAt_iff {D : Divisor k F}
    {ω : Module.Dual k ↥(adeleSubmodule k F)} :
    ω ∈ weilDifferentialsAt D ↔
      ∀ α ∈ boundedSubmodule D, ω α = 0 :=
  Submodule.mem_dualAnnihilator ω

/-- Levels are antitone: killing a larger space is harder.-/
theorem weilDifferentialsAt_antitone {D E : Divisor k F} (h : D ≤ E) :
    weilDifferentialsAt (E : Divisor k F) ≤ weilDifferentialsAt D := by
  intro ω hω
  rw [mem_weilDifferentialsAt_iff] at hω ⊢
  intro α hα
  exact hω α (boundedSubmodule_mono h hα)

/-- **The level shift**: precomposing a level-`D` differential with
multiplication by `f` yields a level-`(D + div f)` differential.-/
theorem comp_adeleSMul_mem_weilDifferentialsAt {f : F} (hf : f ≠ 0)
    {D : Divisor k F} {ω : Module.Dual k ↥(adeleSubmodule k F)}
    (hω : ω ∈ weilDifferentialsAt D) :
    ω ∘ₗ adeleSMul f ∈ weilDifferentialsAt (D + divisorOf k f) := by
  rw [mem_weilDifferentialsAt_iff] at hω ⊢
  intro α hα
  rw [LinearMap.comp_apply]
  refine hω _ ?_
  rw [mem_boundedSubmodule_iff] at hα ⊢
  obtain ⟨x, hx, y, ⟨g, rfl⟩, hxy⟩ := Submodule.mem_sup.1 hα
  have hcoe : (adeleSMul f α : (P : Place k F) → F) =
      adeleMulMap k f x + adeleDiagonal k F (f * g) := by
    rw [adeleSMul_coe, ← hxy, map_add, adeleMulMap_diagonal]
  rw [hcoe]
  exact Submodule.add_mem _
    (Submodule.mem_sup_left (adeleMulMap_mem_adeleSpace hf hx))
    (Submodule.mem_sup_right ⟨f * g, rfl⟩)

end Differentials

section CanonicalDivisor

/-- **The multiplication pairing**: `f ↦ ω ∘ (mult by f)`, as a linear
map from `L(E)` into the level-`D` differentials, for `D + E ≤ W`.-/
noncomputable def differentialPairing {W D E : Divisor k F}
    {ω : Module.Dual k ↥(adeleSubmodule k F)}
    (hω : ω ∈ weilDifferentialsAt W) (hDE : D + E ≤ W) :
    ↥(RiemannSpace E) →ₗ[k] ↥(weilDifferentialsAt D) where
  toFun f := ⟨ω ∘ₗ adeleSMul (f : F), by
    rcases eq_or_ne (f : F) 0 with h0 | h0
    · rw [h0]
      have hz : adeleSMul (k := k) (F := F) (0 : F) = 0 := by
        refine LinearMap.ext fun α ↦ Subtype.ext (funext fun P ↦ ?_)
        change (0 : F) * ((α : (Q : Place k F) → F) P) = 0
        rw [zero_mul]
      rw [hz, LinearMap.comp_zero]
      exact zero_mem _
    · have h1 := comp_adeleSMul_mem_weilDifferentialsAt h0 hω
      refine weilDifferentialsAt_antitone ?_ h1
      intro P
      have h2 := (mem_riemannSpace_iff.1 f.2).resolve_left h0 P
      have h3 := hDE P
      rw [Finsupp.add_apply] at h3
      rw [Finsupp.add_apply, divisorOf_apply h0]
      omega⟩
  map_add' f g := by
    apply Subtype.ext
    change ω ∘ₗ adeleSMul ((f : F) + (g : F)) =
      ω ∘ₗ adeleSMul (f : F) + ω ∘ₗ adeleSMul (g : F)
    rw [adeleSMul_add, LinearMap.comp_add]
  map_smul' c f := by
    apply Subtype.ext
    change ω ∘ₗ adeleSMul (c • (f : F)) = c • (ω ∘ₗ adeleSMul (f : F))
    rw [adeleSMul_smul, LinearMap.comp_smul]

@[simp]
theorem differentialPairing_coe {W D E : Divisor k F}
    {ω : Module.Dual k ↥(adeleSubmodule k F)}
    (hω : ω ∈ weilDifferentialsAt W) (hDE : D + E ≤ W)
    (f : ↥(RiemannSpace E)) :
    (differentialPairing hω hDE f :
      Module.Dual k ↥(adeleSubmodule k F)) = ω ∘ₗ adeleSMul (f : F) :=
  rfl

end CanonicalDivisor

end

end AclGeom
