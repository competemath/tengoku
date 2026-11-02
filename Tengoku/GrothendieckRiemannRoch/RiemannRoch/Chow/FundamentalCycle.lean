/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.GrothendieckRiemannRoch.RiemannRoch.Chow.GradedCycles
import Tengoku.Seed.AlgebraicGeometry.Noetherian
import Tengoku.Seed.RingTheory.HopkinsLevitzki

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fundamental cycles of Noetherian schemes

The fundamental cycle of a Noetherian scheme is supported at the generic points of its
irreducible components.  Its coefficient at a generic point is the length of the local ring at
that point as a module over itself.  The local ring is zero-dimensional Noetherian, hence
Artinian, so this length is finite.

Unlike the finite-point carrier in `FiniteIntersection`, this construction applies to schemes of
arbitrary dimension.  It is therefore the cycle-theoretic carrier needed for positive-dimensional
scheme-theoretic intersections.
-/

noncomputable section

open AlgebraicGeometry Order TopologicalSpace
open scoped BigOperators

universe u

namespace AlgebraicGeometry.Chow

variable {Z : Scheme.{u}} [IsNoetherian Z]

/-- A generic point of an irreducible component is maximal in the specialization order.-/
theorem isMax_of_mem_genericPoints {z : Z} (hz : z ∈ genericPoints Z) : IsMax z := by
  intro y hzy
  rw [Scheme.le_iff_specializes] at hzy ⊢
  apply specializes_iff_closure_subset.mpr
  exact hz.2 isIrreducible_singleton.closure hzy.closure_subset

/-- A maximal point of a Noetherian scheme is the generic point of an irreducible component.-/
theorem mem_genericPoints_of_isMax {z : Z} (hz : IsMax z) : z ∈ genericPoints Z := by
  refine ⟨isIrreducible_singleton.closure, ?_⟩
  intro s hs hzs
  let η := hs.closure.genericPoint
  have hη : IsGenericPoint η (closure s) :=
    hs.closure.isGenericPoint_genericPoint isClosed_closure
  have hzmem : z ∈ closure s :=
    subset_closure (hzs (subset_closure (Set.mem_singleton z)))
  have hzη : z ≤ η := Scheme.le_iff_specializes.mpr (hη.specializes hzmem)
  have hηz : η ≤ z := hz hzη
  have hclosure : closure {η} ⊆ closure {z} :=
    (Scheme.le_iff_specializes.mp hηz).closure_subset
  rw [isGenericPoint_def] at hη
  exact subset_closure.trans (hη ▸ hclosure)

/-- Generic points of irreducible components have codimension zero.-/
theorem coheight_eq_zero_of_mem_genericPoints {z : Z} (hz : z ∈ genericPoints Z) :
    coheight z = 0 :=
  coheight_eq_zero.mpr (isMax_of_mem_genericPoints hz)

/-- On a Noetherian scheme, codimension-zero points are exactly component generic points.-/
theorem mem_genericPoints_iff_coheight_eq_zero {z : Z} :
    z ∈ genericPoints Z ↔ coheight z = 0 :=
  ⟨coheight_eq_zero_of_mem_genericPoints,
    fun hz ↦ mem_genericPoints_of_isMax (coheight_eq_zero.mp hz)⟩

/-- The length of the local ring at a point, regarded as a module over itself.-/
noncomputable def selfLocalLength (z : Z) : ℕ∞ :=
  Module.length ↑(Z.presheaf.stalk z) ↑(Z.presheaf.stalk z)

/-- The natural-number multiplicity of a component in the fundamental cycle.-/
noncomputable def genericMultiplicity (z : Z) : ℕ :=
  (selfLocalLength z).toNat

/-- The fundamental cycle of a Noetherian scheme.-/
noncomputable def fundamentalCycle (Z : Scheme.{u}) [IsNoetherian Z] :
    AlgebraicCycle Z ℤ := by
  classical
  let hG : (genericPoints Z).Finite :=
    genericPoints.finite finite_irreducibleComponents_of_isNoetherian
  exact ∑ z ∈ hG.toFinset,
    Function.locallyFinsuppWithin.single z (genericMultiplicity z : ℤ)

/-- The coefficient of the fundamental cycle at a generic point is its local length.-/
@[simp]
theorem fundamentalCycle_apply_of_mem_genericPoints {z : Z} (hz : z ∈ genericPoints Z) :
    fundamentalCycle Z z = (genericMultiplicity z : ℤ) := by
  classical
  simp [fundamentalCycle, Function.locallyFinsuppWithin.single_apply, hz]

end AlgebraicGeometry.Chow
