/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/

/-
Blueprint unit: mapping-degree. Basics: nonconstancy bridges, fibers, `fiberMultSum`.
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.LocalMultiplicity.Multiplicity
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Identity
public import Tengoku

/-!
# Mapping-degree basics

* `RS.fiberMultSum F y` — the total multiplicity of `F` over `y` (a `finsum`; junk `0` for
  constant or non-holomorphic `F` by CC4's junk conventions) with its `Finset` bridge
  `fiberMultSum_eq_finset_sum` and junk lemma `fiberMultSum_of_forall_eq`.
* `RS.not_eventuallyConst` — globally nonconstant holomorphic maps on connected surfaces are
  nowhere locally constant (identity theorem); THE bridge to every local-multiplicity
  hypothesis. `RS.one_le_multiplicity_of_not_const` is its multiplicity corollary.
* Fibers of nonconstant holomorphic maps on compact surfaces are closed, discrete and finite:
  `RS.isDiscrete_fiber`, `RS.fiber_finite`.
* Re-exports (one-import convenience for downstream): `RS.isOpenMap_of_not_const'`,
  `RS.surjective_of_not_const'`; bounds `RS.multiplicity_le_fiberMultSum`,
  `RS.one_le_fiberMultSum`.

Surface perfectness (`(𝓝[≠] x).NeBot`) is NOT re-proved here: surfaces-and-charts already
provides the instance `RS.nhdsNE_neBot` for any `ChartedSpace ℂ` space.
-/

@[expose] public section

open Filter Set Function
open scoped ContDiff Manifold Topology

namespace RS

/-! ### `fiberMultSum` (minimal instances) -/

section FiberMultSumDef

variable {X Y : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]
  [TopologicalSpace Y] [ChartedSpace ℂ Y]

/-- Total multiplicity of `F` over `y` (the fiber-sum). Junk-free by convention: for
holomorphic nonconstant `F` on compact `X` the fiber is finite and every summand is `≥ 1`; for
constant `F` all summands are junk `0` (CC4), so the value is `0`. -/
noncomputable def fiberMultSum (F : X → Y) (y : Y) : ℕ :=
  ∑ᶠ x ∈ F ⁻¹' {y}, multiplicity F x

/--
@isnad1 id=eq.0h4v.s6.0928e3dce85d from=translated src=- shape=6f8cee8e vocab=49901202
-/
theorem fiberMultSum_def (F : X → Y) (y : Y) :
    fiberMultSum F y = ∑ᶠ x ∈ F ⁻¹' {y}, multiplicity F x := rfl

/--
@isnad1 id=eq.1h4v.s6.aeede54e585f from=translated src=- shape=d332e115 vocab=dc78dcc7
-/
theorem fiberMultSum_eq_finset_sum {F : X → Y} {y : Y} (hfin : (F ⁻¹' {y}).Finite) :
    fiberMultSum F y = ∑ x ∈ hfin.toFinset, multiplicity F x :=
  finsum_mem_eq_finite_toFinset_sum _ hfin

/-- Junk convention: constant maps have `fiberMultSum ≡ 0` (every summand is junk `0`).
@isnad1 id=eq.0h4v.s6.542a5f4f7a2e from=translated src=- shape=4f00caca vocab=75875719
-/
theorem fiberMultSum_of_forall_eq {y : Y} (c : Y) : fiberMultSum (fun _ : X ↦ c) y = 0 := by
  rw [fiberMultSum_def]
  apply finsum_mem_of_eqOn_zero
  intro x _
  exact multiplicity_of_eventuallyConst
    (eventuallyConst_nhds_iff.mpr (Eventually.of_forall fun _ ↦ rfl))

end FiberMultSumDef

/-! ### Nonconstancy bridges and fibers (standing surface hypotheses) -/

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type*} [TopologicalSpace Y] [T2Space Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]
variable {F : X → Y}

end RS
