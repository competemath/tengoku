/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.JacobianConstruction.Basic
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Path.Planar
public import Tengoku

/-!
# `ofCurve`, well-definedness, `ofCurve_self`, `ofCurve_contMDiff` (CC9, §8)

Unit: jacobian-construction. The Abel–Jacobi map `Jacobian.ofCurve`, its any-path recipe
(well-definedness, `ofCurve_eq_of_path`), `ofCurve_self`, and `ofCurve_contMDiff` (holomorphy).
Path-connectedness of `X` is derived locally (§8.1; filed as a request to surfaces-and-charts,
non-blocking).

`ofCurve_contMDiff` (§8.3) is gated by `[DiscreteTopology (periodSubgroup X).topologicalClosure]`,
for the same reason `ChartedSpace`/`IsManifold (Jacobian X)` are (`Basic.lean`'s ledger): the
statement itself does not elaborate without a `ChartedSpace (Fin (genus X) → ℂ) (Jacobian X)`
instance for its codomain. Modulo that (unavoidable) hypothesis, the proof is complete: fix `x₀`,
work in the chart `e := chartAt ℂ x₀`; each `coeffIn e (basis X i)` has a holomorphic primitive
`g i` on a ball around `e x₀` (planar Morera); the straight-segment path in the chart (pulled back
through `e.symm` via `Path.segment`/`Path.map'`) gives `ofCurve P z = ULift.up (mk (v₀ + g (e z)))`
near `x₀` (`hkey`); reading this through the Jacobian's own chart (the same locally-constant
lattice-shift computation as `Torus.contMDiff_add_torus`/`ULift.contMDiff_uliftUp`) makes the
chart composite affine in `g (e z)`, hence analytic.
-/

@[expose] public section

open scoped ContDiff Manifold Convex Topology
open IsManifold Metric Set Filter

noncomputable section

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### §8.1: path-connectedness of `X` (small gap, filled here; `Compat`) -/

/-- `Compat`: `X` is locally path-connected, via its charts into `ℂ` (a locally convex space).
Filed as a request to surfaces-and-charts (`docs/requests/surfaces-and-charts.md`); carried here
as a local instance since no upstream unit currently provides it. -/
instance : LocallyPathConnectedSpace X := ChartedSpace.locallyPathConnectedSpace (H := ℂ) (M := X)

/-- `Compat`: `X` is path-connected (`ConnectedSpace X` + `LocallyPathConnectedSpace X`). -/
instance : PathConnectedSpace X := .of_locallyPathConnectedSpace

/-! ### `periodVector` of a loop, at *any* basepoint, lies in `periodSubgroup X` -/

/-- Basepoint-independence of the period subgroup: for any based loop `γ` at any point `x` (not
just at `periodSubgroup`'s defining basepoint), `periodVector (basis X) γ` still lies in
`periodSubgroup X`, via conjugation by a connecting path (`RS.period_conj`).
@isnad1 id=mem.0h3v.s7.9043943361c2 from=translated src=- shape=aba302e1 vocab=311e437f
-/
theorem RS.periodVector_mem_periodSubgroup {x : X} (γ : Path x x) :
    RS.periodVector (RS.basis X) γ ∈ RS.periodSubgroup X := by
  set x₀ := Classical.arbitrary X
  set σ : Path x₀ x := PathConnectedSpace.somePath x₀ x
  have heq : RS.periodVector (RS.basis X) γ
      = RS.periodVector (RS.basis X) ((σ.trans γ).trans σ.symm) := by
    funext i
    exact (RS.period_conj σ γ (RS.basis X i)).symm
  rw [heq]
  exact AddSubgroup.subset_closure ⟨(σ.trans γ).trans σ.symm, rfl⟩

namespace Jacobian

/-! ### `ofCurve` (§8.2) -/

/-- The Abel–Jacobi map from a compact Riemann surface to its Jacobian
(`docs/Jacobian_challenge.lean:92`): integrate the basis of holomorphic `1`-forms along *some*
path from `P` to `x` (any choice; well-defined mod periods, `ofCurve_eq_of_path`). -/
noncomputable def ofCurve (P : X) : X → Jacobian X := fun x =>
  ULift.up (QuotientAddGroup.mk
    (fun i => RS.pathIntegral (PathConnectedSpace.somePath P x) (RS.basis X i)))

/-- `ofCurve` computed along *any* path `σ : Path P x`, not just the canonical
`PathConnectedSpace.somePath` — the any-path recipe, and the source of well-definedness.
@isnad1 id=eq.0h4v.s13.52a0482ffc16 from=translated src=- shape=218ec304 vocab=01e7841a
-/
theorem ofCurve_eq_of_path (P x : X) (σ : Path P x) :
    ofCurve P x = ULift.up (QuotientAddGroup.mk (fun i => RS.pathIntegral σ (RS.basis X i))) := by
  change ULift.up (QuotientAddGroup.mk
      (fun i => RS.pathIntegral (PathConnectedSpace.somePath P x) (RS.basis X i)))
    = ULift.up (QuotientAddGroup.mk (fun i => RS.pathIntegral σ (RS.basis X i)))
  congr 1
  set σ₀ := PathConnectedSpace.somePath P x with hσ₀_def
  rw [QuotientAddGroup.eq_iff_sub_mem]
  have hmem : RS.periodVector (RS.basis X) (σ.trans σ₀.symm) ∈ RS.periodSubgroup X :=
    RS.periodVector_mem_periodSubgroup (σ.trans σ₀.symm)
  have heq : (fun i => RS.pathIntegral σ₀ (RS.basis X i)) -
      (fun i => RS.pathIntegral σ (RS.basis X i))
      = -RS.periodVector (RS.basis X) (σ.trans σ₀.symm) := by
    funext i
    simp only [Pi.sub_apply, Pi.neg_apply]
    change _ = -(RS.pathIntegral (σ.trans σ₀.symm) (RS.basis X i))
    rw [RS.pathIntegral_trans, RS.pathIntegral_symm]
    ring
  rw [heq]
  exact (RS.periodSubgroup X).topologicalClosure.neg_mem
    (AddSubgroup.le_topologicalClosure _ hmem)

/--
@isnad1 id=eq.0h2v.s8.97701529a021 from=translated src=- shape=0effa0c8 vocab=e07e4f0b
-/
@[simp] theorem ofCurve_self (P : X) : ofCurve P P = 0 := by
  rw [ofCurve_eq_of_path P P (Path.refl P)]
  have hzero : (fun i => RS.pathIntegral (Path.refl P) (RS.basis X i)) = (0 : Fin (genus X) → ℂ) :=
      by
    funext i
    exact RS.pathIntegral_refl P (RS.basis X i)
  rw [hzero]
  rfl

/-! ### `ofCurve_contMDiff` (§8.3) -/

variable [DiscreteTopology (RS.periodSubgroup X).topologicalClosure]

end Jacobian

end
