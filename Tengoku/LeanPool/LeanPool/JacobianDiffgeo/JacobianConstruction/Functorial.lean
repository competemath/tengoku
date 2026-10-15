/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.JacobianConstruction.Basic
public import Tengoku

/-!
# The `→ₜ+` functoriality substrate, wrapped through the `ULift` shell (§9.4)

Unit: jacobian-construction. Wraps `Torus.inducedHom`/`Torus.contMDiff_inducedHom` (the abstract
`V ⧸ L → V' ⧸ L'` substrate, §9.2–§9.3) through the `ULift` shell to produce a `→ₜ+` map
`Jacobian X →ₜ+ Jacobian Y` from a `ℂ`-linear map `T` between the ambient period spaces
respecting the period subgroups.

**Out of scope for this unit** (flagged, not silently dropped, per design §9.4/R4): constructing
the *specific* `T` for a given holomorphic `f : X → Y` (via pullback-of-forms), and the actual
`Jacobian.pushforward`/`Jacobian.pullback` challenge definitions built from a real `f`. No
blueprint unit currently owns "pullback of holomorphic `1`-forms along a holomorphic map" — see
this unit's final report for the flag to the orchestrator.
-/

@[expose] public section

open scoped ContDiff Manifold

universe u

noncomputable section

namespace RS

/-! ### `ULift` as a `→ₜ+` equivalence (generic transport toolkit) -/

variable {G : Type*} [AddCommGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]

/-- `ULift.up`, bundled as a continuous additive homomorphism. -/
def uliftUpHom : G →ₜ+ ULift.{u} G :=
  { (AddEquiv.ulift (α := G)).symm.toAddMonoidHom with
    continuous_toFun := (Homeomorph.ulift (X := G)).symm.continuous }

/-- `ULift.down`, bundled as a continuous additive homomorphism. -/
def uliftDownHom : ULift.{u} G →ₜ+ G :=
  { (AddEquiv.ulift (α := G)).toAddMonoidHom with
    continuous_toFun := (Homeomorph.ulift (X := G)).continuous }

omit [IsTopologicalAddGroup G] in
/--
@isnad1 id=eq.0h2v.s6.3780e3b97556 from=translated src=- shape=eaf4f17a vocab=34c123ba
-/
@[simp] theorem uliftUpHom_apply (x : G) : uliftUpHom.{u} x = ULift.up x := rfl

omit [IsTopologicalAddGroup G] in
/--
@isnad1 id=eq.0h2v.s6.1e3bf7a34caa from=translated src=- shape=f7ae47d7 vocab=d44d96cd
-/
@[simp] theorem uliftDownHom_apply (x : ULift.{u} G) : uliftDownHom x = x.down := rfl

end RS

variable {X : Type u} [TopologicalSpace X] [T2Space X] [CompactSpace X] [ConnectedSpace X]
  [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]
variable {Y : Type u} [TopologicalSpace Y] [T2Space Y] [CompactSpace Y] [ConnectedSpace Y]
  [ChartedSpace ℂ Y] [IsManifold 𝓘(ℂ) ω Y]

namespace Jacobian

/-- A `ℂ`-linear map on the ambient period spaces, respecting the period subgroups (at the raw,
undiscretized `periodSubgroup` level — the natural hypothesis to check for a map arising from a
holomorphic `f : X → Y`, e.g. via naturality of periods under post-composition), induces the
functoriality substrate `Jacobian X →ₜ+ Jacobian Y`. The *closure*-level hypothesis
`Torus.inducedHom` needs is derived from this one via minimality of the topological closure
(`AddSubgroup.topologicalClosure_minimal`), since `(periodSubgroup Y).topologicalClosure` is
already closed and `T` is continuous (finite-dimensional). -/
noncomputable def inducedHom {T : (Fin (genus X) → ℂ) →ₗ[ℂ] (Fin (genus Y) → ℂ)}
    (hT : RS.periodSubgroup X ≤ (RS.periodSubgroup Y).topologicalClosure.comap T.toAddMonoidHom) :
    Jacobian X →ₜ+ Jacobian Y :=
  RS.uliftUpHom.comp
    ((RS.inducedHom (RS.periodSubgroup X).topologicalClosure
        (RS.periodSubgroup Y).topologicalClosure T
        (AddSubgroup.topologicalClosure_minimal (RS.periodSubgroup X) hT
          (((RS.periodSubgroup Y).isClosed_topologicalClosure).preimage
            T.continuous_of_finiteDimensional))).comp
      RS.uliftDownHom)

end Jacobian
