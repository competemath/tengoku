/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Cech.Window
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Surface.Identity
public import Tengoku

/-!
# Window dimension counts (CC8, D7, proof plan §6.8)

Unit: cech-cohomology (`docs/design/cech-cohomology.md` §4.6, §6.8).

* `evalAt_eq_zero_iff` [Compat]: chart-transported analogue of mathlib's
  `tendsto_zero_iff_meromorphicOrderAt_pos`, filed as a request to meromorphic-and-divisors
  (`docs/requests/meromorphic-and-divisors.md`) but not upstreamed — proved here from exported
  chart-transport lemmas only.
* `leadCoeff_eq_zero_iff`: the one-step leading-coefficient functional detects the exact order.
* `finrank_windowAt`/`finrank_window`: the `θ`-basis dimension counts (design §6.8), via an
  explicit one-step splitting `WindowAt p d d' ≃ₗ WindowAt p d (d'-1) × ℂ` and induction on
  `(d' - d).toNat` (no explicit basis/independence argument needed).
-/

@[expose] public section

open scoped ContDiff Manifold Topology
open Set TopologicalSpace RS.Cech Filter

namespace RS.Cech

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Compat: chart-transported vanishing criterion for `evalAt` -/

/-! ### `leadCoeff` detects the exact order -/

/-! ### The one-step splitting `WindowAt p d d' ≃ₗ WindowAt p d (d'-1) × ℂ` -/

variable (p : X)

/-- The distinguished representative of `θ_{p,-d'}` as an `ordGe p (-d')` element. -/
private noncomputable def tailGermElt (d' : ℤ) : ordGe p (-d') :=
  ⟨tailGerm p (-d'), by rw [mem_ordGe_iff, ord_tailGerm_self]⟩

/-! ### The dimension count, by induction on `(d' - d).toNat` -/

/-! ### `finrank_window`: the global (Pi-of-windows) dimension count -/

/-- Registered explicitly (same reason as `Jacobian/Cech/Cochains.lean`'s `Z1`/`H1Cover`
instances): `Window D D' := ∀ q, WindowAt (q:X) (D q) (D' q)` is a Pi type, so its
`Module ℂ`/`Module.Free ℂ` structure needs these per-factor instances solved as a *dependent*
Pi-instance goal — the newer toolchain's `synthInstance` no longer reliably re-derives that from
`WindowAt`'s own (quotient) definition on demand. Supplying them once, directly, for the generic
`WindowAt p d d'` lets every downstream Pi-dependent lookup match verbatim instead of
re-deriving them. -/
noncomputable instance instAddCommGroupWindowAt (p : X) (d d' : ℤ) :
    AddCommGroup (WindowAt p d d') := inferInstance

noncomputable instance instModuleWindowAt (p : X) (d d' : ℤ) : Module ℂ (WindowAt p d d') :=
  inferInstance

variable [T2Space X] [CompactSpace X]

end RS.Cech
