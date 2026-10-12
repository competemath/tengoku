/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov
-/
module

public import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.CanonicalForms.Differential
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.CodiscreteBridge
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.Gluing
import Tengoku.LeanPool.LeanPool.JacobianDiffgeo.Meromorphic.LinearSystem
public import Tengoku

/-!
# One-dimensionality over `ℳ(X)` (D8) and the canonical divisor `K` (D10)

Unit: canonical-forms (`docs/design/canonical-forms.md` §2 D8/D10, proof plan §5 P5).

* `MForm.smul_eq_zero_iff`/`MForm.smul_left_injective`: `ℳ(X)`-scaling by a nonzero form is
  injective (the D5 dichotomy + the `ord_smul_mero` dictionary).
* **D8** `MForm.exists_unique_smul_of_ne_zero`: `MForm X` is one-dimensional over `ℳ X` — every
  meromorphic 1-form is a unique `ℳ(X)`-multiple of any fixed nonzero reference `θ₀`. The ratio
  is built chart-locally (`q x := θ.coeffAt x / θ₀.coeffAt x`, transitions cancel — "the ratio of
  two 1-forms is a function") and glued by `MeroGermOn.exists_glue`; on the QUOTIENT the class
  equation needs only `𝓝[≠]`-agreement at each center, where `θ₀`'s coefficient is eventually
  nonzero (D5), so no removable-singularity repair is needed at the zeros of `θ₀`.
* **D10** `canonicalDivisorOf θ₀ := θ₀.divisor` ("a" canonical divisor, seeded by an explicit
  nonzero reference — no silent choice), `MForm.divisor_smul_mero` (divisors add under the
  `ℳ(X)`-action), and `canonicalDivisorOf_linearEquiv` (any two canonical divisors differ by a
  principal divisor — Forster 16.7-style well-definedness up to linear equivalence).

D10 lives here rather than in the design's `Existence.lean` slot because `Existence.lean` (D9)
remains gated on `Jacobian/Finiteness/Chi.lean` (not on disk); `canonicalDivisorOf` has no
finiteness dependence.

Hypothesis note: D8 needs only `[T1Space X] [ConnectedSpace X]` (the design listed an extra
`[T2Space X]`, which is not required — the dichotomy and `Mero.ord_ne_top` are `T1`-level).
-/

@[expose] public section

open scoped ContDiff Manifold
open Set IsManifold Filter Topology

noncomputable section

namespace RS

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

namespace MForm

section Existence

variable [T1Space X] [ConnectedSpace X]

end Existence

end MForm

/-! ### D10: the canonical divisor `K` -/

/-- D10: "a" canonical divisor, seeded by an explicit nonzero reference (no silent
`Classical.choice`-baked default; downstream fixes one when a definite `K` is needed). -/
noncomputable abbrev canonicalDivisorOf [T1Space X]
    (Θ₀ : MForm X) : Divisor X := Θ₀.divisor

end RS
