/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.DegreeBound
import Tengoku.Seed.Data.Int.ConditionallyCompleteOrder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Riemann's inequality and the genus

The **defect** of a divisor is `deg D + 1 − ℓ(D)`. It is monotone in the
divisor (the subtraction bound) and invariant under adding principal
divisors (degree-zero-ness of `div z` plus the multiplication gauge on
`L`-spaces). Riemann's bound (`exists_forall_defect_le`) caps it
uniformly: every divisor is dominated, up to a principal divisor, by a
multiple of the pole divisor `A = (x)_∞` of a fixed transcendental `x`,
and on multiples of `A` the counting family pins the defect below
`deg C + 1 − [F : k(x)]`. The **genus** is the supremum of the defect,
and Riemann's inequality `ℓ(D) ≥ deg D + 1 − g` holds by construction.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P3).
-/

namespace AclGeom

open IntermediateField

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The **defect** of a divisor: `deg D + 1 − ℓ(D)`. Riemann's bound
caps it uniformly; its supremum is the genus.-/
noncomputable def Divisor.defect (D : Divisor k F) : ℤ :=
  D.deg + 1 - Module.finrank k (RiemannSpace D)

variable (k F) in
/-- The **genus** of the function field: the supremum of the defect
`deg D + 1 − ℓ(D)` over all divisors. Well-defined by Riemann's bound,
realized as `0` at `D = 0`, hence nonnegative.-/
noncomputable def genus : ℤ :=
  sSup (Set.range fun D : Divisor k F ↦ D.defect)

omit [IsAlgClosed k] [IsFunctionFieldOneVar k F] in
/-- A one-dimensional extension is trivial: an intermediate field over
which the ambient field has dimension one is everything.
@isnad1 id=eq.1h3v.s8.a7828535d23c from=translated src=- shape=0b00b7a2 vocab=be092eb0
-/
theorem intermediateField_eq_top_of_finrank_eq_one
    {K : IntermediateField k F} [FiniteDimensional (↥K) F]
    (h1 : Module.finrank (↥K) F = 1) : K = ⊤ := by
  have hspan : Submodule.span (↥K) ({(1 : F)} : Set F) = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    rw [finrank_span_singleton (one_ne_zero (α := F)), h1]
  rw [eq_top_iff]
  intro y _
  have hy : y ∈ Submodule.span (↥K) ({(1 : F)} : Set F) := by
    rw [hspan]
    trivial
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hy
  have hc1 : c • (1 : F) = (c : F) := by
    rw [Algebra.smul_def, mul_one]
    rfl
  rw [← hc, hc1]
  exact c.2

end

end AclGeom
