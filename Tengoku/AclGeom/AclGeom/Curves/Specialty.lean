/-
Copyright (c) 2026 Adam Topaz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Topaz, Claude
-/
import Tengoku.AclGeom.AclGeom.Curves.Adeles

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The index of specialty

The quotient `𝔸 / (A(D) + F)` and its dimension `i(D)`. The one-point
decomposition of adele spaces makes the quotient grow by at most a line
per point, and the dichotomy trades that line against the growth of the
Riemann–Roch space; chaining up to a genus-attaining divisor — where the
quotient vanishes by adelic surjectivity — yields Stichtenoth 1.5.4:
`i(D) = ℓ(D) − deg D − 1 + g`, i.e. the full Riemann–Roch identity with
`i(D)` as the correction term.

This module is part of the formalization of the Evans–Hrushovski–Gismatullin
reconstruction theorem; the source of truth is `sources/blueprint.tex`.

**Status:** in progress (M4b, issue #13, P5).
-/

namespace AclGeom

noncomputable section

variable {k F : Type*} [Field k] [Field F] [Algebra k F]
variable [IsAlgClosed k] [IsFunctionFieldOneVar k F]

/-- The subspace `A(D) + F` of the adele module.-/
noncomputable def boundedSubmodule (D : Divisor k F) :
    Submodule k ↥(adeleSubmodule k F) :=
  (adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F)).comap
    (adeleSubmodule k F).subtype

theorem mem_boundedSubmodule_iff {D : Divisor k F}
    {α : ↥(adeleSubmodule k F)} :
    α ∈ boundedSubmodule D ↔
      (α : (Q : Place k F) → F) ∈
        adeleSpace D ⊔ LinearMap.range (adeleDiagonal k F) := Iff.rfl

theorem boundedSubmodule_mono {D E : Divisor k F} (h : D ≤ E) :
    boundedSubmodule (D : Divisor k F) ≤ boundedSubmodule E :=
  Submodule.comap_mono (sup_le_sup_right (adeleSpace_mono h) _)

theorem adeleMonomial_mem_adeleSubmodule (P : Place k F) (n : ℤ) :
    adeleMonomial P n ∈ adeleSubmodule k F :=
  adeleSpace_le_adeleSubmodule (Finsupp.single P (-n))
    (adeleMonomial_mem_adeleSpace P
      (by rw [Finsupp.single_eq_same]; omega))

/-- The monomial adele as an element of the adele module.-/
noncomputable def adeleMonomialMem (P : Place k F) (n : ℤ) :
    ↥(adeleSubmodule k F) :=
  ⟨adeleMonomial P n, adeleMonomial_mem_adeleSubmodule P n⟩

/-- The **index of specialty** quotient `𝔸 / (A(D) + F)`.-/
abbrev SpecialtyQuotient (D : Divisor k F) :=
  ↥(adeleSubmodule k F) ⧸ boundedSubmodule D

/-- The **index of specialty** `i(D)`: the codimension of `A(D) + F`
in the adeles.-/
noncomputable def specialtyIndex (D : Divisor k F) : ℤ :=
  Module.finrank k (SpecialtyQuotient D)

end

end AclGeom
