/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.LinearAlgebra.LinearIndependent.Basic
import Tengoku.Seed.LinearAlgebra.SesquilinearForm.Orthogonal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {R X ι κ : Type*} [CommRing R] [AddCommGroup X] [Module R X]

theorem linearIndependent_sum_of_orthogonal
    (B : X →ₗ[R] X →ₗ[R] R) (hself : ∀ x, B x x = 0 → x = 0)
    (r : ι → X) (s : κ → X) (hr : LinearIndependent R r) (hs : LinearIndependent R s)
    (horth : ∀ i j, B (r i) (s j) = 0) : LinearIndependent R (Sum.elim r s) := by
  have hleft (j) : Submodule.span R (Set.range r) ≤ (B.flip (s j)).ker :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact horth i j)
  have hright : Submodule.span R (Set.range s) ≤
      (Submodule.span R (Set.range r)).orthogonalBilin B :=
    Submodule.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact fun x hx => hleft j hx)
  exact hr.sum_type hs (Submodule.disjoint_def.mpr
    (fun x hx hy => hself x (hright hy x hx)))

end SRG266.Lattice
