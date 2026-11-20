/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RationalFrameTrace
import Tengoku.Seed.LinearAlgebra.BilinearForm.Orthogonal
import Tengoku.Seed.LinearAlgebra.Dimension.Constructions
import Tengoku.Seed.LinearAlgebra.Matrix.BilinearForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

variable {X : Type*} [AddCommGroup X] [Module ℚ X]

theorem finrank_orthogonal_span_le [FiniteDimensional ℚ X]
    {κ : Type*} [Fintype κ] (B : LinearMap.BilinForm ℚ X)
    (hpos : ∀ x, x ≠ 0 → 0 < B x x) (r : κ → X) (hr : LinearIndependent ℚ r) :
    Module.finrank ℚ ((Submodule.span ℚ (Set.range r)).orthogonalBilin B) ≤
      Module.finrank ℚ X-Fintype.card κ := by
  let P := Submodule.span ℚ (Set.range r)
  let Q := P.orthogonalBilin B
  have hd : Disjoint P Q := Submodule.disjoint_def.mpr (fun x hx hq => by
    by_contra hne
    have h := hpos x hne
    have hz : B x x = 0 := hq x hx
    linarith)
  have hf := Submodule.finrank_sup_add_finrank_inf_eq P Q
  rw [hd.eq_bot, finrank_bot, add_zero] at hf
  have hle := Submodule.finrank_le (P ⊔ Q)
  have hP : Module.finrank ℚ P = Fintype.card κ := finrank_span_eq_card hr
  change Module.finrank ℚ Q ≤ _
  omega

theorem rational_frame_mass_le_orthogonal_rank [FiniteDimensional ℚ X]
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (B : LinearMap.BilinForm ℚ X) (hB : LinearMap.IsSymm B)
    (hpos : ∀ x, x ≠ 0 → 0 < B x x) (v : ι → X) (C : ℚ) (hC : 0 ≤ C)
    (hbound : ∀ y, (∑ i, (B y (v i))^2) ≤ C*B y y)
    (r : κ → X) (hr : LinearIndependent ℚ r) (horth : ∀ j i, B (r j) (v i) = 0) :
    (∑ i, B (v i) (v i)) ≤ C*((Module.finrank ℚ X-Fintype.card κ : ℕ) : ℚ) := by
  let P := Submodule.span ℚ (Set.range r)
  have hv (i) : v i ∈ P.orthogonalBilin B := by
    have hker : P ≤ (B.flip (v i)).ker := Submodule.span_le.mpr (by
      rintro _ ⟨j, rfl⟩
      exact horth j i)
    exact fun x hx => hker hx
  have hmass := rational_frame_mass_le_submodule_finrank B hB hpos v C hbound _ hv
  have hrank := finrank_orthogonal_span_le B hpos r hr
  exact hmass.trans (mul_le_mul_of_nonneg_left (by exact_mod_cast hrank) hC)

end SRG266.Lattice
