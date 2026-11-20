/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Glue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

variable {X : Type*} [AddCommGroup X] [Module ℚ X]
variable {F : LinearMap.BilinForm ℚ X}

theorem span_eq_top_of_bilinear_moment (R : Finset X) (a b : ℚ)
    (hpd : ∀ x : X, x ≠ 0 → 0 < F x x) (hb : b ≠ 0)
    (hm : ∀ x y, a * (∑ r ∈ R, F r x * F r y) = b * F x y) :
    Submodule.span ℚ (R : Set X) = ⊤ := by
  apply top_unique
  intro x _
  let S := Submodule.span ℚ (R : Set X)
  let v : X := a • (∑ r ∈ R, F r x • r) - b • x
  have hv (y : X) : F v y = 0 := by
    simp only [v, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply,
      map_sum, LinearMap.sum_apply, smul_eq_mul]
    exact sub_eq_zero.mpr (hm x y)
  have hv0 : v = 0 := by
    by_contra hne
    have hp := hpd v hne
    rw [hv] at hp
    exact lt_irrefl 0 hp
  have heq : a • (∑ r ∈ R, F r x • r) = b • x := sub_eq_zero.mp hv0
  have hsum : (∑ r ∈ R, F r x • r) ∈ S := by
    exact S.sum_mem fun r hr => S.smul_mem _ (Submodule.subset_span hr)
  have hbx : b • x ∈ S := heq ▸ S.smul_mem a hsum
  have hx := S.smul_mem b⁻¹ hbx
  simpa only [smul_smul, inv_mul_cancel₀ hb, one_smul] using hx

end SRG266.Lattice
