/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Seed.LinearAlgebra.QuadraticForm.Basic
import Tengoku.Seed.Algebra.Order.BigOperators.Group.Finset
import Tengoku.Seed.Algebra.BigOperators.Field
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

variable {X : Type*} [AddCommGroup X] [Module ℚ X]

theorem orthogonal_basis_pair_repr {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : LinearMap.BilinForm ℚ X) (b : Module.Basis κ ℚ X)
    (hb : B.IsOrthoᵢ b) (x : X) (i : κ) :
    B (b i) x = b.repr x i * B (b i) (b i) := by
  calc
    _ = B (b i) (∑ j, b.repr x j • b j) := by rw [b.sum_repr]
    _ = _ := by
      rw [map_sum, Finset.sum_eq_single i]
      · simp only [map_smul, smul_eq_mul]
      · intro j _ hji
        simp only [map_smul, smul_eq_mul, hb hji.symm, mul_zero]
      · simp

theorem orthogonal_basis_norm_expansion {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : LinearMap.BilinForm ℚ X) (b : Module.Basis κ ℚ X)
    (hb : B.IsOrthoᵢ b) (hdiag : ∀ i, B (b i) (b i) ≠ 0) (x : X) :
    B x x = ∑ i, (B (b i) x)^2/B (b i) (b i) := by
  calc
    _ = B (∑ i, b.repr x i • b i) x := by rw [b.sum_repr]
    _ = ∑ i, b.repr x i * B (b i) x := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [orthogonal_basis_pair_repr B b hb]
      field_simp [hdiag i]

theorem rational_frame_mass_le_finrank [FiniteDimensional ℚ X]
    {ι : Type*} [Fintype ι] (B : LinearMap.BilinForm ℚ X) (hB : B.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < B x x) (v : ι → X) (C : ℚ)
    (hbound : ∀ y, (∑ i, (B y (v i))^2) ≤ C*B y y) :
    (∑ i, B (v i) (v i)) ≤ C*(Module.finrank ℚ X : ℚ) := by
  classical
  let : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  have hdiag (j) : 0 < B (b j) (b j) := hpos (b j) (b.ne_zero j)
  have hsum (j) : (∑ i, (B (b j) (v i))^2/B (b j) (b j)) ≤ C := by
    rw [← Finset.sum_div]
    exact (div_le_iff₀ (hdiag j)).mpr (hbound (b j))
  rw [Finset.sum_congr rfl (fun i _ =>
    orthogonal_basis_norm_expansion B b hb (fun j => ne_of_gt (hdiag j)) (v i))]
  rw [Finset.sum_comm]
  have h := Finset.sum_le_sum (s := Finset.univ) (fun j _ => hsum j)
  simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_comm] using h

theorem rational_frame_mass_le_submodule_finrank [FiniteDimensional ℚ X]
    {ι : Type*} [Fintype ι] (B : LinearMap.BilinForm ℚ X) (hB : B.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < B x x) (v : ι → X) (C : ℚ)
    (hbound : ∀ y, (∑ i, (B y (v i))^2) ≤ C*B y y)
    (P : Submodule ℚ X) (hv : ∀ i, v i ∈ P) :
    (∑ i, B (v i) (v i)) ≤ C*(Module.finrank ℚ P : ℚ) := by
  apply rational_frame_mass_le_finrank (B.domRestrict₁₂ P P) (hB.domRestrict P)
    (fun x hx => hpos x (fun hz => hx (Subtype.ext hz))) (fun i => ⟨v i, hv i⟩) C
  intro y
  exact hbound y

end SRG266.Lattice
