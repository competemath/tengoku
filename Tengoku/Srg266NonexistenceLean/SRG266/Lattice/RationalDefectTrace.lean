/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RationalFrameTrace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

variable {X : Type*} [AddCommGroup X] [Module ℚ X]

theorem orthogonal_basis_pair_expansion {κ : Type*} [Fintype κ] [DecidableEq κ]
    (B : LinearMap.BilinForm ℚ X) (b : Module.Basis κ ℚ X)
    (hb : B.IsOrthoᵢ b) (hdiag : ∀ i, B (b i) (b i) ≠ 0) (x y : X) :
    B x y = ∑ i, B (b i) x * B (b i) y / B (b i) (b i) := by
  calc
    _ = B (∑ i, b.repr x i • b i) y := by rw [b.sum_repr]
    _ = ∑ i, b.repr x i * B (b i) y := by
      simp only [map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [orthogonal_basis_pair_repr B b hb x i]
      field_simp [hdiag i]

theorem rational_frame_mass_eq_quadratic_defect [FiniteDimensional ℚ X]
    {ι : Type*} [Fintype ι] (B : LinearMap.BilinForm ℚ X) (hB : B.IsSymm)
    (hpos : ∀ x, x ≠ 0 → 0 < B x x) (v : ι → X) (u w : X) (a p q r : ℚ)
    (hidentity : ∀ y, (∑ i, (B y (v i))^2) =
      a*B y y-(p*(B y u)^2+q*(B y w)^2+r*(B y u)*(B y w))) :
    (∑ i, B (v i) (v i)) =
      a*(Module.finrank ℚ X : ℚ)-(p*B u u+q*B w w+r*B u w) := by
  classical
  let : Invertible (2 : ℚ) := invertibleOfNonzero (by norm_num)
  obtain ⟨b, hb⟩ := LinearMap.BilinForm.exists_orthogonal_basis hB
  have hdiag (j) : B (b j) (b j) ≠ 0 := ne_of_gt (hpos (b j) (b.ne_zero j))
  have hsum (j) :
      (∑ i, (B (b j) (v i))^2/B (b j) (b j)) =
        a-(p*((B (b j) u)^2/B (b j) (b j))+
          q*((B (b j) w)^2/B (b j) (b j))+
          r*(B (b j) u*B (b j) w/B (b j) (b j))) := by
    rw [← Finset.sum_div, hidentity]
    field_simp [hdiag j]
  rw [Finset.sum_congr rfl (fun i _ => orthogonal_basis_norm_expansion B b hb hdiag (v i)),
    Finset.sum_comm, Finset.sum_congr rfl (fun j _ => hsum j)]
  rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
    ← orthogonal_basis_norm_expansion B b hb hdiag u,
    ← orthogonal_basis_norm_expansion B b hb hdiag w,
    ← orthogonal_basis_pair_expansion B b hb hdiag u w]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

end SRG266.Lattice
