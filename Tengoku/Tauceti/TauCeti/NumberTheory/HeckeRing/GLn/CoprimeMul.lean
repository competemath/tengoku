/-
Copyright (c) 2024 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
module

public import Tengoku.Tauceti.TauCeti.NumberTheory.HeckeRing.GLn.DiagonalCosets

public import Tengoku
import Tengoku.Tauceti.TauCeti.LinearAlgebra.Matrix.SpecialLinearGroup.CongruenceSplit

/-!
# Coprime multiplication in the `GL_n` Hecke ring

One row of the multiplication table of the integral Hecke ring of the arithmetic Hecke
triple (Shimura, Proposition 3.16): when the determinants `∏ aᵢ`, `∏ bᵢ` are coprime, the
product of the two diagonal double cosets is again a single diagonal coset,
`T(a) · T(b) = T(a * b)`.

The two levels differ in what they assume. The **set-level** results — the double-coset
statements and their supporting lemmas — carry `∀ i, 0 < a i` explicitly, because
`natDiagGL` sends a tuple with a zero entry to its junk value `1` and those statements are
about genuine diagonal representatives. The **ring-level** theorem
`diagElem_mul_of_coprime` needs no positivity at all: on a tuple with a zero entry both
sides degenerate, and coprimality forces the *other* tuple to be all ones (a zero entry makes
that determinant `0`, and `Nat.Coprime 0 m` holds only for `m = 1`), so the identity survives.
It does assume `[NeZero n]`, which is what the arithmetic Hecke triple instance — and hence
multiplication in `IntegralHeckeRing n` — requires.

The scalar row (Shimura 3.17) lives in `GLn/ScalarMul.lean`.

The coprime case runs on a Chinese-remainder factorization of `SL_n(ℤ)`: modulo coprime
`p`, `q` an element splits as a product of one element congruent to the identity mod `p` and
one congruent to the identity mod `q`
(`Matrix.SpecialLinearGroup.exists_mul_modEq_one_of_coprime`), which is what makes the two
diagonal sandwiches commute past each other.

Ported from the AINTLIB `LeanModularForms` project
([`LeanModularForms/HeckeRIngs/GLn/CoprimeMul.lean`](https://github.com/CBirkbeck/AINTLIB),
Chris Birkbeck).

## Main results

* `HeckeRing.GLn.mul_mem_doubleCoset_of_coprime`: the set-level statement — for **positive**
  tuples with coprime determinants, a product of representatives lies in the double coset of
  the product tuple.
* `HeckeRing.GLn.diagElem_mul_of_coprime`: the ring-level statement — `T(a) · T(b) = T(a * b)`
  from **coprimality alone**, given `[NeZero n]`; the zero-entry case degenerates as described
  above.

## References

* [G. Shimura, *Introduction to the arithmetic theory of automorphic functions*][shimura1971],
  Proposition 3.16.
-/

public section

open Matrix HeckeRing DoubleCoset Finset Matrix.SpecialLinearGroup
open scoped Pointwise

namespace HeckeRing.GLn

variable (n : ℕ)

section Conjugation

/-! ## Conjugating congruent elements across the diagonal

An element of `SL_n(ℤ)` congruent to `1` modulo the full diagonal product conjugates
across `natDiagGL n a` — on either side — to an integral matrix of determinant one. -/

private lemma conjugate_congruent_mem_SLnZ (a : Fin n → ℕ) (ha : ∀ i, 0 < a i)
    (τ : SpecialLinearGroup (Fin n) ℤ) (hcong : ∀ i j, (∏ k, (a k : ℤ)) ∣
      ((τ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0)) :
    ∃ σ : SpecialLinearGroup (Fin n) ℤ,
      mapGL ℚ σ = natDiagGL n a * mapGL ℚ τ * (natDiagGL n a)⁻¹ := by
  have hdvd : ∀ i j, (a j : ℤ) ∣ (a i : ℤ) * τ.val i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ j))
        (by simpa [hij] using hcong i j)) _
  set M : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j ↦ (a i : ℤ) * τ.val i j / (a j : ℤ)
  set diag_a := Matrix.diagonal fun i ↦ (a i : ℤ)
  have h_int_eq : diag_a * τ.val = M * diag_a := by
    ext i j
    simpa only [diag_a, M, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.of_apply] using
      (Int.ediv_mul_cancel (hdvd i j)).symm
  have h_det_ne : diag_a.det ≠ 0 := by
    simpa only [diag_a, Matrix.det_diagonal] using
      ne_of_gt (Finset.prod_pos fun i _ ↦ Nat.cast_pos.mpr (ha i))
  have hM_det : M.det = 1 := by
    have h := congr_arg Matrix.det h_int_eq
    rw [Matrix.det_mul, Matrix.det_mul, τ.prop, mul_one] at h
    exact (mul_left_cancel₀ h_det_ne (by rwa [mul_one, mul_comm])).symm
  refine ⟨⟨M, hM_det⟩, ?_⟩
  have h_Q_eq : natDiagGL n a * mapGL ℚ τ =
      mapGL ℚ (⟨M, hM_det⟩ : SpecialLinearGroup (Fin n) ℤ) * natDiagGL n a := by
    apply Units.ext
    simp only [mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Units.val_mul, natDiagGL_coe n a ha]
    have h_diag_map : (Matrix.diagonal fun i ↦ (a i : ℤ)).map (Int.cast : ℤ → ℚ) =
        Matrix.diagonal fun i ↦ (a i : ℚ) := Matrix.diagonal_map (by simp)
    have hmap : (↑(mapGL ℚ (⟨M, hM_det⟩ : SpecialLinearGroup (Fin n) ℤ)) :
        Matrix (Fin n) (Fin n) ℚ) = M.map ⇑(Int.castRingHom ℚ) :=
      mapGL_coe_matrix _
    rw [← h_diag_map]
    simp only [← Int.coe_castRingHom, ← Matrix.map_mul]
    rw [h_int_eq, Matrix.map_mul, hmap]
  exact eq_mul_inv_iff_mul_eq.mpr h_Q_eq.symm

private lemma inv_conjugate_congruent_mem_SLnZ (b : Fin n → ℕ) (hb : ∀ i, 0 < b i)
    (τ : SpecialLinearGroup (Fin n) ℤ) (hcong : ∀ i j, (∏ k, (b k : ℤ)) ∣
      ((τ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0)) :
    ∃ σ : SpecialLinearGroup (Fin n) ℤ,
      mapGL ℚ σ = (natDiagGL n b)⁻¹ * mapGL ℚ τ * natDiagGL n b := by
  have hdvd : ∀ i j, (b i : ℤ) ∣ (b j : ℤ) * τ.val i j := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact dvd_mul_right _ _
    · exact dvd_mul_of_dvd_right (dvd_trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))
        (by simpa [hij] using hcong i j)) _
  set N : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j ↦ (b j : ℤ) * τ.val i j / (b i : ℤ)
  set diag_b := Matrix.diagonal fun i ↦ (b i : ℤ)
  have h_int_eq : τ.val * diag_b = diag_b * N := by
    ext i j
    simp only [diag_b, N, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.of_apply]
    calc τ.val i j * (b j : ℤ) = (b j : ℤ) * τ.val i j := mul_comm _ _
      _ = (b j : ℤ) * τ.val i j / (b i : ℤ) * (b i : ℤ) :=
          (Int.ediv_mul_cancel (hdvd i j)).symm
      _ = (b i : ℤ) * ((b j : ℤ) * τ.val i j / (b i : ℤ)) := mul_comm _ _
  have h_det_ne : diag_b.det ≠ 0 := by
    simpa only [diag_b, Matrix.det_diagonal] using
      ne_of_gt (Finset.prod_pos fun i _ ↦ Nat.cast_pos.mpr (hb i))
  have hN_det : N.det = 1 := by
    have h := congr_arg Matrix.det h_int_eq
    rw [Matrix.det_mul, Matrix.det_mul, τ.prop, one_mul] at h
    exact (mul_left_cancel₀ h_det_ne (by rwa [mul_one])).symm
  refine ⟨⟨N, hN_det⟩, ?_⟩
  have h_Q_eq : natDiagGL n b * mapGL ℚ (⟨N, hN_det⟩ : SpecialLinearGroup (Fin n) ℤ) =
      mapGL ℚ τ * natDiagGL n b := by
    apply Units.ext
    simp only [mapGL_coe_matrix, algebraMap_int_eq, map_apply_coe,
      RingHom.mapMatrix_apply, Int.coe_castRingHom, Units.val_mul, natDiagGL_coe n b hb]
    have h_diag_map : (Matrix.diagonal fun i ↦ (b i : ℤ)).map (Int.cast : ℤ → ℚ) =
        Matrix.diagonal fun i ↦ (b i : ℚ) := Matrix.diagonal_map (by simp)
    have hmap : (↑(mapGL ℚ (⟨N, hN_det⟩ : SpecialLinearGroup (Fin n) ℤ)) :
        Matrix (Fin n) (Fin n) ℚ) = N.map ⇑(Int.castRingHom ℚ) :=
      mapGL_coe_matrix _
    rw [← h_diag_map]
    simp only [← Int.coe_castRingHom, ← Matrix.map_mul]
    rw [h_int_eq, Matrix.map_mul, hmap]
  exact (eq_inv_mul_of_mul_eq h_Q_eq).trans (mul_assoc _ _ _).symm

end Conjugation

section CoprimeCosets

/-- **The set-level coprime product** (Shimura, Proposition 3.16, key step): sandwiching any
`τ ∈ SL_n(ℤ)` between the diagonals of `a` and `b` stays inside the double coset of the
diagonal of `a * b`, when the determinants are coprime. -/
lemma mul_mem_doubleCoset_of_coprime (a b : Fin n → ℕ)
    (ha_pos : ∀ i, 0 < a i) (hb_pos : ∀ i, 0 < b i)
    (hcop : Nat.Coprime (∏ i, a i) (∏ i, b i)) (τ : SpecialLinearGroup (Fin n) ℤ) :
    natDiagGL n a * mapGL ℚ τ * natDiagGL n b ∈
      doubleCoset (natDiagGL n (a * b) : GL (Fin n) ℚ) (SLnZ n) (SLnZ n) := by
  obtain ⟨τ₁, τ₂, hτ, hτ₁, hτ₂⟩ :=
    exists_mul_modEq_one_of_coprime (∏ i, a i) (∏ i, b i) hcop τ
  have hτ₁_cong : ∀ i j, (∏ k, (a k : ℤ)) ∣
      ((τ₁ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0) := fun i j ↦ by
    rw [← Nat.cast_prod]; exact hτ₁ i j
  obtain ⟨σ₁, hσ₁⟩ := conjugate_congruent_mem_SLnZ n a ha_pos τ₁ hτ₁_cong
  have hτ₂_cong : ∀ i j, (∏ k, (b k : ℤ)) ∣
      ((τ₂ : Matrix (Fin n) (Fin n) ℤ) i j - if i = j then 1 else 0) := fun i j ↦ by
    rw [← Nat.cast_prod]; exact hτ₂ i j
  obtain ⟨σ₂, hσ₂⟩ := inv_conjugate_congruent_mem_SLnZ n b hb_pos τ₂ hτ₂_cong
  rw [mem_doubleCoset]
  refine ⟨mapGL ℚ σ₁, coe_mem_SLnZ n σ₁, mapGL ℚ σ₂, coe_mem_SLnZ n σ₂, ?_⟩
  have hσ₁' : natDiagGL n a * mapGL ℚ τ₁ = mapGL ℚ σ₁ * natDiagGL n a := by
    rw [hσ₁]; group
  have hσ₂' : mapGL ℚ τ₂ * natDiagGL n b = natDiagGL n b * mapGL ℚ σ₂ := by
    rw [hσ₂]; group
  rw [hτ, map_mul (mapGL ℚ)]
  calc natDiagGL n a * (mapGL ℚ τ₁ * mapGL ℚ τ₂) * natDiagGL n b
      = natDiagGL n a * mapGL ℚ τ₁ * (mapGL ℚ τ₂ * natDiagGL n b) := by group
    _ = natDiagGL n a * mapGL ℚ τ₁ * (natDiagGL n b * mapGL ℚ σ₂) := by rw [hσ₂']
    _ = mapGL ℚ σ₁ * natDiagGL n a * (natDiagGL n b * mapGL ℚ σ₂) := by rw [hσ₁']
    _ = mapGL ℚ σ₁ * (natDiagGL n a * natDiagGL n b) * mapGL ℚ σ₂ := by group
    _ = mapGL ℚ σ₁ * natDiagGL n (a * b) * mapGL ℚ σ₂ := by
        rw [natDiagGL_mul n a b ha_pos hb_pos]

variable [NeZero n]

end CoprimeCosets

section CoprimeIntegrality

variable [NeZero n]

end CoprimeIntegrality

end HeckeRing.GLn
