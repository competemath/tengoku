/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.D7ShortDual
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.MomentBounds
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Glue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

variable {W U ι : Type*} [AddCommGroup W] [Module ℚ W]
  [AddCommGroup U] [Module ℚ U] [Fintype ι]
variable {B : LinearMap.BilinForm ℚ W} {C : LinearMap.BilinForm ℚ U}

theorem d7_root_separation_of_frame
    (u : ι → W) (L : Submodule ℤ ((W × (Fin 7 → ℚ)) × U)) (bound : ℚ)
    (hB : ∀ y : W, y ≠ 0 → 0 < B y y) (hC : ∀ z : U, z ≠ 0 → 0 < C z z)
    (hi : IsIntegral (prodForm (prodForm B (standardRatForm 7)) C) L)
    (hD7 : ∀ a ∈ evenCoordinateLattice 7, ((0, a), (0 : U)) ∈ L)
    (hframe : ∀ i, ((u i, coordinateSpinor 7), (0 : U)) ∈ L)
    (hbound : ∀ y, ∑ i, (B y (u i)) ^ 2 ≤ bound * B y y)
    (hbound0 : 0 ≤ bound) (hmass : 4 * bound < Fintype.card ι)
    {r : (W × (Fin 7 → ℚ)) × U} (hr : r ∈ L)
    (hnorm : prodForm (prodForm B (standardRatForm 7)) C r r = 2) :
    r.1.2 = 0 ∨ (r.1.1 = 0 ∧ r.2 = 0) := by
  rcases r with ⟨⟨y, a⟩, z⟩
  change a = 0 ∨ (y = 0 ∧ z = 0)
  by_cases ha0 : a = 0
  · exact Or.inl ha0
  right
  have ha : 0 < standardRatForm 7 a a := standardRatForm_posDef 7 a ha0
  have hBy : 0 ≤ B y y := by
    by_cases hy : y = 0
    · simp [hy]
    · exact (hB y hy).le
  have hCz : 0 ≤ C z z := by
    by_cases hz : z = 0
    · simp [hz]
    · exact (hC z hz).le
  change B y y + standardRatForm 7 a a + C z z = 2 at hnorm
  have htwo : standardRatForm 7 a a = 2 := by
    by_contra hne
    have hsmall : standardRatForm 7 a a < 2 := lt_of_le_of_ne (by linarith) hne
    have hadual : a ∈ (standardRatForm 7).dualSubmodule (evenCoordinateLattice 7) := by
      intro b hb
      have hp := hi hr ((0, b), 0) (hD7 b hb)
      simpa only [prodForm_apply, map_zero, zero_add, add_zero] using hp
    have hgap (i) : (2 - standardRatForm 7 a a) / 4 ≤ (B y (u i)) ^ 2 := by
      apply d7_short_dual_gap hadual ha hsmall
      have hp := hi hr ((u i, coordinateSpinor 7), 0) (hframe i)
      simpa only [prodForm_apply, map_zero, add_zero] using hp
    have hupper : ∑ i, (B y (u i)) ^ 2 ≤ bound * (2 - standardRatForm 7 a a) :=
      (hbound y).trans (mul_le_mul_of_nonneg_left (by linarith) hbound0)
    have hc := MomentBounds.card_le_four_mul_bound Finset.univ
      (fun i => B y (u i)) (2 - standardRatForm 7 a a) bound (by linarith)
      (fun i _ => hgap i) hupper
    simp only [Finset.card_univ] at hc
    exact (not_le_of_gt hmass) hc
  constructor
  · by_contra hy
    have hp := hB y hy
    linarith
  · by_contra hz
    have hp := hC z hz
    linarith

end SRG266.Lattice
