/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEComponentScalar
import Tengoku.Seed.LinearAlgebra.BilinearForm.Basic
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

variable {X Y : Type*} [AddCommGroup X] [Module ℚ X] [AddCommGroup Y] [Module ℚ Y]

theorem zero_or_zero_of_even_sum_two
    (B : LinearMap.BilinForm ℚ X) (C : LinearMap.BilinForm ℚ Y)
    (hB : ∀ x, x ≠ 0 → 0 < B x x) (hC : ∀ y, y ≠ 0 → 0 < C y y)
    (x : X) (y : Y) (hx : ∃ m : ℤ, B x x = 2*(m : ℚ))
    (hsum : B x x+C y y = 2) : x = 0 ∨ y = 0 := by
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  · right
    obtain ⟨m, hm⟩ := hx
    have hmQ : (0 : ℚ) < m := by linarith [hB x hx0]
    have hmZ : (0 : ℤ) < m := by exact_mod_cast hmQ
    have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (1 : ℤ) ≤ m by omega)
    by_contra hy0
    linarith [hC y hy0]

theorem same_zero_side_of_pair_ne_zero
    (B : LinearMap.BilinForm ℚ X) (C : LinearMap.BilinForm ℚ Y)
    {x u : X} {y v : Y} (hx : x = 0 ∨ y = 0) (hu : u = 0 ∨ v = 0)
    (hp : B x u+C y v ≠ 0) : x = 0 ↔ u = 0 := by
  constructor
  · intro hx0
    rcases hu with hu0 | hv0
    · exact hu0
    · exact (hp (by simp only [hx0, hv0, map_zero, LinearMap.zero_apply, add_zero])).elim
  · intro hu0
    rcases hx with hx0 | hy0
    · exact hx0
    · exact (hp (by simp only [hu0, hy0, map_zero, LinearMap.zero_apply, zero_add])).elim

theorem A_chain_in_one_component
    (B : LinearMap.BilinForm ℚ X) (C : LinearMap.BilinForm ℚ Y)
    (n : ℕ) (x : Fin (n+1) → X) (y : Fin (n+1) → Y)
    (hside : ∀ i, x i = 0 ∨ y i = 0)
    (hgram : ∀ i j, B (x i) (x j)+C (y i) (y j) = (gramA (n+1) i j : ℚ)) :
    (∀ i, x i = 0) ∨ (∀ i, y i = 0) := by
  have hc := gramA_scalar_constant n (fun i => x i = 0) (by
    intro i j hij
    apply propext
    apply same_zero_side_of_pair_ne_zero B C (hside i) (hside j)
    rw [hgram]
    exact_mod_cast hij)
  by_cases h0 : x 0 = 0
  · exact Or.inl (fun i => (hc i).mpr h0)
  · right
    intro i
    exact (hside i).resolve_left (fun hi => h0 ((hc i).mp hi))

end SRG266.Lattice
