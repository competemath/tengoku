/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11E6FrameOrientation
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11D7E6Energy
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanASignedPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

theorem A11E6NormalizedType.label_nine_of_zero
    {a δ : ℤ} {u : Fin 11 → ℚ} {v : Fin 6 → ℚ}
    (h : A11E6NormalizedType a δ u v) (hv : v = 0) : a = 9 := by
  rcases h with h | ⟨_, _, hn, _⟩
  · exact h.1
  · simp only [hv, map_zero] at hn
    norm_num at hn

theorem a11_type_A_binary_coordinates
    {ε δ : ℤ} {u : Fin 11 → ℚ} {v : Fin 6 → ℚ}
    (hv : v = 0)
    (h : ∃ (a : ℤ) (z : Fin 12 → ℤ), (∑ i, z i) = a ∧
      (∀ i, (ε : ℚ)*cartanAZeroSum 11 u i = (z i : ℚ)-(a : ℚ)/12) ∧
      (∀ i, z i = 0 ∨ z i = 1) ∧ A11E6NormalizedType a δ u v) :
    ∃ z : Fin 12 → ℤ, (∑ i, z i) = 3 ∧
      (∀ i, (-(ε : ℚ))*cartanAZeroSum 11 u i = (z i : ℚ)-3/12) ∧
      (∀ i, z i = 0 ∨ z i = 1) := by
  obtain ⟨a, z, hz, hc, hb, ht⟩ := h
  have ha := ht.label_nine_of_zero hv
  rw [ha] at hz hc
  norm_num only at hc
  refine ⟨fun i => 1-z i, ?_, ?_, ?_⟩
  · rw [Finset.sum_sub_distrib, hz]
    norm_num
  · intro i
    push_cast
    linarith [hc i]
  · intro i
    rcases hb i with hi | hi <;> simp [hi]

variable {W U : Type*} [AddCommGroup W] [Module ℚ W] [AddCommGroup U] [Module ℚ U]

end SRG266.Lattice
