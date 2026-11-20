/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.BinaryConstantBlock
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanAChainCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.A11E6FrameOrientation
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.MomentBounds

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators Classical

theorem a11_constant_block_coordinate (u : Fin 11 → ℚ) (ε a : ℤ)
    (z : Fin 12 → ℤ) (f : Fin 5 ↪ Fin 12)
    (hsum : (∑ i, z i) = a)
    (hcoord : ∀ i, (ε : ℚ)*cartanAZeroSum 11 u i = (z i : ℚ)-(a : ℚ)/12)
    (hbinary : ∀ i, z i = 0 ∨ z i = 1) (ha : a = 9 ∨ a = 1)
    (hconst : ∀ j, cartanAZeroSum 11 u (f j) = cartanAZeroSum 11 u (f 0)) :
    (ε : ℚ)*cartanAZeroSum 11 u (f 0) = if a = 9 then 1/4 else -1/12 := by
  have hz (j : Fin 5) : z (f j) = z (f 0) := by
    have h1 := hcoord (f j)
    have h0 := hcoord (f 0)
    rw [hconst j] at h1
    have heq : (z (f j) : ℚ) = z (f 0) := by linarith
    exact_mod_cast heq
  have hb := binary_twelve_constant_block (by decide) z a (z (f 0)) f hsum hbinary hz ha
  have hc := hcoord (f 0)
  rcases hb with ⟨ha, ht⟩ | ⟨ha, ht⟩ <;> rw [ha, ht] at hc <;>
    norm_num [ha] at hc ⊢ <;> exact hc

theorem two_type_first_moment_counts {ι : Type*} [Fintype ι]
    (a : ι → ℤ) (ha : ∀ i, a i = 9 ∨ a i = 1) (hcard : Fintype.card ι = 220)
    (hfirst : (∑ i, if a i = 9 then (1/4 : ℚ) else -1/12) = 0) :
    (Finset.univ.filter (fun i => a i = 9)).card = 55 ∧
      (Finset.univ.filter (fun i => a i = 1)).card = 165 := by
  have hnot (i : ι) : (¬a i = 9) ↔ a i = 1 := by rcases ha i with h | h <;> omega
  have htotal := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i => a i = 9)
  simp only [hnot, Finset.card_univ, hcard] at htotal
  have htotalQ : ((Finset.univ.filter (fun i => a i = 9)).card : ℚ)+
      (Finset.univ.filter (fun i => a i = 1)).card = 220 := by exact_mod_cast htotal
  simp only [Finset.sum_ite, hnot, Finset.sum_const, nsmul_eq_mul] at hfirst
  have hfirstQ : ((Finset.univ.filter (fun i => a i = 9)).card : ℚ)/4-
      (Finset.univ.filter (fun i => a i = 1)).card/12 = 0 := by linarith
  obtain ⟨hA, hB⟩ := MomentBounds.shell_type_balance _ _ htotalQ hfirstQ
  exact ⟨by exact_mod_cast hA, by exact_mod_cast hB⟩

end SRG266.Lattice
