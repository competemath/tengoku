/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CartanAZeroSum
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SimplexCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

open scoped BigOperators

theorem simplex_pair_delete_last (n : ℕ) (x y : Fin (n+1) → ℚ)
    (hx : (∑ i, x i) = 0) (hy : (∑ i, y i) = 0) :
    simplexRatForm n (fun i => x i.castSucc) (fun i => y i.castSucc) =
      standardRatForm (n+1) x y := by
  rw [Fin.sum_univ_castSucc] at hx hy
  rw [simplexRatForm_apply, standardRatForm_apply, Fin.sum_univ_castSucc]
  have hx' : (∑ i : Fin n, x i.castSucc) = -x (Fin.last n) := by linarith
  have hy' : (∑ i : Fin n, y i.castSucc) = -y (Fin.last n) := by linarith
  rw [hx', hy']
  ring

def simplexSimpleRoot (n : ℕ) (i : Fin n) : Fin n → ℚ :=
  fun j => aSimpleVector i j.castSucc

theorem simplexSimpleRoot_mem (n : ℕ) (i : Fin n) :
    simplexSimpleRoot n i ∈ coordinateIntegerLattice n := by
  refine mem_coordinateIntegerLattice.mpr
    ⟨fun j => (if j.castSucc = i.castSucc then 1 else 0) -
      (if j.castSucc = i.succ then 1 else 0), ?_⟩
  intro j
  simp [simplexSimpleRoot, aSimpleVector, Pi.single_apply]

theorem simplexSimpleRoot_gram (n : ℕ) (i j : Fin n) :
    simplexRatForm n (simplexSimpleRoot n i) (simplexSimpleRoot n j) =
      (gramA n i j : ℚ) := by
  exact (simplex_pair_delete_last n (aSimpleVector i) (aSimpleVector j)
    (aSimpleVector_sum i) (aSimpleVector_sum j)).trans (aSimpleVector_gram i j)

end SRG266.Lattice
