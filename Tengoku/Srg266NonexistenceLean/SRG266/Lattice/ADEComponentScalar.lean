/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.ADEGram
import Tengoku.Seed.Data.Fin.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266.Lattice

theorem constant_of_successive_eq {K : Type*} {n : ℕ} (a : Fin (n + 1) → K)
    (h : ∀ i : Fin n, a i.castSucc = a i.succ) : ∀ i, a i = a 0 := by
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih => exact (h i).symm.trans ih

theorem constant_of_path_and_leaf {K : Type*} {n : ℕ} (a : Fin (n + 2) → K)
    (h : ∀ i : Fin n, a i.castSucc.castSucc = a i.succ.castSucc)
    (j : Fin (n + 1)) (hj : a (Fin.last (n + 1)) = a j.castSucc) :
    ∀ i, a i = a 0 := by
  have hc := constant_of_successive_eq (fun i : Fin (n + 1) => a i.castSucc) h
  intro i
  exact Fin.lastCases (hj.trans (hc j)) (fun k => hc k) i

theorem gramA_scalar_constant {K : Type*} (n : ℕ) (a : Fin (n + 1) → K)
    (h : ∀ i j, gramA (n + 1) i j ≠ 0 → a i = a j) :
    ∀ i, a i = a 0 := by
  apply constant_of_successive_eq
  intro i
  apply h
  simp [gramA, gramAEntry]

theorem gramD_scalar_constant {K : Type*} (n : ℕ) (a : Fin (n + 4) → K)
    (h : ∀ i j, gramD (n + 4) i j ≠ 0 → a i = a j) :
    ∀ i, a i = a 0 := by
  refine constant_of_path_and_leaf a ?_ (⟨n + 1, by omega⟩ : Fin (n + 3)) ?_
  · intro i
    apply h
    simp [gramD, gramDEntry]
    omega
  · apply h
    simp [gramD, gramDEntry]

theorem gramE_scalar_constant {K : Type*} (n : ℕ) (a : Fin (n + 4) → K)
    (h : ∀ i j, gramE (n + 4) i j ≠ 0 → a i = a j) :
    ∀ i, a i = a 0 := by
  refine constant_of_path_and_leaf a ?_ (⟨2, by omega⟩ : Fin (n + 3)) ?_
  · intro i
    apply h
    simp [gramE, gramEEntry]
    omega
  · apply h
    simp [gramE, gramEEntry]

end SRG266.Lattice
