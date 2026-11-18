import Tengoku.Seed.LinearAlgebra.Matrix.Charpoly.Coeff
import Tengoku.Seed.Tactic.LinearCombination

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_pow_five_eq_one_of_trace_sq_add_trace_sub_one

open Polynomial

namespace Matrix
export _root_.Matrix (row aeval_self_charpoly charpoly charpoly_fin_two det of trace)
open _root_.Matrix

variable {R : Type*} [CommRing R]

theorem pow_five_aux (g : Matrix (Fin 2) (Fin 2) R) (hdet : g.det = 1)
    (ht : g.trace ^ 2 + g.trace - 1 = 0) : g ^ 5 = 1 := by
  nontriviality R
  set t := g.trace with ht_def
  have e1 : (C t : R[X]) ^ 4 - 3 * C t ^ 2 + 1 = 0 := by
    have : t ^ 4 - 3 * t ^ 2 + 1 = 0 := by linear_combination (t ^ 2 - t - 1) * ht
    have h__af := (congrArg (C : R → R[X]) this)
    simp at h__af
    exact h__af
  have e2 : (C t : R[X]) ^ 3 - 2 * C t + 1 = 0 := by
    have : t ^ 3 - 2 * t + 1 = 0 := by linear_combination (t - 1) * ht
    have h__af := (congrArg (C : R → R[X]) this)
    simp at h__af
    exact h__af
  have key : (X ^ 5 - 1 : R[X]) =
      g.charpoly * (X ^ 3 + C t * X ^ 2 + (C t ^ 2 - 1) * X + (C t ^ 3 - 2 * C t)) := by
    rw [Matrix.charpoly_fin_two, hdet, map_one]
    linear_combination X * e1 - e2
  have h := Matrix.aeval_self_charpoly g
  have : aeval g (X ^ 5 - 1 : R[X]) = 0 := by rw [key, map_mul, h, zero_mul]
  simpa [sub_eq_zero] using this

end Matrix

theorem solution {R : Type*} [CommRing R] (g : Matrix (Fin 2) (Fin 2) R) (hdet : g.det = 1) (ht : g.trace ^ 2 + g.trace - 1 = 0) : g ^ 5 = 1 :=
  Matrix.pow_five_aux g hdet ht

