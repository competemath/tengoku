import Tengoku.FltAnthropic.Definitions.Def_TaylorWiles_Primes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_trace_pow_eq_sum_pow.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_trace_pow_eq_sum_pow

theorem solution {R : Type*} [CommRing R]
    {M : Matrix (Fin 2) (Fin 2) R} {α β : R}
    (htr : M.trace = α + β) (hdet : M.det = α * β) (k : ℕ) :
    (M ^ k).trace = α ^ k + β ^ k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp [Matrix.trace_one, one_add_one_eq_two]
    | 1 => simpa using htr
    | (k + 2) =>
      rw [Matrix.trace_pow_add_two, htr, hdet, ih (k + 1) (by omega), ih k (by omega)]
      ring
