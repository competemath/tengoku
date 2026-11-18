import Tengoku.FltAnthropic.Definitions.Def_TaylorWiles_Primes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Matrix_trace_pow_eq_of_trace_eq_of_det_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Matrix_trace_pow_eq_of_trace_eq_of_det_eq

/--
@isnad1 id=eq.2h4v.s8.999538b23d2c from=translated src=- shape=b59afd42 vocab=5d296274
-/
theorem solution {R : Type*} [CommRing R]
    {M N : Matrix (Fin 2) (Fin 2) R} (htr : M.trace = N.trace) (hdet : M.det = N.det)
    (k : ℕ) : (M ^ k).trace = (N ^ k).trace := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k with
    | 0 => simp
    | 1 => simpa using htr
    | (k + 2) =>
      rw [Matrix.trace_pow_add_two, Matrix.trace_pow_add_two, htr, hdet,
        ih (k + 1) (by omega), ih k (by omega)]
