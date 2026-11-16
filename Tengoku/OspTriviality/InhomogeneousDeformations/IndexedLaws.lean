import Tengoku.OspTriviality.InhomogeneousDeformations.Indexed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# R2-C-1 (U0-U3) — general-rank interface, degree law and super-skew

`H1.2`: every declaration here is stated for general `n : ℕ`, with indices
in `Fin (2 * n)`; no `n = 1` specialization, `Fin 2` instance, or literal
five-element basis appears anywhere. `Indexed.lean` (frozen) is never
reopened; every law here is a genuinely new statement/proof about its
already-accepted definitions.

`H1.3` (verbatim, do not upgrade): a successful R2-C-1 establishes, for
every `n ≥ 1`, that the frozen indexed bracket satisfies the degree law
and super-skew symmetry -- half of P1. It does NOT establish super-Jacobi
(U4/U5, R2-C-2) or the oscillator realization correspondence (P1's own
declared non-goal).
-/

namespace InhomogeneousDeformations
namespace Indexed

/-! ## U0 — `Jn`/`Lof` interface at general `n`

Transposed from the `n=1` route Agent1 specified: antisymmetry follows by
case analysis on the two mutually-exclusive decidable branch conditions,
introducing no term containing `2 * n` as a factor (the omega-nonlinearity
trap from correction002). -/

/-- `Jn`'s vanishing diagonal: `J_{uu} = 0`. Both of `Jn`'s branch
conditions reduce, at `v = u`, to the impossible `u = u + 1`.-/
theorem Jn_diag (n : ℕ) (u : Fin (2 * n)) : Jn n u u = 0 := by
  have h : (u : ℕ) ≠ (u : ℕ) + 1 := by omega
  simp [Jn]

/-! ## U1 — degree law at general `n` -/

/-- General-rank homogeneity predicate, transposed from `Native.lean`'s
`n=1`-only `IsHomog` (which is stated over the fixed `Mod = Basis5 → Coeff`
and cannot itself be reused here).-/
def IsHomogN {n : ℕ} (x : IndexedMod n) (d : ZMod 2) : Prop :=
  ∀ i : IndexedBasis n, x i ≠ 0 → parity i = d

/-! ## U2 — super-skew at basis level, general `n`

`gsignN` is the rank-indexed analogue of `N1Proofs.lean`'s `Coeff`-valued
`gsign`, valued in `Pn n` here since general-rank structure constants live
there, not in the `n=1`-only `Coeff`. -/

noncomputable def gsignN (n : ℕ) (p q : ZMod 2) : Pn n :=
  if p = 1 ∧ q = 1 then cratN n (-1) else cratN n 1

theorem gsignN_00 (n : ℕ) : gsignN n (0 : ZMod 2) (0 : ZMod 2) = 1 := by
  unfold gsignN; rw [ite_eq_right (by decide), cratN_one]
theorem gsignN_01 (n : ℕ) : gsignN n (0 : ZMod 2) (1 : ZMod 2) = 1 := by
  unfold gsignN; rw [ite_eq_right (by decide), cratN_one]
theorem gsignN_10 (n : ℕ) : gsignN n (1 : ZMod 2) (0 : ZMod 2) = 1 := by
  unfold gsignN; rw [ite_eq_right (by decide), cratN_one]
theorem gsignN_11 (n : ℕ) : gsignN n (1 : ZMod 2) (1 : ZMod 2) = -1 := by
  unfold gsignN
  rw [ite_eq_left (by decide)]
  rw [show (-1 : ℚ) = -(1 : ℚ) from rfl, ← cratN_neg, cratN_one]

/-! ## U3 — super-skew for arbitrary module elements, general `n` -/

end Indexed
end InhomogeneousDeformations
