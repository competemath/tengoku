import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.Degree
import Tengoku.Seed.Algebra.Polynomial.BigOperators
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# The polynomials s_{t,n} on LN97 p. 307

After reducing powers of a field element modulo the polynomial `B`,
LN97 writes

    s_{t,n}(x) = Σ_i Σ_j b_{t,i} e_{i,j,n}(x) x^j.

The crucial elementary estimate is

    deg s_{t,n} ≤ max deg(e_{i,j,n}) + u.

This file formalizes that polynomial and degree estimate.  The
coefficients `b_{t,i}` are arbitrary field scalars here; their special
origin from reduction modulo `B` is irrelevant for this step.
-/

/-- The polynomial `s_{t,n}` with the derivative index `n` suppressed
from the notation of the coefficient family `e`.-/
noncomputable def stepanovSTN
    {m r u : ℕ}
    (b : Fin r → Fin m → F)
    (e : Fin m → Fin (u + 1) → Polynomial F)
    (t : Fin r) :
    Polynomial F :=
  Finset.univ.sum (fun i : Fin m =>
    Finset.univ.sum (fun j : Fin (u + 1) =>
      C (b t i) * e i j * X ^ (j : ℕ)))

omit [Fintype F] in
/-- If every `e_{ij,n}` has degree at most `Edeg`, then
`deg s_{t,n} ≤ Edeg + u`.

Taking `Edeg = q/m + n(k-1) - 1` gives the bound immediately below
equation (6.25) in LN97.
@isnad1 id=le.1h8v.s6.7e332cbc5bc6 from=translated src=- shape=298185ec vocab=ba49b90e
-/
theorem stepanovSTN_natDegree_le
    {m r u Edeg : ℕ}
    (b : Fin r → Fin m → F)
    (e : Fin m → Fin (u + 1) → Polynomial F)
    (he : ∀ i j, (e i j).natDegree ≤ Edeg)
    (t : Fin r) :
    (stepanovSTN b e t).natDegree ≤ Edeg + u := by
  have hinner :
      ∀ i : Fin m,
        (Finset.univ.sum (fun j : Fin (u + 1) =>
          C (b t i) * e i j * X ^ (j : ℕ))).natDegree
          ≤ Edeg + u := by
    intro i
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro j hj
    have hce :
        (C (b t i) * e i j).natDegree ≤ Edeg := by
      calc
        (C (b t i) * e i j).natDegree
            ≤ (C (b t i)).natDegree + (e i j).natDegree :=
          natDegree_mul_le_add (F := F) _ _
        _ ≤ 0 + Edeg := by
          exact Nat.add_le_add (by simp) (he i j)
        _ = Edeg := by simp
    have hjle : (j : ℕ) ≤ u := by
      omega
    have hx :
        (X ^ (j : ℕ) : Polynomial F).natDegree ≤ u := by
      rw [Polynomial.natDegree_pow]
      simpa using hjle
    exact le_trans
      (natDegree_mul_le_add
        (F := F) (C (b t i) * e i j)
          (X ^ (j : ℕ) : Polynomial F))
      (Nat.add_le_add hce hx)
  unfold stepanovSTN
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  exact hinner i

end LN97
end MagicSquares
