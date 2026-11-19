import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.STNReduction
import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Lemma652.FiniteFieldEval
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-!
# From the equations s_{t,n}=0 to vanishing after evaluation

This is the payoff of the power-reduction / regrouping calculation.
If all of the polynomials `s_t` vanish identically, then at every `c`
for which `B(g(c))=0`, the corresponding double sum in (6.25) vanishes.
-/

omit [Fintype F] [DecidableEq F] in
/-- Vanishing of all `s_t` forces the reduced double sum to vanish at
any point whose `g(c)` is a root of `B`.
@isnad1 id=eq.5h8v.s8.9dc2533a49d0 from=translated src=- shape=e3c80e40 vocab=7635a57c
-/
theorem eval_doubleSum_eq_zero_of_stepanovSTN_eq_zero
    {m r u : ℕ}
    (B : Polynomial F)
    (hB : B.Monic)
    (hr : 0 < r)
    (hdeg : B.natDegree = r)
    (e : Fin m → Fin (u + 1) → Polynomial F)
    (g : Polynomial F)
    (c : F)
    (hc : B.IsRoot (eval c g))
    (hstn : ∀ t : Fin r,
      stepanovSTN
        (fun tt ii =>
          powerReductionCoeff B (ii : ℕ) (tt : ℕ))
        e t = 0) :
    (∑ i : Fin m,
      ∑ j : Fin (u + 1),
        eval c (e i j) *
          (eval c g) ^ (i : ℕ) * c ^ (j : ℕ)) = 0 := by
  have hred :=
    sum_e_mul_pow_eq_sum_STN_mul_pow
      (F := F) B hB hr hdeg e c (eval c g) hc
  rw [hred]
  apply Finset.sum_eq_zero
  intro t ht
  rw [hstn t]
  simp

omit [DecidableEq F] in
/-- The exact Frobenius-evaluation form arising from (6.25): the factor
`(c^q)^j` may be replaced by `c^j`.
@isnad1 id=eq.5h8v.s8.bfe733ff9328 from=translated src=- shape=4c721e8b vocab=d743430d
-/
theorem eval_doubleSum_frobenius_eq_zero_of_stepanovSTN_eq_zero
    {m r u : ℕ}
    (B : Polynomial F)
    (hB : B.Monic)
    (hr : 0 < r)
    (hdeg : B.natDegree = r)
    (e : Fin m → Fin (u + 1) → Polynomial F)
    (g : Polynomial F)
    (c : F)
    (hc : B.IsRoot (eval c g))
    (hstn : ∀ t : Fin r,
      stepanovSTN
        (fun tt ii =>
          powerReductionCoeff B (ii : ℕ) (tt : ℕ))
        e t = 0) :
    (∑ i : Fin m,
      ∑ j : Fin (u + 1),
        eval c (e i j) *
          (eval c g) ^ (i : ℕ) *
          (c ^ Fintype.card F) ^ (j : ℕ)) = 0 := by
  simpa [finiteField_pow_card] using
    (eval_doubleSum_eq_zero_of_stepanovSTN_eq_zero
      (F := F) B hB hr hdeg e g c hc hstn)

end LN97
end MagicSquares
