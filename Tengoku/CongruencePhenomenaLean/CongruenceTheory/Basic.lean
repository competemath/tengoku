import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Formalization of the universal cycle-index polynomials `C_n` from
`A_General_Theory_of_Congruence_Phenomena_I.tex` (the "General Theory of
Congruence Phenomena" manuscript), Section 2-3.

We take Proposition `prop:recurrence` (the falling-factorial recurrence) as
the *definition* of `C n`, exactly as the manuscript's own proof of
Theorem `thm:universal` does: "Work first in `R = Z[X_1,X_2,...]`... The
[recurrence], with `w_j = X_j`, is an identity in `R`."  The manuscript
separately proves (Proposition `prop:cycle-index`, via differentiating the
EGF) that this recurrence characterizes the same object as the combinatorial
cycle-index sum; we do not re-derive that equivalence here.
-/

open Finset

namespace CongruenceTheory

/-- The falling factorial `n(n-1)...(n-r+1)`, valued in `ℤ` so that no
truncation issues arise; matches `\fall{n}{r}` in the manuscript.-/
def fall (n r : ℕ) : ℤ := ∏ i ∈ range r, ((n : ℤ) - i)

/--
@isnad1 id=eq.0h1v.s4.00fe98b40240 from=translated src=- shape=8fc7241c vocab=a76bf9a6
-/
@[simp] lemma fall_zero (n : ℕ) : fall n 0 = 1 := by simp [fall]

/--
@isnad1 id=eq.0h2v.s5.7b9f5cfda903 from=translated src=- shape=6831156f vocab=fa0fd238
-/
lemma fall_succ (n r : ℕ) :
    fall n (r + 1) = fall n r * ((n : ℤ) - r) := by
  simp [fall, Finset.prod_range_succ]

/-- The universal cycle-index polynomial `C_n = C_n(X_1, X_2, ...)`, defined
by the falling-factorial recurrence (`eq:recurrence` in the manuscript,
Proposition `prop:recurrence`). Variables are indexed by `ℕ`; we only ever
use `X j` for `j ≥ 1`, matching the manuscript's `X_j`.-/
noncomputable def C : ℕ → MvPolynomial ℕ ℤ
  | 0 => 1
  | n + 1 =>
      ∑ r ∈ range (n + 1),
        (fall n r : MvPolynomial ℕ ℤ) * (MvPolynomial.X (r + 1) * C (n - r))
termination_by n => n
decreasing_by all_goals omega

/--
@isnad1 id=eq.0h0v.s5.9904af070e8a from=translated src=- shape=978b4adc vocab=ab9048ca
-/
lemma C_zero : C 0 = 1 := by simp [C]

/--
@isnad1 id=eq.0h1v.s7.d361183177f1 from=translated src=- shape=ad8c62e1 vocab=78b2f738
-/
lemma C_succ (n : ℕ) :
    C (n + 1) =
      ∑ r ∈ range (n + 1),
        (fall n r : MvPolynomial ℕ ℤ) * (MvPolynomial.X (r + 1) * C (n - r)) := by
  conv_lhs => rw [C]

-- Sanity check: `C 1 = X_1`.

end CongruenceTheory
