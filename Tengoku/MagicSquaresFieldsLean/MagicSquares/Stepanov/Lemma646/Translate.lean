import Tengoku.Seed.Algebra.Polynomial.Taylor
import Tengoku.Seed.Algebra.Polynomial.Roots
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

variable {F : Type*} [Field F] [Fintype F]

/-!
# The translation reduction in the last paragraph of LN97 Lemma 6.46

The proof first treats the case `f(0) ≠ 0`.  For a general nonzero
polynomial `f` of degree `< q`, LN97 chooses `c ∈ F_q` with `f(c) ≠ 0`
and replaces `f(x)` by `f(x+c)`.

Mathlib's `Polynomial.taylor c f` is precisely the translated polynomial
`f(X+c)`.  Its constant coefficient is `f(c)`, and translation preserves
natural degree.
-/

/-- A nonzero polynomial of degree strictly smaller than the cardinality
of a finite field cannot vanish at every field element.
@isnad1 id=ex.2h2v.s6.23c56e6058be from=translated src=- shape=6e00e53c vocab=c71ef627
-/
theorem exists_eval_ne_zero_of_natDegree_lt_card
    (P : Polynomial F)
    (hP : P ≠ 0)
    (hdeg : P.natDegree < Fintype.card F) :
    ∃ c : F, eval c P ≠ 0 := by
  classical
  by_contra h
  have hall : ∀ c : F, eval c P = 0 := by
    intro c
    by_contra hc
    exact h ⟨c, hc⟩
  have hzero : P = 0 :=
    Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
      P
      (f := fun c : F => c)
      Function.injective_id
      hall
      hdeg
  exact hP hzero

/-- The precise translation step needed in Lemma 6.46:
there is a translate with nonzero constant coefficient, and its degree
is unchanged.
@isnad1 id=ex.2h2v.s9.a3c56cfd7b2a from=translated src=- shape=86e8b9f7 vocab=40a6794e
-/
theorem exists_taylor_constant_ne_zero_same_natDegree
    (P : Polynomial F)
    (hP : P ≠ 0)
    (hdeg : P.natDegree < Fintype.card F) :
    ∃ c : F,
      ((taylor c) P).coeff 0 ≠ 0 ∧
      ((taylor c) P).natDegree = P.natDegree := by
  obtain ⟨c, hc⟩ :=
    exists_eval_ne_zero_of_natDegree_lt_card
      P hP hdeg
  refine ⟨c, ?_, ?_⟩
  · simpa using hc
  · exact Polynomial.natDegree_taylor P c

/-- In particular, the translated polynomial itself is nonzero.
@isnad1 id=ex.2h2v.s9.31c0affc16f5 from=translated src=- shape=a395b7d0 vocab=40a6794e
-/
theorem exists_taylor_nonzero_constant
    (P : Polynomial F)
    (hP : P ≠ 0)
    (hdeg : P.natDegree < Fintype.card F) :
    ∃ c : F,
      (taylor c) P ≠ 0 ∧
      ((taylor c) P).coeff 0 ≠ 0 := by
  obtain ⟨c, hc0, hdeg'⟩ :=
    exists_taylor_constant_ne_zero_same_natDegree
      P hP hdeg
  refine ⟨c, ?_, hc0⟩
  intro hz
  rw [hz] at hc0
  simp at hc0

end LN97
end MagicSquares
