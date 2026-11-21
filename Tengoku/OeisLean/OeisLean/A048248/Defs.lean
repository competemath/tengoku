/-
OEIS A048248: definitions shared by the proof files.

`OeisLean/A048248/Walk.lean` shows that the traces of `n`-step walks are exactly the lists
`l` with `Valid n l`; `OeisLean/A048248/Count.lean` counts those lists.
-/
import Tengoku.Seed.Algebra.Ring.Parity
import Tengoku.Seed.Data.Fintype.Pi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace A048248

/-! ## The sequence, taken literally from the OEIS entry -/

/-- Number of times the walk `w`, started at position `pos`, uses the edge between `j` and
`j + 1`. `true` is a step `+1` (it uses the edge above the current position), `false` a step
`-1` (it uses the edge below).-/
def edgeCount : List Bool → ℤ → ℤ → ℕ
  | [], _, _ => 0
  | true :: w, pos, j => (if pos = j then 1 else 0) + edgeCount w (pos + 1) j
  | false :: w, pos, j => (if pos - 1 = j then 1 else 0) + edgeCount w (pos - 1) j

/-- The trace of an `n`-step walk from `0`: the positive edge counts, read from left to right.
An `n`-step walk only uses edges in `[-n, n)`. Dropping the zero counts is what "ignoring
translations" means (OEIS comment: "the sequence of visits <0,1,2,1,0> has trace (2,2), as do
<0,-1,0,1,0>, <0,-1,-2,-1,0>"), and is what the Mathematica program in the entry does.-/
def trace (n : ℕ) (w : List Bool) : List ℕ :=
  ((List.range (2 * n)).map fun i : ℕ => edgeCount w 0 ((i : ℤ) - n)).filter (0 < ·)

/-- OEIS A048248 (offset 1): "Possible traces of n-step walks on 1-D lattice, ignoring
translations." OEIS comment: "Trace as used here refers to the number of times an edge is used
in the walk."-/
def a (n : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → Bool)).image fun f => trace n (List.ofFn f)).card

/-! ## The intermediate notion linking the two halves of the proof -/

/-- `Valid n l`: `l` is a list of positive integers with sum `n` whose parities read
even, ..., even, odd, ..., odd, even, ..., even (each of the three blocks may be empty).-/
def Valid (n : ℕ) (l : List ℕ) : Prop :=
  l.sum = n ∧ (∀ x ∈ l, 0 < x) ∧
    ∃ e₁ o e₂ : List ℕ, l = e₁ ++ o ++ e₂ ∧
      (∀ x ∈ e₁, Even x) ∧ (∀ x ∈ o, Odd x) ∧ (∀ x ∈ e₂, Even x)

end A048248
