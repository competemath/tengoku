/-
OEIS A307917: definitions shared by the proof files.

Reader-facing: `V`, `Adj`, `dirPaths`, `a` (the sequence) and `formula`.
Internal to the proof: `Sp` and `B`.
-/
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Data.Fintype.Pi
import Tengoku.Seed.Data.Fintype.Prod
import Tengoku.Seed.Data.Nat.Choose.Basic
import Tengoku.Seed.Data.Nat.Factorial.Basic
import Tengoku.Seed.Order.Interval.Finset.Nat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace A307917

/-! ## The sequence, taken literally from the OEIS name -/

/-- Vertices of the n-crown graph: two copies of `{0, ..., n-1}`; the `Bool` is the side.-/
abbrev V (n : ℕ) := Bool × Fin n

/-- `(s, i)` and `(t, j)` are adjacent iff they lie on different sides and `i ≠ j`: the
complete bipartite graph `K_{n,n}` minus a perfect matching.-/
def Adj {n : ℕ} (u v : V n) : Prop := u.1 ≠ v.1 ∧ u.2 ≠ v.2

instance {n : ℕ} (u v : V n) : Decidable (Adj u v) := by
  unfold Adj
  infer_instance

/-- Directed paths on `L` vertices: sequences of `L` distinct vertices in which consecutive
vertices are adjacent.-/
def dirPaths (n L : ℕ) : Finset (Fin L → V n) :=
  Finset.univ.filter fun f =>
    Function.Injective f ∧ ∀ i j : Fin L, i.val + 1 = j.val → Adj (f i) (f j)

/-- OEIS A307917 (offset 1): "Number of (undirected) paths in the n-crown graph."

A path has at least one edge, hence at least 2 vertices, and at most all `2n` vertices. Each
undirected path is traversed in exactly two directions, hence the division by 2.-/
def a (n : ℕ) : ℕ := (∑ L ∈ Finset.Icc 2 (2 * n), (dirPaths n L).card) / 2

/-! ## The claimed closed formula -/

/-- `a(n) = Sum_{k=1..n} n!/(n-k)! * Sum_{j=0..k} (-1)^j C(2k-j, j) (n-j)!/(n-k)!`
`     + Sum_{k=1..n-1} n!/(n-k-1)! * Sum_{j=0..k} (-1)^j C(2k+1-j, j) (n-j)!/(n-k)!`.
The first sum counts the paths on `2k` vertices, the second those on `2k+1` vertices.
`Nat.descFactorial m r = m (m-1) ... (m-r+1)`, so `n.descFactorial k = n!/(n-k)!` and
`(n-j).descFactorial (k-j) = (n-j)!/(n-k)!` for `j ≤ k ≤ n`.-/
def formula (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.Icc 1 n, (n.descFactorial k : ℤ) *
      ∑ j ∈ Finset.range (k + 1),
        (-1) ^ j * ((2 * k - j).choose j : ℤ) * ((n - j).descFactorial (k - j) : ℤ)
  + ∑ k ∈ Finset.Icc 1 (n - 1), (n.descFactorial (k + 1) : ℤ) *
      ∑ j ∈ Finset.range (k + 1),
        (-1) ^ j * ((2 * k + 1 - j).choose j : ℤ) * ((n - j).descFactorial (k - j) : ℤ)

/-! ## Intermediate notions used by the proof -/

/-- Positions of equal parity carry distinct values. (Along a path that starts on a fixed
side, positions of equal parity are the vertices on one side.)-/
def Sp {n L : ℕ} (z : Fin L → Fin n) : Prop :=
  ∀ i j : Fin L, i ≠ j → i.val % 2 = j.val % 2 → z i ≠ z j

instance {n L : ℕ} (z : Fin L → Fin n) : Decidable (Sp z) := by
  unfold Sp
  infer_instance

/-- `B n L c`: the number of `z : Fin L → Fin n` with `Sp z` in which the first `c`
neighbouring pairs `(z i, z (i+1))`, `i < c`, are unequal.-/
def B (n L c : ℕ) : ℕ :=
  (Finset.univ.filter fun z : Fin L → Fin n =>
    Sp z ∧ ∀ i j : Fin L, i.val + 1 = j.val → i.val < c → z i ≠ z j).card

end A307917
