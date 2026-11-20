/-
OEIS A347722: definitions shared by the proof files.

Reader-facing: `verts`, `Adj`, `Irredundant`, `a` (the sequence), and `h`, `f`, `formula`.
Internal to the proof: `deg`, `Star`, `Unc`, `PM`, `Idem`, `BadAt`, `IsoAt`, `Good`, `D`, `F`,
`edgeSet`.
-/
import Tengoku.Seed.Algebra.BigOperators.Ring.Finset
import Tengoku.Seed.Algebra.Ring.Parity
import Tengoku.Seed.Data.Finset.Powerset
import Tengoku.Seed.Data.Fintype.Pi
import Tengoku.Seed.Data.Fintype.Powerset
import Tengoku.Seed.Data.Nat.Choose.Basic
import Tengoku.Seed.Data.Nat.Factorial.DoubleFactorial
import Tengoku.Seed.Order.Interval.Finset.Nat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace A347722

/-! ## The sequence, taken literally from the OEIS name -/

/-- Vertices of the n-triangular graph `T(n)`: the 2-element subsets of `{0, ..., n-1}`.-/
def verts (n : ℕ) : Finset (Finset (Fin n)) := (Finset.univ : Finset (Fin n)).powersetCard 2

/-- Two vertices of `T(n)` are adjacent iff the two subsets have exactly one common element.-/
def Adj {n : ℕ} (e f : Finset (Fin n)) : Prop := (e ∩ f).card = 1

instance {n : ℕ} (e f : Finset (Fin n)) : Decidable (Adj e f) := by
  unfold Adj
  infer_instance

/-- A set `S` of vertices is irredundant iff every `e ∈ S` has a private closed neighbour:
a vertex `f` of the graph in the closed neighbourhood of `e` (so `f = e` or `f` adjacent to
`e`) that is in the closed neighbourhood of no other member of `S`.-/
def Irredundant {n : ℕ} (S : Finset (Finset (Fin n))) : Prop :=
  ∀ e ∈ S, ∃ f ∈ verts n, (f = e ∨ Adj e f) ∧ ∀ g ∈ S, g ≠ e → ¬ (f = g ∨ Adj g f)

instance {n : ℕ} (S : Finset (Finset (Fin n))) : Decidable (Irredundant S) := by
  unfold Irredundant
  infer_instance

/-- OEIS A347722 (offset 2): "Number of irredundant sets in the n-triangular (Johnson) graph."
The empty set is irredundant and is counted.-/
def a (n : ℕ) : ℕ := ((verts n).powerset.filter Irredundant).card

/-! ## The claimed closed formula -/

/-- `h m = Sum_{k=0..m} C(m,k) k^(m-k)`, the number of idempotent maps on `m` points
(OEIS A000248).-/
def h (m : ℕ) : ℕ := ∑ k ∈ Finset.range (m + 1), m.choose k * k ^ (m - k)

/-- `f m = Sum_{j=0..m/2} (-1)^j C(m,2j) (2j-1)!! h(m-2j)`, the number of star forests on `m`
labelled vertices (isolated vertices allowed). `Nat.doubleFactorial (2*0-1) = 0!! = 1`.-/
def f (m : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (m / 2 + 1),
    (-1) ^ j * (m.choose (2 * j) : ℤ) * (Nat.doubleFactorial (2 * j - 1) : ℤ) * (h (m - 2 * j) : ℤ)

/-- `a(n) = [n even] (n-1)!! + Sum_{i=1..n} (-1)^(i+1) C(n,i) f(n-i)`.-/
def formula (n : ℕ) : ℤ :=
  (if Even n then (Nat.doubleFactorial (n - 1) : ℤ) else 0)
    + ∑ i ∈ Finset.Icc 1 n, (-1) ^ (i + 1) * (n.choose i : ℤ) * f (n - i)

/-! ## Intermediate notions used by the proof: edge sets of `K_n` -/

/-- Number of members of `S` containing `v` (the degree of `v` in the edge set `S`).-/
def deg {n : ℕ} (S : Finset (Finset (Fin n))) (v : Fin n) : ℕ := (S.filter fun e => v ∈ e).card

/-- Every edge has an endpoint of degree 1: `S` is a star forest.-/
def Star {n : ℕ} (S : Finset (Finset (Fin n))) : Prop := ∀ e ∈ S, ∃ v ∈ e, deg S v = 1

/-- Some vertex lies on no edge.-/
def Unc {n : ℕ} (S : Finset (Finset (Fin n))) : Prop := ∃ v : Fin n, deg S v = 0

/-- Every vertex lies on exactly one edge: `S` is a perfect matching.-/
def PM {n : ℕ} (S : Finset (Finset (Fin n))) : Prop := ∀ v : Fin n, deg S v = 1

instance {n : ℕ} (S : Finset (Finset (Fin n))) : Decidable (Star S) := by
  unfold Star
  infer_instance

instance {n : ℕ} (S : Finset (Finset (Fin n))) : Decidable (Unc S) := by
  unfold Unc
  infer_instance

instance {n : ℕ} (S : Finset (Finset (Fin n))) : Decidable (PM S) := by
  unfold PM
  infer_instance

/-! ## Intermediate notions used by the proof: idempotent maps -/

/-- `g` is idempotent. Its fixed points are the centres, every other point is a leaf of the
centre it is mapped to.-/
def Idem {n : ℕ} (g : Fin n → Fin n) : Prop := ∀ v, g (g v) = g v

/-- `c` is a fixed point with exactly one other preimage `u`, and `u < c`. (A single edge has
two possible centres; the map with the larger one as centre is the bad one.)-/
def BadAt {n : ℕ} (g : Fin n → Fin n) (c : Fin n) : Prop :=
  g c = c ∧ ∃ u, u < c ∧ g u = c ∧ ∀ w, g w = c → w = u ∨ w = c

/-- `v` is a fixed point with no other preimage.-/
def IsoAt {n : ℕ} (g : Fin n → Fin n) (v : Fin n) : Prop := ∀ w, g w = v ↔ w = v

/-- Idempotent with no bad fixed point: these maps correspond one to one to star forests.-/
def Good {n : ℕ} (g : Fin n → Fin n) : Prop := Idem g ∧ ∀ v, ¬ BadAt g v

instance {n : ℕ} (g : Fin n → Fin n) : Decidable (Idem g) := by
  unfold Idem
  infer_instance

instance {n : ℕ} (g : Fin n → Fin n) (c : Fin n) : Decidable (BadAt g c) := by
  unfold BadAt
  infer_instance

instance {n : ℕ} (g : Fin n → Fin n) (v : Fin n) : Decidable (IsoAt g v) := by
  unfold IsoAt
  infer_instance

instance {n : ℕ} (g : Fin n → Fin n) : Decidable (Good g) := by
  unfold Good
  infer_instance

/-- Idempotent maps on `n` points in which none of the first `c` points is bad.-/
def D (n c : ℕ) : ℕ :=
  (Finset.univ.filter fun g : Fin n → Fin n =>
    Idem g ∧ ∀ v : Fin n, v.val < c → ¬ BadAt g v).card

/-- Good maps on `n` points in which none of the first `d` points is isolated.-/
def F (n d : ℕ) : ℕ :=
  (Finset.univ.filter fun g : Fin n → Fin n =>
    Good g ∧ ∀ v : Fin n, v.val < d → ¬ IsoAt g v).card

/-- The edge set of a map: one edge `{v, g v}` for every non-fixed point `v`.-/
def edgeSet {n : ℕ} (g : Fin n → Fin n) : Finset (Finset (Fin n)) :=
  (Finset.univ.filter fun v => g v ≠ v).image fun v => {v, g v}

end A347722
