/-
Copyright (c) 2026 Zeru Zhu, Jinzheng Li, Yuanjie Ren. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zeru Zhu, Jinzheng Li, Yuanjie Ren
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.ACMax.Spectral.AlgConn
public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.LowDegreeVertex
public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.WeightedCut
public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.Ind2K2
public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.TriangleFree2K2
public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.Disconnected
public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.GoodC4
public import Tengoku.LeanPool.LeanPool.ACMax.Cuts.GoodK23

/-!
# The `n`-generic master reduction for the ACMAX conjecture

For every `n ≥ 12`, the upper-bound clause of Kolokolnikov's Conjecture 1.5
(arXiv:1412.6147) reduces to the residual predicate `ResidualCore`. The residual
hypothesis is discharged downstream in `LeanPool.ACMax.Band.Final`; the full
entry point also covers orders `4 ≤ n ≤ 11`.

## The reduction

Let `G` be a graph on `Fin n` (`n ≥ 12`) with `2(n-2)` edges.  Then `algConn G ≤ 2` follows
unconditionally in each of the following cases, via the *generic* certificate layer (each of the
lemmas below is already stated for an arbitrary finite vertex type):

1. `G` disconnected → `algConn_le_two_of_not_connected`;
2. some vertex has degree `≤ 2` → `algConn_le_two_of_low_degree_vertex`
   (the complement of the closed neighbourhood is nonempty since `n ≥ 12 > 3`);
3. otherwise `δ ≥ 3`, and the handshake `∑ deg = 4n − 8 = 3n + (n − 8)` forces at least `8`
   vertices of degree exactly `3` (`card_deg3_ge_eight`: each degree-`≥4` vertex absorbs at least
   one unit of the excess `n − 8`, so `|D| ≥ 8`);
4. a **good triangle** — three mutually adjacent vertices with
   `n·(∑deg − 6) ≤ 2·(3·(n−3))` — is a sparse weighted cut → `algConn_le_two_of_weighted_cut`
   (the triangle sends exactly `∑deg − 6` edges out).  Similarly a **good `C₄`**
   (`n·(∑deg − 8) ≤ 2·(4·(n−4))`) → `algConn_le_two_of_good_C4`, and a **good `K_{2,3}`**
   (`n·(∑deg − 12) ≤ 2·(5·(n−5))`) → `algConn_le_two_of_good_K23`.  These `n`-uniform
   thresholds are *exactly* the hypotheses the generic cut lemmas consume — no slack is given
   away (at `n = 19` they specialise to the familiar `∑deg ≤ 11 / ≤ 14 / ≤ 19`; see the
   sanity `example`s below);
5. no good triangle, and every degree-`3` vertex has a degree-`3` neighbour → the degree-`3` set
   `D` is triangle-free (a triangle in `D` has `∑deg = 9`, good for `n ≥ 6`), has min-`D`-degree
   `≥ 1` and max-`D`-degree `≤ 3`, and `|D| ≥ 8`, so `exists_induced_2K2_of_triangleFree_smalldeg`
   yields an induced `2K₂` of degree sum `12` → `algConn_le_two_of_ind_2K2`;
6. **the residual**: what survives is *exactly* `ResidualCore n G` — connected, `δ ≥ 3`,
   `2(n−2)` edges, an *isolated* degree-`3` vertex (one with no degree-`3` neighbour — the
   precise negation of the hypothesis step 5 consumes), no good triangle, no induced `2K₂` on
   degree-`3` vertices, no good `C₄`, no good `K_{2,3}`.

The conditional dispatcher `algConn_le_two_of_card_general_cond` takes the
residual case as an explicit hypothesis. `residual_algConn_le_two` in
`LeanPool.ACMax.Band.Final` proves that hypothesis from the unconditional
conjecture. The numeric examples below check the cut thresholds at order 19.
-/

@[expose] public section

namespace ACMax

/-! ## The `n`-uniform certificate predicates

Each predicate carries its degree-sum threshold in the exact `n`-uniform form consumed by the
corresponding generic cut lemma, so that the dispatch below gives away no slack. -/

open Classical in
/-- A **good triangle**: three mutually adjacent vertices whose degree sum satisfies the
`n`-uniform weighted-cut inequality `n·(∑deg − 6) ≤ 2·(3·(n−3))`.  (The triangle `A = {x,y,z}`
sends exactly `∑deg − 6` edges to `Aᶜ`, so this is precisely the hypothesis of
`algConn_le_two_of_weighted_cut`.)  At `n = 19` this is `∑deg ≤ 11`. -/
def HasGoodTriangle (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ x y z : Fin n, x ≠ y ∧ y ≠ z ∧ x ≠ z ∧
    G.Adj x y ∧ G.Adj y z ∧ G.Adj x z ∧
    n * (G.degree x + G.degree y + G.degree z - 6) ≤ 2 * (3 * (n - 3))

open Classical in
/-- An **induced `2K₂` on degree-`3` vertices**: four distinct vertices of degree `3` spanning
exactly the two edges `ab`, `cd`.  Its degree sum is `12`, so `algConn_le_two_of_ind_2K2`
applies (for every `n`). -/
def HasDeg3Ind2K2 (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d : Fin n, ({a, b, c, d} : Finset (Fin n)).card = 4 ∧
    G.degree a = 3 ∧ G.degree b = 3 ∧ G.degree c = 3 ∧ G.degree d = 3 ∧
    G.Adj a b ∧ G.Adj c d ∧ ¬G.Adj a c ∧ ¬G.Adj a d ∧ ¬G.Adj b c ∧ ¬G.Adj b d

open Classical in
/-- A **good `C₄`**: an induced `4`-cycle `a-b-c-d-a` with the `n`-uniform threshold
`n·(∑deg − 8) ≤ 2·(4·(n−4))` — exactly the hypothesis of `algConn_le_two_of_good_C4`.
At `n = 19` this is `∑deg ≤ 14`. -/
def HasGoodC4 (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d : Fin n, ({a, b, c, d} : Finset (Fin n)).card = 4 ∧
    G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a ∧ ¬G.Adj a c ∧ ¬G.Adj b d ∧
    n * (G.degree a + G.degree b + G.degree c + G.degree d - 8) ≤ 2 * (4 * (n - 4))

open Classical in
/-- A **good `K_{2,3}`**: an induced complete bipartite `K_{2,3}` (parts `{a,b}`, `{c,d,e}`)
with the `n`-uniform threshold `n·(∑deg − 12) ≤ 2·(5·(n−5))` — exactly the hypothesis of
`algConn_le_two_of_good_K23`.  At `n = 19` this is `∑deg ≤ 19`. -/
def HasGoodK23 (n : ℕ) (G : SimpleGraph (Fin n)) : Prop :=
  ∃ a b c d e : Fin n, ({a, b, c, d, e} : Finset (Fin n)).card = 5 ∧
    G.Adj a c ∧ G.Adj a d ∧ G.Adj a e ∧ G.Adj b c ∧ G.Adj b d ∧ G.Adj b e ∧
    ¬G.Adj a b ∧ ¬G.Adj c d ∧ ¬G.Adj c e ∧ ¬G.Adj d e ∧
    n * (G.degree a + G.degree b + G.degree c + G.degree d + G.degree e - 12)
      ≤ 2 * (5 * (n - 5))

/-! ## The residual predicate -/

open Classical in
/-- **The residual core** — exactly the class of graphs that survives the generic reduction
steps 1–5 (see the module docstring).  Every field is the *precise* negation of the branch
condition the corresponding step consumes; nothing is weakened and nothing extraneous is added:

* `connected` — step 1 (disconnected graphs are closed by `algConn_le_two_of_not_connected`);
* `min_degree` — step 2 (a degree-`≤2` vertex is closed by `algConn_le_two_of_low_degree_vertex`);
* `edge_card`, `n_ge` — the standing hypotheses (from which `≥ 8` degree-`3` vertices follow,
  `card_deg3_ge_eight`);
* `no_good_triangle` — step 4a (weighted cut on a triangle);
* `iso_deg3` — the negation of "every degree-`3` vertex has a degree-`3` neighbour"
  (step 5 consumes that hypothesis to extract an induced `2K₂` inside the degree-`3` set);
* `no_deg3_ind2K2` — step 5's certificate directly (an induced `2K₂` on degree-`3` vertices
  closes the graph regardless of how it was found);
* `no_good_C4`, `no_good_K23` — steps 4b, 4c.

Every such residual graph is closed by `residual_algConn_le_two` in
`LeanPool.ACMax.Band.Final`. -/
structure ResidualCore (n : ℕ) (G : SimpleGraph (Fin n)) : Prop where
  n_ge : 12 ≤ n
  edge_card : G.edgeFinset.card = 2 * (n - 2)
  connected : G.Connected
  min_degree : ∀ v : Fin n, 3 ≤ G.degree v
  iso_deg3 : ∃ t : Fin n, G.degree t = 3 ∧ ∀ w : Fin n, G.Adj t w → G.degree w ≠ 3
  no_good_triangle : ¬HasGoodTriangle n G
  no_deg3_ind2K2 : ¬HasDeg3Ind2K2 n G
  no_good_C4 : ¬HasGoodC4 n G
  no_good_K23 : ¬HasGoodK23 n G

/-! ## Step 3: the handshake counting lemma -/

open Classical in
/-- **Handshake counting.**  If every degree is `≥ 3` and `G` has `2(n−2)` edges, then at least
`8` vertices have degree exactly `3`: with `D = {deg = 3}` and `H = {deg ≥ 4}`,
`3|D| + 4|H| ≤ ∑deg = 4n − 8` and `|D| + |H| = n` give `|D| ≥ 8`. -/
theorem card_deg3_ge_eight (n : ℕ) (hn : 8 ≤ n) (G : SimpleGraph (Fin n))
    (hm : G.edgeFinset.card = 2 * (n - 2)) (h3 : ∀ v : Fin n, 3 ≤ G.degree v) :
    8 ≤ (Finset.univ.filter (fun v : Fin n => G.degree v = 3)).card := by
  classical
  set D := Finset.univ.filter (fun v : Fin n => G.degree v = 3) with hD
  set H := Finset.univ.filter (fun v : Fin n => 4 ≤ G.degree v) with hH
  have hsum : ∑ v : Fin n, G.degree v = 2 * (2 * (n - 2)) := by
    rw [SimpleGraph.sum_degrees_eq_twice_card_edges, hm]
  have hmemD : ∀ v : Fin n, v ∈ D ↔ G.degree v = 3 := by
    intro v; rw [hD]; simp
  have hmemH : ∀ v : Fin n, v ∈ H ↔ 4 ≤ G.degree v := by
    intro v; rw [hH]; simp
  have hDH : ∀ v : Fin n, v ∈ D ∨ v ∈ H := by
    intro v
    rcases Nat.lt_or_ge (G.degree v) 4 with hlt | hge
    · exact Or.inl ((hmemD v).mpr (by have := h3 v; omega))
    · exact Or.inr ((hmemH v).mpr hge)
  have hdisj : Disjoint D H := by
    rw [Finset.disjoint_left]
    intro v hvD hvH
    have h1 := (hmemD v).mp hvD
    have h2 := (hmemH v).mp hvH
    omega
  have hunion : D ∪ H = Finset.univ := by
    ext v
    simp only [Finset.mem_union, Finset.mem_univ, iff_true]
    exact hDH v
  have hsumpart : ∑ v ∈ D, G.degree v + ∑ v ∈ H, G.degree v = 2 * (2 * (n - 2)) := by
    rw [← Finset.sum_union hdisj, hunion]; exact hsum
  have hsumD : ∑ v ∈ D, G.degree v = 3 * D.card := by
    rw [Finset.sum_congr rfl (fun v hv => (hmemD v).mp hv), Finset.sum_const,
      smul_eq_mul, mul_comm]
  have hsumH : H.card * 4 ≤ ∑ v ∈ H, G.degree v := by
    have hb : ∀ x ∈ H, 4 ≤ (fun v => G.degree v) x := fun i hi => (hmemH i).mp hi
    have h := Finset.card_nsmul_le_sum H (fun v => G.degree v) 4 hb
    simpa [smul_eq_mul] using h
  have hpart2 : D.card + H.card = n := by
    have h := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at h
    omega
  rw [hsumD] at hsumpart
  omega

/-! ## The master reduction -/

/-! ## Sanity checks at `n = 19`

The `n`-uniform thresholds specialize at `n = 19` to these numerical bounds: -/

/-- Good-triangle threshold at `n = 19`: `19·(S−6) ≤ 2·(3·16) = 96 ↔ S ≤ 11`. -/
example : ∀ S : ℕ, 19 * (S - 6) ≤ 2 * (3 * (19 - 3)) ↔ S ≤ 11 := by intro S; omega

/-- Good-`C₄` threshold at `n = 19`: `19·(S−8) ≤ 2·(4·15) = 120 ↔ S ≤ 14`. -/
example : ∀ S : ℕ, 19 * (S - 8) ≤ 2 * (4 * (19 - 4)) ↔ S ≤ 14 := by intro S; omega

/-- Good-`K_{2,3}` threshold at `n = 19`: `19·(S−12) ≤ 2·(5·14) = 140 ↔ S ≤ 19`. -/
example : ∀ S : ℕ, 19 * (S - 12) ≤ 2 * (5 * (19 - 5)) ↔ S ≤ 19 := by intro S; omega

end ACMax
