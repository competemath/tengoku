import Tengoku.GrunbaumLean.FranklFuredi.Remarks

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# P. Frankl, Z. Füredi — *An exact result for 3-graphs* (Discrete Math. 50 (1984) 323–328)

This file collects the statements of the paper, in the order in which they appear, as proved
in the other files of the project.  Nothing here uses `sorry`; run `#print axioms` on any of
them to see that only the standard axioms `propext`, `Classical.choice`, `Quot.sound` are used.

Conventions:
* a 3-graph on a finite vertex type `V` is `ThreeGraph V` (a finset of 3-element finsets);
* a partition `V = V₁ ∪ ⋯ ∪ V₆` is a map `f : V → Fin 6` (classes may be empty);
* the plane is `ℝ × ℝ`, the unit circle is `{(x, y) | x² + y² = 1}`;
* "isomorphic to one of the 3-graphs in Example 1 or 2" becomes "equal to one of them", since
  the examples are defined on `V` itself, for an arbitrary partition resp. placement.
-/

open Finset

namespace FranklFuredi.Paper

open FranklFuredi

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## §1  Definitions and examples -/

/-- "Any 4 points span 2 edges in `S(6)`."
@isnad1 id=eq.1h1v.s5.a8658629ebbd from=translated src=- shape=c50c4a83 vocab=094b42af
-/
theorem S6_any_four_points_span_two_edges :
    ∀ W : Finset (Fin 6), W.card = 4 → (S6.spanned W).card = 2 :=
  S6_spanned_four

/-- "If we choose a partition satisfying `|Vᵢ| ≥ ⌊n/6⌋`, `H_S` has more than `10⌊n/6⌋³`
edges" (precisely: at least).
@isnad1 id=le.1h2v.s6.4922803b7465 from=translated src=- shape=513e0b27 vocab=39743883
-/
theorem HS_many_edges (f : V → Fin 6) (hf : ∀ i, Fintype.card V / 6 ≤ partSizes f i) :
    10 * (Fintype.card V / 6) ^ 3 ≤ (HS f).edges.card :=
  HS_card_ge f hf

/-- "… which is more than `n³/24`, disproving Turán's conjecture": `m(n,3,4,3) > n³/24` for all
`n ≥ 25`.
@isnad1 id=lt.1h1v.s6.94c5b4089743 from=translated src=- shape=7534e79d vocab=9748202d
-/
theorem Turan_conjecture_disproved (n : ℕ) (hn : 25 ≤ n) :
    (n : ℝ) ^ 3 / 24 < mExtremal n 3 4 3 :=
  turan_conjecture_false n hn

/-- Example 1: "in `H_S` any four points span either zero or two edges".
@isnad1 id=fourpoin.0h2v.s4.b3c1e865787b from=translated src=- shape=97e97d05 vocab=ac5db7d8
-/
theorem example1_property (f : V → Fin 6) : (HS f).FourPointProperty :=
  HS_fourPointProperty f

/-- Example 2: "the fact that in this 3-graph any 4 points span 0 or 2 edges can be verified
easily".
@isnad1 id=fourpoin.1h2v.s4.bc5279c9f67c from=translated src=- shape=fcef3e1a vocab=847237e5
-/
theorem example2_property (p : V → ℝ × ℝ) (hp : IsCircleConfig p) :
    (circleGraph p).FourPointProperty :=
  circleGraph_fourPointProperty hp

/-- **Theorem 1.**  Suppose `H = (V, 𝓔)` is a 3-graph in which any 4 points span 0 or 2 edges.
Then `H` is isomorphic to one of the 3-graphs in Examples 1 or 2.
@isnad1 id=or.1h2v.s6.d3826a74fcbf from=translated src=- shape=39446920 vocab=c60ccbae
-/
theorem Theorem1 (H : ThreeGraph V) (hH : H.FourPointProperty) :
    (∃ f : V → Fin 6, H = HS f) ∨ (∃ p : V → ℝ × ℝ, IsCircleConfig p ∧ H = circleGraph p) :=
  theorem1 H hH

/-- **Theorem 2.**  Suppose that `H = (V, 𝓔)`, `|V| = n ≥ 5` and any 4 points of `V` span 0 or
2 edges.  Then `max |𝓔|` is attained exactly for `H` of the form `H_S` for some equipartition,
i.e. `⌊n/6⌋ ≤ |Vᵢ| ≤ ⌈n/6⌉`.

(Formally: the maximum is `ex(n)`, it is attained by an equipartition `H_S`, and every 3-graph
attaining it is an equipartition `H_S`.  The converse — every equipartition `H_S` attains the
maximum — fails for `n ≡ 3 (mod 6)`; see `Theorem2_extremal_HS` for the exact statement.)
@isnad1 id=and.1h1v.s7.53a2560ab886 from=translated src=- shape=5c237dee vocab=8d390b5e
-/
theorem Theorem2 (hn : 5 ≤ Fintype.card V) :
    (∀ H : ThreeGraph V, H.FourPointProperty → H.edges.card ≤ exS6 (Fintype.card V)) ∧
    (∃ f : V → Fin 6, IsEquipartition f ∧ (HS f).edges.card = exS6 (Fintype.card V)) ∧
    (∀ H : ThreeGraph V, H.FourPointProperty → H.edges.card = exS6 (Fintype.card V) →
      ∃ f : V → Fin 6, IsEquipartition f ∧ H = HS f) :=
  theorem2 hn

/-- Theorem 2, precisely: which equipartitions are extremal.  For `n ≡ 3 (mod 6)` the three
larger classes have to form a triple of `S(6)`; the other equipartitions have one edge less.
@isnad1 id=iff.1h2v.s7.89131420da31 from=translated src=- shape=2fd30239 vocab=e2a8fe8a
-/
theorem Theorem2_extremal_HS (hn : 5 ≤ Fintype.card V) (f : V → Fin 6) :
    (HS f).edges.card = exS6 (Fintype.card V) ↔
      IsEquipartition f ∧ (Fintype.card V % 6 = 3 →
        univ.filter (fun i => partSizes f i = Fintype.card V / 6 + 1) ∈ S6.edges) :=
  HS_extremal_iff hn f

/-! ## §2  A remark on `m(n, 3, 4, 3)` -/

/-- **Theorem 3.**  `(2 + o(1))/7 · C(n,3) ≤ m(n,3,4,3) ≤ (1/3) · C(n,3) · n/(n-2)`.
@isnad1 id=and.0h0v.s7.55e0e320f3a8 from=translated src=- shape=763b33db vocab=5ea84e91
-/
theorem Theorem3 :
    (∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
        (2 - ε) / 7 * (n.choose 3 : ℝ) ≤ mExtremal n 3 4 3) ∧
    (∀ n : ℕ, 3 ≤ n → (mExtremal n 3 4 3 : ℝ) ≤ 1 / 3 * (n.choose 3 : ℝ) * (n / (n - 2))) :=
  ⟨theorem3_lower, theorem3_upper⟩

/-! ## §3  The proof of Theorem 1 -/

omit [Fintype V] in
/-- **Proposition 6.**  Two points `v, w` are equivalent iff no edge contains both.
@isnad1 id=iff.2h4v.s5.9ff1327911ac from=translated src=- shape=6ac46358 vocab=d76b9c81
-/
theorem Proposition6 (H : ThreeGraph V) (hH : H.FourPointProperty) {v w : V} (hvw : v ≠ w) :
    (∀ a b, H.IsEdge v a b ↔ H.IsEdge w a b) ↔ ∀ z, ¬H.IsEdge v w z :=
  prop6 ((H.fourPointProperty_iff).mp hH) hvw

/-- The four-point property characterises Examples 1 and 2 (Theorem 1 and its converse).
@isnad1 id=iff.0h2v.s6.0b25abdbc7b1 from=translated src=- shape=3c3fe658 vocab=c60ccbae
-/
theorem characterisation (H : ThreeGraph V) :
    H.FourPointProperty ↔
      (∃ f : V → Fin 6, H = HS f) ∨ (∃ p : V → ℝ × ℝ, IsCircleConfig p ∧ H = circleGraph p) :=
  fourPointProperty_iff_examples H

/-! ## Not formalised

* Remark 1 (the points of Example 2 can be moved to the vertices of a regular `(2k+1)`-gon;
  if any two vertices are covered by an edge then `n` is odd);
* §4: Bollobás' theorem and the result of [4] (cited, not proved in the paper), Problem 1 and
  Example 3.  Conjecture 1 is stated (not proved) as `FranklFuredi.ErdosSosConjecture`.
-/

/-- "For `n ≤ 5` the two examples coincide."
@isnad1 id=ex.2h2v.s5.8f951eac0b38 from=translated src=- shape=37c893fe vocab=987a6c39
-/
theorem small_case (H : ThreeGraph V) (hH : H.FourPointProperty) (hn : Fintype.card V ≤ 5) :
    ∃ f : V → Fin 6, H = HS f :=
  eq_HS_of_card_le_five H hH hn

end FranklFuredi.Paper
