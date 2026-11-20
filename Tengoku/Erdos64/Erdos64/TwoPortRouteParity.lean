import Tengoku.Erdos64.Erdos64.Arithmetic
import Tengoku.Seed.Combinatorics.SimpleGraph.Coloring.Constructions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Two walks with the same endpoints and opposite length parity rule out
a bipartition, without requiring either walk to be simple or their interiors
to be disjoint.
@isnad1 id=not.2h6v.s5.cb727215c30f from=translated src=- shape=f2a5bf99 vocab=6f0694bd
-/
theorem not_isBipartite_of_opposite_parity_routes
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (p q : G.Walk a b) (hp : Odd p.length) (hq : Even q.length) :
    ¬ G.IsBipartite := by
  rintro ⟨color⟩
  let c : G.Coloring Bool := SimpleGraph.recolorOfEquiv G finTwoEquiv color
  have hsame := (c.even_length_iff_congr q).mp hq
  have hpEven := (c.even_length_iff_congr p).mpr hsame
  exact (Nat.not_even_iff_odd.mpr hp) hpEven

/-- A route completed to dyadic length by one new edge is odd, whereas an
already dyadic route is even. Consequently the two supplied routes have
different lengths, are distinct, and certify non-bipartiteness. This does
not infer internally disjoint routes or a dyadic simple cycle.
@isnad1 id=and.4h8v.s7.98c846f2a56a from=translated src=- shape=62519362 vocab=fa12c266
-/
theorem twoPort_routes_parity_of_dyadic_completion
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (p q : G.Walk a b) {j k : ℕ} (hj : 2 ≤ j) (hk : 2 ≤ k)
    (hp : p.length + 1 = 2 ^ j) (hq : q.length = 2 ^ k) :
    Odd p.length ∧ Even q.length ∧ p.length ≠ q.length ∧
      p ≠ q ∧ ¬ G.IsBipartite := by
  have htwo : Even (2 : ℕ) := by decide
  have hpNext : Even (p.length + 1) := by
    rw [hp]
    exact htwo.pow_of_ne_zero (by omega)
  have hpOdd : Odd p.length := by
    exact Nat.not_even_iff_odd.mp (Nat.even_add_one.mp hpNext)
  have hqEven : Even q.length := by
    rw [hq]
    exact htwo.pow_of_ne_zero (by omega)
  have hlength : p.length ≠ q.length := by
    intro heq
    exact (Nat.not_even_iff_odd.mpr hpOdd) (heq.symm ▸ hqEven)
  refine ⟨hpOdd, hqEven, hlength, ?_,
    not_isBipartite_of_opposite_parity_routes p q hpOdd hqEven⟩
  intro heq
  exact hlength (congrArg SimpleGraph.Walk.length heq)

end Erdos64
