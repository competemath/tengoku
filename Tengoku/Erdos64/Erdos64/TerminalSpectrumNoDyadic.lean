import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- In a graph with no power-of-two simple cycle, an explicit positive
terminal path with two root edges cannot have a dyadic fan-cycle length.
@isnad1 id=ne.8h7v.s6.04d99d467358 from=translated src=- shape=4018264c vocab=9a4e3ada
-/
theorem terminal_path_length_not_dyadic_of_no_powerOfTwoCycle
    {V : Type u} {G : SimpleGraph V} {r a b : V}
    {p : G.Walk a b}
    (hno : ¬ HasPowerOfTwoCycle G)
    (hp : p.IsPath)
    (hroot : r ∉ p.support)
    (hra : G.Adj r a)
    (hrb : G.Adj r b)
    (hab : a ≠ b)
    (hlong : 1 < p.length)
    {k : ℕ} (hk : k ≥ 2) :
    p.length + 2 ≠ 2 ^ k := by
  intro hlen
  obtain ⟨c, hc, hclen⟩ :=
    endpoint_fan_cycle_certificate hp hra hrb hroot hab hlong
  apply hno
  refine ⟨k, a, c, hk, hc, ?_⟩
  exact hclen.trans hlen

end Erdos64
