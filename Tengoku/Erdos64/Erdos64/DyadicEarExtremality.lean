import Tengoku.Erdos64.Erdos64.DyadicPathEar

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

private theorem fresh_dyadic_ear_reroute_and_length_ne
    {V : Type u} {G : SimpleGraph V} {a b x y : V}
    (pre : G.Walk a x) (segment : G.Walk x y)
    (suffix : G.Walk y b) (ear : G.Walk x y)
    (horiginal : ((pre.append segment).append suffix).IsPath)
    (hear : ear.IsPath) (hxy : x ≠ y)
    (hfresh : ∀ z, z ∈ ear.support →
      z ∈ ((pre.append segment).append suffix).support → z = x ∨ z = y)
    {k : ℕ} (hk : 1 ≤ k) (hlen : ear.length = 2 ^ k)
    (hno : ¬HasPowerOfTwoCycle G) :
    ((pre.append ear).append suffix).IsPath ∧ ear.length ≠ segment.length := by
  have htwo : 2 ≤ ear.length := by
    rw [hlen]
    exact (show 2 = 2 ^ 1 from rfl).le.trans
      (Nat.pow_le_pow_right (by decide) hk)
  obtain ⟨hreroute, hcycle⟩ := terminal_path_reroute_of_fresh_ear
    pre segment suffix ear horiginal hear hxy hfresh (Or.inr (by omega))
  refine ⟨hreroute, ?_⟩
  intro heq
  apply hno
  refine ⟨k + 1, x, segment.append ear.reverse, by omega, hcycle, ?_⟩
  simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
    ← heq, hlen, Nat.pow_succ]
  omega

/-- A fresh dyadic ear strictly shortens the segment it replaces on an
absolutely longest terminal path in a dyadic-cycle-free graph. This consumes
an existing ear and longestness among all simple terminal paths.-/
theorem dyadic_ear_lt_segment_of_longest_terminal_path
    {V : Type u} {G : SimpleGraph V} {a b x y : V}
    (pre : G.Walk a x) (segment : G.Walk x y)
    (suffix : G.Walk y b) (ear : G.Walk x y)
    (horiginal : ((pre.append segment).append suffix).IsPath)
    (hear : ear.IsPath) (hxy : x ≠ y)
    (hfresh : ∀ z, z ∈ ear.support →
      z ∈ ((pre.append segment).append suffix).support → z = x ∨ z = y)
    {k : ℕ} (hk : 1 ≤ k) (hlen : ear.length = 2 ^ k)
    (hno : ¬HasPowerOfTwoCycle G)
    (hmax : ∀ q : G.Walk a b, q.IsPath →
      q.length ≤ ((pre.append segment).append suffix).length) :
    ear.length < segment.length := by
  obtain ⟨hreroute, hne⟩ := fresh_dyadic_ear_reroute_and_length_ne
    pre segment suffix ear horiginal hear hxy hfresh hk hlen hno
  have hle := hmax ((pre.append ear).append suffix) hreroute
  simp only [SimpleGraph.Walk.length_append] at hle
  omega

/-- A fresh dyadic ear strictly lengthens the segment it replaces on an
absolutely shortest terminal path in a dyadic-cycle-free graph. This is a
comparison, not a theorem asserting that an ear exists.-/
theorem segment_lt_dyadic_ear_of_shortest_terminal_path
    {V : Type u} {G : SimpleGraph V} {a b x y : V}
    (pre : G.Walk a x) (segment : G.Walk x y)
    (suffix : G.Walk y b) (ear : G.Walk x y)
    (horiginal : ((pre.append segment).append suffix).IsPath)
    (hear : ear.IsPath) (hxy : x ≠ y)
    (hfresh : ∀ z, z ∈ ear.support →
      z ∈ ((pre.append segment).append suffix).support → z = x ∨ z = y)
    {k : ℕ} (hk : 1 ≤ k) (hlen : ear.length = 2 ^ k)
    (hno : ¬HasPowerOfTwoCycle G)
    (hmin : ∀ q : G.Walk a b, q.IsPath →
      ((pre.append segment).append suffix).length ≤ q.length) :
    segment.length < ear.length := by
  obtain ⟨hreroute, hne⟩ := fresh_dyadic_ear_reroute_and_length_ne
    pre segment suffix ear horiginal hear hxy hfresh hk hlen hno
  have hle := hmin ((pre.append ear).append suffix) hreroute
  simp only [SimpleGraph.Walk.length_append] at hle
  omega

end Erdos64
