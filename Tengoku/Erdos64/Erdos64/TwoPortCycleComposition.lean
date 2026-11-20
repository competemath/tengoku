import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

private theorem terminal_pair_isCycle
    {V : Type u} {G : SimpleGraph V} {a b : V}
    {p q : G.Walk a b}
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ z, z ∈ p.support → z ∈ q.support → z = a ∨ z = b)
    (hlong : 1 < p.length) :
    (p.append q.reverse).IsCycle := by
  have ha : a ∉ p.support.tail := by
    have hn : (a :: p.support.tail).Nodup := by
      rw [p.cons_tail_support]
      exact hp.support_nodup
    exact (List.nodup_cons.mp hn).1
  have hb : b ∉ q.reverse.support.tail := by
    have hn : (b :: q.reverse.support.tail).Nodup := by
      rw [q.reverse.cons_tail_support]
      exact hq.reverse.support_nodup
    exact (List.nodup_cons.mp hn).1
  have htails : p.support.tail.Disjoint q.reverse.support.tail := by
    rw [List.disjoint_left]
    intro z hzp hzq
    have hzq' : z ∈ q.support := by
      have hmem := List.mem_of_mem_tail hzq
      simpa only [SimpleGraph.Walk.support_reverse, List.mem_reverse] using hmem
    rcases hinter z (List.mem_of_mem_tail hzp) hzq' with hza | hzb
    · exact ha (hza ▸ hzp)
    · exact hb (hzb ▸ hzq)
  exact hp.isCycle_append hq.reverse htails (Or.inl hlong)

/-- Three simple paths with common terminals and pairwise-disjoint interiors
give three explicit simple cycles. Their lengths are the pairwise path-length
sums, and their support lists are specified exactly. No dyadicity is asserted.-/
theorem three_terminal_paths_cycle_spectrum
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (p q t : G.Walk a b)
    (hp : p.IsPath) (hq : q.IsPath) (ht : t.IsPath)
    (hpq : ∀ z, z ∈ p.support → z ∈ q.support → z = a ∨ z = b)
    (hqt : ∀ z, z ∈ q.support → z ∈ t.support → z = a ∨ z = b)
    (htp : ∀ z, z ∈ t.support → z ∈ p.support → z = a ∨ z = b)
    (hpLength : 1 < p.length)
    (hqLength : 1 < q.length)
    (htLength : 1 < t.length) :
    ((p.append q.reverse).IsCycle ∧
      (p.append q.reverse).length = p.length + q.length ∧
      (p.append q.reverse).support = p.support ++ q.support.reverse.tail) ∧
    ((q.append t.reverse).IsCycle ∧
      (q.append t.reverse).length = q.length + t.length ∧
      (q.append t.reverse).support = q.support ++ t.support.reverse.tail) ∧
    ((t.append p.reverse).IsCycle ∧
      (t.append p.reverse).length = t.length + p.length ∧
      (t.append p.reverse).support = t.support ++ p.support.reverse.tail) := by
  refine ⟨⟨terminal_pair_isCycle hp hq hpq hpLength, ?_, ?_⟩,
    ⟨terminal_pair_isCycle hq ht hqt hqLength, ?_, ?_⟩,
    ⟨terminal_pair_isCycle ht hp htp htLength, ?_, ?_⟩⟩ <;>
      simp only [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
      SimpleGraph.Walk.support_append, SimpleGraph.Walk.support_reverse]

/-- Two internally disjoint terminal paths of the same dyadic length already
form a forbidden cycle of the next dyadic length.-/
theorem false_of_equal_dyadic_terminal_paths
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (hno : ¬ HasPowerOfTwoCycle G)
    (p q : G.Walk a b)
    (hp : p.IsPath) (hq : q.IsPath)
    (hinter : ∀ z, z ∈ p.support → z ∈ q.support → z = a ∨ z = b)
    (hlong : 1 < p.length)
    {k : ℕ} (hk : 2 ≤ k)
    (hpLength : p.length = 2 ^ k)
    (hqLength : q.length = 2 ^ k) :
    False := by
  have hc : (p.append q.reverse).IsCycle :=
    terminal_pair_isCycle hp hq hinter hlong
  apply hno
  refine ⟨k + 1, a, p.append q.reverse, ?_, hc, ?_⟩
  · omega
  · simp [hpLength, hqLength, pow_succ, Nat.mul_two]

/-- In a graph with no required cycle, three internally disjoint terminal
paths cannot realize a dyadic length either through the common root or by
pairing two of the routes. This is the obstruction form used by descent
arguments; it asserts non-dyadicity rather than assuming a dyadic route.-/
theorem three_terminal_paths_no_dyadic_lengths
    {V : Type u} {G : SimpleGraph V} {r a b : V}
    (hno : ¬ HasPowerOfTwoCycle G)
    (p q t : G.Walk a b)
    (hp : p.IsPath) (hq : q.IsPath) (ht : t.IsPath)
    (hpq : ∀ z, z ∈ p.support → z ∈ q.support → z = a ∨ z = b)
    (hqt : ∀ z, z ∈ q.support → z ∈ t.support → z = a ∨ z = b)
    (htp : ∀ z, z ∈ t.support → z ∈ p.support → z = a ∨ z = b)
    (hpLength : 1 < p.length)
    (hqLength : 1 < q.length)
    (htLength : 1 < t.length)
    (hrootp : r ∉ p.support)
    (hrootq : r ∉ q.support)
    (hroott : r ∉ t.support)
    (hra : G.Adj r a)
    (hrb : G.Adj r b)
    (hab : a ≠ b) :
    (∀ k, 2 ≤ k → p.length + 2 ≠ 2 ^ k) ∧
      (∀ k, 2 ≤ k → q.length + 2 ≠ 2 ^ k) ∧
      (∀ k, 2 ≤ k → t.length + 2 ≠ 2 ^ k) ∧
      (∀ k, 2 ≤ k → p.length + q.length ≠ 2 ^ k) ∧
      (∀ k, 2 ≤ k → q.length + t.length ≠ 2 ^ k) ∧
      (∀ k, 2 ≤ k → t.length + p.length ≠ 2 ^ k) := by
  obtain ⟨⟨hpqCycle, hpqLength, _⟩, ⟨hqtCycle, hqtLength, _⟩,
      ⟨htpCycle, htpLength, _⟩⟩ :=
    three_terminal_paths_cycle_spectrum p q t hp hq ht hpq hqt htp
      hpLength hqLength htLength
  have hfanp : ∀ k, 2 ≤ k → p.length + 2 ≠ 2 ^ k := by
    intro k hk hlen
    obtain ⟨c, hc, hclen⟩ :=
      endpoint_fan_cycle_certificate hp hra hrb hrootp hab hpLength
    apply hno
    exact ⟨k, a, c, hk, hc, hclen.trans hlen⟩
  have hfanq : ∀ k, 2 ≤ k → q.length + 2 ≠ 2 ^ k := by
    intro k hk hlen
    obtain ⟨c, hc, hclen⟩ :=
      endpoint_fan_cycle_certificate hq hra hrb hrootq hab hqLength
    apply hno
    exact ⟨k, a, c, hk, hc, hclen.trans hlen⟩
  have hfant : ∀ k, 2 ≤ k → t.length + 2 ≠ 2 ^ k := by
    intro k hk hlen
    obtain ⟨c, hc, hclen⟩ :=
      endpoint_fan_cycle_certificate ht hra hrb hroott hab htLength
    apply hno
    exact ⟨k, a, c, hk, hc, hclen.trans hlen⟩
  have hpairpq : ∀ k, 2 ≤ k → p.length + q.length ≠ 2 ^ k := by
    intro k hk hlen
    apply hno
    exact ⟨k, a, p.append q.reverse, hk, hpqCycle, hpqLength.trans hlen⟩
  have hpairqt : ∀ k, 2 ≤ k → q.length + t.length ≠ 2 ^ k := by
    intro k hk hlen
    apply hno
    exact ⟨k, a, q.append t.reverse, hk, hqtCycle, hqtLength.trans hlen⟩
  have hpairtp : ∀ k, 2 ≤ k → t.length + p.length ≠ 2 ^ k := by
    intro k hk hlen
    apply hno
    exact ⟨k, a, t.append p.reverse, hk, htpCycle, htpLength.trans hlen⟩
  exact ⟨hfanp, hfanq, hfant, hpairpq, hpairqt, hpairtp⟩

/-- A simple path of length greater than one together with a terminal edge
forms a simple cycle. This is the edge-route case omitted by the
three-long-path spectrum lemma.-/
theorem terminal_path_edge_cycle
    {V : Type u} {G : SimpleGraph V} {a b : V}
    (p : G.Walk a b)
    (hp : p.IsPath)
    (hab : G.Adj a b)
    (hlong : 1 < p.length) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = p.length + 1 := by
  let q : G.Walk a b := hab.toWalk
  have hq : q.IsPath := hab.isPath_toWalk
  have hinter : ∀ z, z ∈ p.support → z ∈ q.support → z = a ∨ z = b := by
    intro z _hzp hzq
    simpa [q, or_comm] using hzq
  refine ⟨p.append q.reverse, terminal_pair_isCycle hp hq hinter hlong, ?_⟩
  simp [q, SimpleGraph.Walk.length_append]

/-- A path between third neighbors, together with the two connector edges,
gives an `a -> b` route. If `a-b` is also an edge, this route closes to a
cycle whose length is the third-neighbor path length plus three.-/
theorem connector_path_edge_cycle
    {V : Type u} {G : SimpleGraph V}
    {a b z w : V} {p : G.Walk z w}
    (hp : p.IsPath)
    (havoid : ∀ v, v ∈ p.support → v ≠ a ∧ v ≠ b)
    (hab : a ≠ b)
    (hza : G.Adj a z)
    (hwb : G.Adj w b)
    (hzw : z ≠ w)
    (hedge : G.Adj a b) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = p.length + 3 := by
  let tail : G.Walk z b :=
    p.append (SimpleGraph.Walk.cons hwb SimpleGraph.Walk.nil)
  have htail : tail.IsPath := by
    dsimp [tail]
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_append]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons]
    apply List.nodup_append.mpr
    refine ⟨hp.support_nodup, by simp, ?_⟩
    intro v hv u hu
    simp only [List.mem_singleton] at hu
    subst u
    exact (havoid v hv).2
  let q : G.Walk a b := SimpleGraph.Walk.cons hza tail
  have hq : q.IsPath := by
    dsimp [q]
    apply (SimpleGraph.Walk.cons_isPath_iff hza _).2
    refine ⟨htail, ?_⟩
    rw [SimpleGraph.Walk.support_append]
    simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
      List.tail_cons, List.mem_append, List.mem_singleton]
    intro hv
    rcases hv with hv | rfl
    · exact (havoid a hv).1 rfl
    · exact hab rfl
  have hpos : 0 < p.length := by
    apply Nat.pos_of_ne_zero
    intro hzero
    exact hzw (SimpleGraph.Walk.eq_of_length_eq_zero hzero)
  have hqlong : 1 < q.length := by
    simp [q, tail, SimpleGraph.Walk.length_cons,
      SimpleGraph.Walk.length_append]
  obtain ⟨c, hc, hclength⟩ :=
    terminal_path_edge_cycle q hq hedge hqlong
  refine ⟨c, hc, ?_⟩
  calc
    c.length = q.length + 1 := hclength
    _ = p.length + 3 := by
      simp [q, tail, SimpleGraph.Walk.length_cons,
        SimpleGraph.Walk.length_append]

end Erdos64
