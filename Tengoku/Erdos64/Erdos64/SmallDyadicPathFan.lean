import Tengoku.Erdos64.Erdos64.OneBoundaryOffPathFan

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

private theorem cycle_support_index_lt
    {V : Type u} {G : SimpleGraph V} {r a : V}
    (c : G.Walk r r) (hc : c.IsCycle) (ha : a ∈ c.support) :
    ∃ i, i < c.length ∧ c.getVert i = a := by
  obtain ⟨i, hi, hile⟩ := SimpleGraph.Walk.mem_support_iff_exists_getVert.mp ha
  by_cases hil : i = c.length
  · refine ⟨0, by have := hc.three_le_length; omega, ?_⟩
    simpa [hil] using hi
  · exact ⟨i, by omega, hi⟩

private theorem cycle_idxOf_getVert
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r : V}
    (c : G.Walk r r) (hc : c.IsCycle) {i : ℕ} (hi : i < c.length) :
    c.support.idxOf (c.getVert i) = i := by
  by_cases hi0 : i = 0
  · subst i
    rw [SimpleGraph.Walk.getVert_zero]
    have h := c.length_takeUntil c.start_mem_support
    simpa using h.symm
  have hne : c.getVert i ≠ r := by
    intro h
    have heq := hc.getVert_injOn' (x₁ := i) (x₂ := 0)
      (by change i ≤ c.length - 1; omega)
      (by change 0 ≤ c.length - 1; omega)
      (by simpa using h)
    exact hi0 heq
  have hlt := c.length_takeUntil_lt_length (c.getVert_mem_support i) hne
  have hindex := hc.getVert_injOn'
    (x₁ := (c.takeUntil (c.getVert i) (c.getVert_mem_support i)).length) (x₂ := i)
    (by change _ ≤ c.length - 1; omega)
    (by change i ≤ c.length - 1; omega)
    (c.getVert_length_takeUntil (c.getVert_mem_support i))
  rwa [c.length_takeUntil] at hindex

private theorem cycle_rotate_getVert_add
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r : V}
    (c : G.Walk r r) (hc : c.IsCycle) {i j : ℕ}
    (hi : i < c.length) (hij : i + j < c.length) :
    (c.rotate (c.getVert i) (c.getVert_mem_support i)).getVert j = c.getVert (i + j) := by
  have hidx := cycle_idxOf_getVert c hc hi
  simp only [SimpleGraph.Walk.rotate, SimpleGraph.Walk.dropUntil_eq_drop,
    SimpleGraph.Walk.takeUntil_eq_take, SimpleGraph.Walk.getVert_append,
    SimpleGraph.Walk.length_copy, SimpleGraph.Walk.drop_length, hidx]
  rw [ite_eq_left (by omega)]
  simp [hidx]

private theorem cycle_fan_index_lengths
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r w : V}
    (c : G.Walk r r) (hc : c.IsCycle) {i j : ℕ}
    (hij : i < j) (hj : j < c.length)
    (hwi : G.Adj w (c.getVert i)) (hwj : G.Adj w (c.getVert j))
    (hw : w ∉ c.support)
    (hgap : 1 < j - i) (hother : 1 < c.length - (j - i)) :
    HasSimpleCycleOfLength G (j - i + 2) ∧
      HasSimpleCycleOfLength G (c.length - (j - i) + 2) := by
  let q := c.rotate (c.getVert i) (c.getVert_mem_support i)
  have hq : q.IsCycle := hc.rotate (c.getVert_mem_support i)
  have hqlen : q.length = c.length := c.length_rotate _ _
  have hget : q.getVert (j - i) = c.getVert j := by
    have h := cycle_rotate_getVert_add c hc (i := i) (j := j - i)
      (by omega) (by omega)
    simpa only [show i + (j - i) = j by omega] using h
  have hwiq : G.Adj w (q.getVert (j - i)) := by simpa only [hget] using hwj
  have hneq : c.getVert i ≠ q.getVert (j - i) := by
    rw [hget]
    intro h
    have := hc.getVert_injOn' (x₁ := i) (x₂ := j)
      (by change i ≤ c.length - 1; omega)
      (by change j ≤ c.length - 1; omega) h
    omega
  have hwq : w ∉ q.support := by
    intro h
    exact hw ((c.mem_support_rotate_iff _ _).mp h)
  constructor
  · obtain ⟨d, hd, hlen⟩ := endpoint_fan_cycle_certificate
      (hq.isPath_take (n := j - i) (by omega)) hwi hwiq
      (fun h => hwq ((q.isSubwalk_take (j - i)).support_subset h)) hneq
      (by simp only [SimpleGraph.Walk.take_length]; omega)
    refine ⟨_, d, hd, ?_⟩
    simpa only [SimpleGraph.Walk.take_length,
      Nat.min_eq_left (show j - i ≤ q.length by omega)] using hlen
  · obtain ⟨d, hd, hlen⟩ := endpoint_fan_cycle_certificate
      (hq.isPath_drop (n := j - i) (by omega)) hwiq hwi
      (fun h => hwq ((q.isSubwalk_drop (j - i)).support_subset h)) hneq.symm
      (by simpa only [SimpleGraph.Walk.drop_length, hqlen] using hother)
    refine ⟨_, d, hd, ?_⟩
    simpa only [SimpleGraph.Walk.drop_length, hqlen] using hlen

private theorem small_cycle_even_index_fan
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r w : V}
    (c : G.Walk r r) (hc : c.IsCycle)
    (hlen : c.length = 6 ∨ c.length = 10) {i j : ℕ}
    (hi : i < c.length) (hj : j < c.length) (hne : i ≠ j)
    (hparity : i % 2 = j % 2)
    (hwi : G.Adj w (c.getVert i)) (hwj : G.Adj w (c.getVert j))
    (hw : w ∉ c.support) : HasPowerOfTwoCycle G := by
  suffices hordered : ∀ a b : ℕ, a < b → b < c.length → a % 2 = b % 2 →
      G.Adj w (c.getVert a) → G.Adj w (c.getVert b) → HasPowerOfTwoCycle G by
    rcases lt_or_gt_of_ne hne with h | h
    · exact hordered i j h hj hparity hwi hwj
    · exact hordered j i h hi hparity.symm hwj hwi
  intro a b hab hb hmod hwa hwb
  have hgap : 1 < b - a := by omega
  have hother : 1 < c.length - (b - a) := by omega
  obtain ⟨hfirst, hsecond⟩ := cycle_fan_index_lengths c hc hab hb hwa hwb hw hgap hother
  have hcases : b - a + 2 = 4 ∨ b - a + 2 = 8 ∨
      c.length - (b - a) + 2 = 4 ∨ c.length - (b - a) + 2 = 8 := by omega
  rcases hcases with h4 | h8 | h4 | h8
  · obtain ⟨v, d, hd, hlength⟩ := hfirst
    exact ⟨2, v, d, by omega, hd, by omega⟩
  · obtain ⟨v, d, hd, hlength⟩ := hfirst
    exact ⟨3, v, d, by omega, hd, by omega⟩
  · obtain ⟨v, d, hd, hlength⟩ := hsecond
    exact ⟨2, v, d, by omega, hd, by omega⟩
  · obtain ⟨v, d, hd, hlength⟩ := hsecond
    exact ⟨3, v, d, by omega, hd, by omega⟩

/-- Three distinct neighbors of one external vertex on a simple six- or
ten-cycle force a cycle of power-of-two length. The parity pigeonhole gives
two attachments with an even arc, and one complementary arc has length two
or six. No minimum-degree or minimal-counterexample assumption is needed.-/
theorem hasPowerOfTwoCycle_of_three_attachments_to_six_or_ten_cycle
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r w a b d : V}
    (c : G.Walk r r) (hc : c.IsCycle) (hlen : c.length = 6 ∨ c.length = 10)
    (ha : a ∈ c.support) (hb : b ∈ c.support) (hd : d ∈ c.support)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hwa : G.Adj w a) (hwb : G.Adj w b) (hwd : G.Adj w d)
    (hw : w ∉ c.support) : HasPowerOfTwoCycle G := by
  obtain ⟨i, hi, hia⟩ := cycle_support_index_lt c hc ha
  obtain ⟨j, hj, hjb⟩ := cycle_support_index_lt c hc hb
  obtain ⟨k, hk, hkd⟩ := cycle_support_index_lt c hc hd
  have hij : i ≠ j := by intro h; exact hab (hia.symm.trans (h ▸ hjb))
  have hik : i ≠ k := by intro h; exact had (hia.symm.trans (h ▸ hkd))
  have hjk : j ≠ k := by intro h; exact hbd (hjb.symm.trans (h ▸ hkd))
  have hwi : G.Adj w (c.getVert i) := by simpa only [hia] using hwa
  have hwj : G.Adj w (c.getVert j) := by simpa only [hjb] using hwb
  have hwk : G.Adj w (c.getVert k) := by simpa only [hkd] using hwd
  have hparity : i % 2 = j % 2 ∨ i % 2 = k % 2 ∨ j % 2 = k % 2 := by omega
  rcases hparity with h | h | h
  · exact small_cycle_even_index_fan c hc hlen hi hj hij h hwi hwj hw
  · exact small_cycle_even_index_fan c hc hlen hi hk hik h hwi hwk hw
  · exact small_cycle_even_index_fan c hc hlen hj hk hjk h hwj hwk hw

/-- A simple port path of length four or eight, closed through its external
common root, cannot have an external vertex distinct from the root with
three distinct attachments to the path in a dyadic-cycle-free graph.-/
theorem hasPowerOfTwoCycle_of_three_attachments_to_small_port_path
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {r w x y a b d : V}
    (p : G.Walk x y) (hp : p.IsPath) (hlen : p.length = 4 ∨ p.length = 8)
    (hrp : r ∉ p.support) (hrx : G.Adj r x) (hry : G.Adj r y)
    (ha : a ∈ p.support) (hb : b ∈ p.support) (hd : d ∈ p.support)
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hwa : G.Adj w a) (hwb : G.Adj w b) (hwd : G.Adj w d)
    (hwp : w ∉ p.support) (hwr : w ≠ r) : HasPowerOfTwoCycle G := by
  let c : G.Walk r r := SimpleGraph.Walk.cons hrx (p.concat hry.symm)
  have hc : c.IsCycle := by
    apply SimpleGraph.Walk.isCycle_iff_isPath_tail_and_le_length.mpr
    constructor
    · change ((SimpleGraph.Walk.cons hrx (p.concat hry.symm)).tail).IsPath
      rw [SimpleGraph.Walk.tail_cons]
      exact (SimpleGraph.Walk.isPath_copy _ _ _).mpr (hp.concat hrp hry.symm)
    · simp only [c, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]
      omega
  have hclen : c.length = 6 ∨ c.length = 10 := by
    simp only [c, SimpleGraph.Walk.length_cons, SimpleGraph.Walk.length_concat]
    omega
  have hsupp (v : V) : v ∈ c.support ↔ v = r ∨ v ∈ p.support := by
    simp only [c, SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_concat,
      List.mem_cons, List.mem_append]
    tauto
  exact hasPowerOfTwoCycle_of_three_attachments_to_six_or_ten_cycle c hc hclen
    ((hsupp a).mpr (Or.inr ha)) ((hsupp b).mpr (Or.inr hb))
    ((hsupp d).mpr (Or.inr hd)) hab had hbd hwa hwb hwd
    (by rw [hsupp]; exact fun h => h.elim hwr hwp)

/-- Every component outside a native simple port path of length four or
eight has at least two carrier boundary vertices. A boundary of size at
most one would be a singleton with three attachments, which the small
cycle fan theorem excludes.-/
theorem MinimalCounterexample.rootDeleted_small_port_path_two_le_component_boundary
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent) (hCD : C ≠ D)
    {x y : V} (hxy : x ≠ y) (hrx : G.Adj r x) (hry : G.Adj r y)
    (p : G.Walk x y) (hp : p.IsPath) (hlen : p.length = 4 ∨ p.length = 8)
    (hinside : ∀ v, v ∈ p.support → v ∈ rootDeletedComponentCarrier G r C)
    (E : (G.induce {v : V | v ∈ rootDeletedComponentCarrier G r C ∧
      v ∉ p.support}).ConnectedComponent) :
    2 ≤ (carrierBoundaryVertices G
      (offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E)).card := by
  classical
  by_contra hnot
  obtain ⟨t, a, b, d, ht, htp, ha, hb, hd, hab, had, hbd, hta, htb, htd⟩ :=
    M.rootDeleted_one_boundary_component_three_attachment_fan r C D hCD
      hxy hrx hry p hinside E (by omega)
  have hrC : r ∉ rootDeletedComponentCarrier G r C :=
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).2
  have hrp : r ∉ p.support := fun h => hrC (hinside r h)
  have htK : t ∈ offPathComponentCarrier G (rootDeletedComponentCarrier G r C) p E := by
    rw [ht]
    simp
  have htr : t ≠ r := by
    intro h
    obtain ⟨htC, _⟩ :=
      (mem_offPathComponentCarrier_iff G (rootDeletedComponentCarrier G r C) p E t).mp htK
    exact hrC (h ▸ htC.1)
  exact M.isCounterexample.2
    (hasPowerOfTwoCycle_of_three_attachments_to_small_port_path p hp hlen hrp hrx hry
      ha hb hd hab had hbd hta htb htd htp htr)

end Erdos64
