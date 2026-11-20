/-
The declarations below include the target, elementary proof terms, and a
kernel-checked boundary lemma.
Pins: Lean v4.33.1; mathlib 0df444a360eaa60ab8c11dca51a86af692955474.
No proof of Conjecture is supplied.
-/

import Tengoku.Seed.Combinatorics.SimpleGraph.Finite
import Tengoku.Seed.Combinatorics.SimpleGraph.Paths
import Tengoku.Seed.Combinatorics.SimpleGraph.Acyclic
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Tengoku.Seed.Combinatorics.SimpleGraph.Walk.Chord
import Tengoku.Seed.Combinatorics.SimpleGraph.DeleteEdges
import Tengoku.Seed.Combinatorics.Enumerative.DoubleCounting

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- A simple cycle whose length is a power of two with exponent at least two.-/
def HasPowerOfTwoCycle {V : Type u} (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (v : V) (c : G.Walk v v),
    k ≥ 2 ∧ c.IsCycle ∧ c.length = 2^k

/-- A finite graph satisfying the degree hypothesis and lacking the required cycle.-/
def IsCounterexample {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] : Prop :=
  G.minDegree ≥ 3 ∧ ¬ HasPowerOfTwoCycle G

/-- The affirmative target, with the vertex type and graph explicitly quantified.-/
def Conjecture : Prop :=
  ∀ (V : Type u) (G : SimpleGraph V) [Fintype V] [DecidableRel G.Adj],
    G.minDegree ≥ 3 → HasPowerOfTwoCycle G

/-- Propagate the minimum-degree lower bound to a supplied vertex.-/
theorem degree_ge_three_of_minDegree_ge_three {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] (h : G.minDegree ≥ 3) (v : V) :
    G.degree v ≥ 3 :=
  le_trans h (G.minDegree_le_degree v)

/-- A finite graph of minimum degree at least three contains a simple cycle.

The proof uses a longest path. If the graph were acyclic, every neighbor of
the path's initial endpoint would have to be the path's second vertex;
otherwise the path could be extended, or acyclicity would be contradicted.-/
theorem exists_simpleCycle_of_minDegree_ge_three
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj]
    (hmin : G.minDegree ≥ 3) :
    ∃ (v : V) (c : G.Walk v v), c.IsCycle := by
  classical
  haveI : Nonempty V := by
    by_contra hV
    letI : IsEmpty V := ⟨fun v => hV ⟨v⟩⟩
    have : (3 : ℕ) ≤ 0 := by simpa using hmin
    omega
  obtain ⟨u, v, p, hp, hmax⟩ :=
    SimpleGraph.Walk.exists_isPath_forall_isPath_length_le_length G
  by_contra hno
  have hacyc : G.IsAcyclic := by
    intro w c hc
    exact hno ⟨w, c, hc⟩
  have hdeg : 3 ≤ G.degree u :=
    degree_ge_three_of_minDegree_ge_three G hmin u
  have hforall : ∀ w, G.Adj u w → w = p.snd := by
    intro w hadj
    have hwmem : w ∈ p.support := by
      by_contra hw
      have hpcons : (SimpleGraph.Walk.cons hadj.symm p).IsPath := hp.cons hw
      have hle := hmax w v (SimpleGraph.Walk.cons hadj.symm p) hpcons
      have hbad : p.length + 1 ≤ p.length := by
        simpa [SimpleGraph.Walk.length_cons] using hle
      omega
    exact hacyc.eq_snd_of_adj_start hp hadj hwmem
  let N := G.neighborFinset u
  have hNsub : N ⊆ ({p.snd} : Finset V) := by
    intro w hw
    have hadj' : G.Adj u w := by
      simpa [N] using hw
    exact Finset.mem_singleton.mpr (hforall w hadj')
  have hcard : N.card ≤ 1 := by
    calc
      N.card ≤ ({p.snd} : Finset V).card := Finset.card_le_card hNsub
      _ = 1 := by simp
  have hdeg_le : G.degree u ≤ 1 := by
    change (G.neighborFinset u).card ≤ 1
    exact hcard
  omega

/-- Package an already supplied cycle; this does not construct one.-/
theorem hasPowerOfTwoCycle_of_witness {V : Type u} {G : SimpleGraph V}
    {k : ℕ} {v : V} (c : G.Walk v v) (hk : k ≥ 2)
    (hc : c.IsCycle) (hlen : c.length = 2^k) : HasPowerOfTwoCycle G :=
  ⟨k, v, c, hk, hc, hlen⟩

/-- A fully explicit certificate for the desired cycle.-/
structure CycleCertificate {V : Type u} (G : SimpleGraph V) where
  exponent : ℕ
  start : V
  cycle : G.Walk start start
  exponent_ge_two : exponent ≥ 2
  isCycle : cycle.IsCycle
  length_eq : cycle.length = 2 ^ exponent

/-- Convert an explicit cycle certificate into the conjecture's target.-/
theorem CycleCertificate.hasPowerOfTwoCycle {V : Type u}
    {G : SimpleGraph V} (certificate : CycleCertificate G) :
    HasPowerOfTwoCycle G :=
  ⟨certificate.exponent, certificate.start, certificate.cycle,
    certificate.exponent_ge_two, certificate.isCycle, certificate.length_eq⟩

/-- A path segment together with two endpoint edges gives an explicit cycle.

The path `q` runs from `a` to `b`; the two edges run from `b` to `v` and from
`v` back to `a`. The support hypotheses make the construction genuinely
simple rather than merely a closed walk.-/
theorem endpoint_fan_cycle_certificate
    {V : Type u} {G : SimpleGraph V}
    {a b v : V} {q : G.Walk a b}
    (hq : q.IsPath)
    (hva : G.Adj v a)
    (hvb : G.Adj v b)
    (hva_not_mem : v ∉ q.support)
    (hab : a ≠ b)
    (hqlen : 1 < q.length) :
    ∃ c : G.Walk a a, c.IsCycle ∧ c.length = q.length + 2 := by
  let r : G.Walk b a :=
    SimpleGraph.Walk.cons hvb.symm (SimpleGraph.Walk.cons hva SimpleGraph.Walk.nil)
  have hr : r.IsPath := by
    dsimp [r]
    refine (SimpleGraph.Walk.cons_isPath_iff _ _).2 ⟨?_, ?_⟩
    · exact
        (SimpleGraph.Walk.cons_isPath_iff _ _).2
          ⟨SimpleGraph.Walk.IsPath.nil, by simp [hva.ne]⟩
    · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
        List.mem_cons]
      intro hba
      rcases hba with hba | hba
      · exact (hvb.ne.symm hba).elim
      · rcases hba with hba | hba
        · exact (hab hba.symm).elim
        · simp at hba
  have hq_nil : ¬q.Nil := by
    intro hnil
    have hzero : q.length = 0 := by simp [hnil]
    omega
  have ha_not_mem_tail : a ∉ q.support.tail := by
    have hsupp : a :: q.support.tail = q.support := by
      calc
        a :: q.support.tail = a :: q.tail.support := by
          rw [q.support_tail_of_not_nil hq_nil]
        _ = q.support := q.cons_support_tail hq_nil
    have hnodup : (a :: q.support.tail).Nodup := by
      rw [hsupp]
      exact hq.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  have hdis : q.support.tail.Disjoint r.support.tail := by
    dsimp [r]
    simp only [List.disjoint_left, List.mem_cons]
    intro x hxq hxr
    rcases hxr with rfl | hxr
    · exact (hva_not_mem (List.mem_of_mem_tail hxq)).elim
    · rcases hxr with hxr | hxr
      · exact (ha_not_mem_tail (hxr ▸ hxq)).elim
      · simp at hxr
  refine ⟨q.append r, hq.isCycle_append hr hdis (Or.inl hqlen), ?_⟩
  rw [SimpleGraph.Walk.length_append]
  simp [r, SimpleGraph.Walk.length_cons]

/-- Existence of a simple cycle with one specified length.-/
def HasSimpleCycleOfLength {V : Type u} (G : SimpleGraph V) (n : ℕ) : Prop :=
  ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = n

/-- Turn a simple-cycle length witness into the target when its length is
dyadic.-/
theorem hasPowerOfTwoCycle_of_simpleCycleOfLength
    {V : Type u} {G : SimpleGraph V} {n k : ℕ}
    (hcycle : HasSimpleCycleOfLength G n)
    (hk : k ≥ 2)
    (hlen : n = 2 ^ k) :
    HasPowerOfTwoCycle G := by
  obtain ⟨v, c, hc, hclen⟩ := hcycle
  exact ⟨k, v, c, hk, hc, hclen.trans hlen⟩

/-- The seven explicit cycle-length witnesses supplied by two alternating
disjoint ears.

The fields are deliberately witness-oriented: realizing the seven simple
cycles from a cycle-and-ears decomposition is a separate graph-theoretic
theorem. This structure records exactly what that theorem must provide.-/
structure TwoEarSevenCycleCertificate {V : Type u} (G : SimpleGraph V) where
  n : ℕ
  p : ℕ
  q : ℕ
  alpha : ℕ
  beta : ℕ
  gamma : ℕ
  delta : ℕ
  cycle_n : HasSimpleCycleOfLength G n
  cycle_p_alpha_beta : HasSimpleCycleOfLength G (p + alpha + beta)
  cycle_p_gamma_delta : HasSimpleCycleOfLength G (p + gamma + delta)
  cycle_q_beta_gamma : HasSimpleCycleOfLength G (q + beta + gamma)
  cycle_q_delta_alpha : HasSimpleCycleOfLength G (q + delta + alpha)
  cycle_p_q_gamma_alpha : HasSimpleCycleOfLength G (p + q + gamma + alpha)
  cycle_p_q_beta_delta : HasSimpleCycleOfLength G (p + q + beta + delta)

/-- Any dyadic member of the seven-cycle certificate proves the conjecture
for the underlying graph.-/
theorem TwoEarSevenCycleCertificate.hasPowerOfTwoCycle
    {V : Type u} {G : SimpleGraph V}
    (certificate : TwoEarSevenCycleCertificate G)
    (hdyadic :
      ∃ k : ℕ, k ≥ 2 ∧
        (certificate.n = 2 ^ k ∨
          certificate.p + certificate.alpha + certificate.beta = 2 ^ k ∨
          certificate.p + certificate.gamma + certificate.delta = 2 ^ k ∨
          certificate.q + certificate.beta + certificate.gamma = 2 ^ k ∨
          certificate.q + certificate.delta + certificate.alpha = 2 ^ k ∨
          certificate.p + certificate.q + certificate.gamma + certificate.alpha = 2 ^ k ∨
          certificate.p + certificate.q + certificate.beta + certificate.delta = 2 ^ k)) :
    HasPowerOfTwoCycle G := by
  obtain ⟨k, hk, hlength⟩ := hdyadic
  rcases hlength with hlength | hlength
  · exact hasPowerOfTwoCycle_of_simpleCycleOfLength certificate.cycle_n hk hlength
  rcases hlength with hlength | hlength
  · exact
      hasPowerOfTwoCycle_of_simpleCycleOfLength
        certificate.cycle_p_alpha_beta hk hlength
  rcases hlength with hlength | hlength
  · exact
      hasPowerOfTwoCycle_of_simpleCycleOfLength
        certificate.cycle_p_gamma_delta hk hlength
  rcases hlength with hlength | hlength
  · exact
      hasPowerOfTwoCycle_of_simpleCycleOfLength
        certificate.cycle_q_beta_gamma hk hlength
  rcases hlength with hlength | hlength
  · exact
      hasPowerOfTwoCycle_of_simpleCycleOfLength
        certificate.cycle_q_delta_alpha hk hlength
  rcases hlength with hlength | hlength
  · exact
      hasPowerOfTwoCycle_of_simpleCycleOfLength
        certificate.cycle_p_q_gamma_alpha hk hlength
  · exact
      hasPowerOfTwoCycle_of_simpleCycleOfLength
        certificate.cycle_p_q_beta_delta hk hlength

/-- Six explicit paths describing a cycle with two alternating ears.

The four arc paths run in cyclic order `a -> b -> c -> d -> a`. The ears
run `a -> c` and `b -> d`. The cycle fields are the seven concrete
concatenations associated with this configuration. Their simplicity is
kept as an explicit hypothesis; forcing it from a minimal counterexample is
the later attachment theorem.-/
structure TwoEarPathConfiguration {V : Type u} (G : SimpleGraph V) where
  a : V
  b : V
  c : V
  d : V
  arcAB : G.Walk a b
  arcBC : G.Walk b c
  arcCD : G.Walk c d
  arcDA : G.Walk d a
  earAC : G.Walk a c
  earBD : G.Walk b d
  base_isCycle :
    (arcAB.append (arcBC.append (arcCD.append arcDA))).IsCycle
  p_alpha_beta_isCycle :
    (earAC.append (arcAB.append arcBC).reverse).IsCycle
  p_gamma_delta_isCycle :
    (earAC.append (arcCD.append arcDA)).IsCycle
  q_beta_gamma_isCycle :
    (earBD.append (arcBC.append arcCD).reverse).IsCycle
  q_delta_alpha_isCycle :
    (earBD.append (arcDA.append arcAB)).IsCycle
  p_q_gamma_alpha_isCycle :
    (earAC.append
      (arcCD.append (earBD.reverse.append arcAB.reverse))).IsCycle
  p_q_beta_delta_isCycle :
    (earAC.append
      (arcBC.reverse.append (earBD.append arcDA))).IsCycle

/-- Convert explicit two-ear path data into the seven-cycle certificate.-/
def TwoEarPathConfiguration.toCertificate
    {V : Type u} {G : SimpleGraph V}
    (configuration : TwoEarPathConfiguration G) :
    TwoEarSevenCycleCertificate G where
  n := configuration.arcAB.length + configuration.arcBC.length +
    configuration.arcCD.length + configuration.arcDA.length
  p := configuration.earAC.length
  q := configuration.earBD.length
  alpha := configuration.arcAB.length
  beta := configuration.arcBC.length
  gamma := configuration.arcCD.length
  delta := configuration.arcDA.length
  cycle_n := ⟨configuration.a,
    configuration.arcAB.append
      (configuration.arcBC.append
        (configuration.arcCD.append configuration.arcDA)),
    configuration.base_isCycle, by
      simp [SimpleGraph.Walk.length_append, Nat.add_assoc]⟩
  cycle_p_alpha_beta := ⟨configuration.a,
    configuration.earAC.append
      (configuration.arcAB.append configuration.arcBC).reverse,
    configuration.p_alpha_beta_isCycle, by
      simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
        Nat.add_assoc] <;> omega⟩
  cycle_p_gamma_delta := ⟨configuration.a,
    configuration.earAC.append
      (configuration.arcCD.append configuration.arcDA),
    configuration.p_gamma_delta_isCycle, by
      simp [SimpleGraph.Walk.length_append] <;> omega⟩
  cycle_q_beta_gamma := ⟨configuration.b,
    configuration.earBD.append
      (configuration.arcBC.append configuration.arcCD).reverse,
    configuration.q_beta_gamma_isCycle, by
      simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
        Nat.add_assoc] <;> omega⟩
  cycle_q_delta_alpha := ⟨configuration.b,
    configuration.earBD.append
      (configuration.arcDA.append configuration.arcAB),
    configuration.q_delta_alpha_isCycle, by
      simp [SimpleGraph.Walk.length_append] <;> omega⟩
  cycle_p_q_gamma_alpha := ⟨configuration.a,
    configuration.earAC.append
      (configuration.arcCD.append
        (configuration.earBD.reverse.append configuration.arcAB.reverse)),
    configuration.p_q_gamma_alpha_isCycle, by
      simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]⟩
  cycle_p_q_beta_delta := ⟨configuration.a,
    configuration.earAC.append
      (configuration.arcBC.reverse.append
        (configuration.earBD.append configuration.arcDA)),
    configuration.p_q_beta_delta_isCycle, by
      simp [SimpleGraph.Walk.length_append, SimpleGraph.Walk.length_reverse,
        Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]⟩

/-- A shortest-cycle certificate packages a cycle and its global length
minimality. It is an interface for later shortest-cycle bridge arguments;
existence is intentionally separate.-/
structure ShortestCycleCertificate {V : Type u} (G : SimpleGraph V) where
  start : V
  cycle : G.Walk start start
  isCycle : cycle.IsCycle
  shortest :
    ∀ (v : V) (c : G.Walk v v), c.IsCycle → cycle.length ≤ c.length

/-- A shortest-cycle certificate rules out every strictly shorter simple
cycle.-/
theorem ShortestCycleCertificate.not_exists_strictly_shorter
    {V : Type u} {G : SimpleGraph V}
    (certificate : ShortestCycleCertificate G)
    {v : V} {c : G.Walk v v} (hc : c.IsCycle)
    (hshorter : c.length < certificate.cycle.length) :
    False := by
  have hle := certificate.shortest v c hc
  omega

/-- A nonempty graph cycle family has a shortest simple cycle.

The proof minimizes natural-number lengths, so it does not require a finite
enumeration of all walks.-/
theorem exists_shortestCycleCertificate_of_exists_cycle
    {V : Type u} {G : SimpleGraph V}
    (hcycle : ∃ (v : V) (c : G.Walk v v), c.IsCycle) :
    Nonempty (ShortestCycleCertificate G) := by
  let lengths : Set ℕ :=
    {n | ∃ (v : V) (c : G.Walk v v), c.IsCycle ∧ c.length = n}
  have hlengths : lengths.Nonempty := by
    rcases hcycle with ⟨v, c, hc⟩
    exact ⟨c.length, ⟨v, c, hc, rfl⟩⟩
  let minLength := Nat.lt_wfRel.wf.min lengths hlengths
  have hminmem : minLength ∈ lengths := by
    exact Nat.lt_wfRel.wf.min_mem lengths hlengths
  rcases hminmem with ⟨v, c, hc, hlen⟩
  refine ⟨{ start := v, cycle := c, isCycle := hc, shortest := ?_ }⟩
  intro v' c' hc'
  have hmember : c'.length ∈ lengths := ⟨v', c', hc', rfl⟩
  have hle : minLength ≤ c'.length :=
    Nat.lt_wfRel.wf.min_le hmember
  simpa [hlen] using hle

/- A chordless cycle accounts for at most two ambient neighbors at each of
its vertices. Consequently, a vertex of degree at least three has an
external neighbor. The chordlessness premise is kept explicit until the
shortest-cycle chord argument is formalized. -/
theorem ShortestCycleCertificate.exists_external_neighbor_of_chordless
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (certificate : ShortestCycleCertificate G)
    (hchordless : certificate.cycle.IsChordless)
    (hmin : G.minDegree ≥ 3)
    {v : V} (hv : v ∈ certificate.cycle.support) :
    ∃ w, G.Adj v w ∧ w ∉ certificate.cycle.support := by
  classical
  by_contra hnone
  push_neg at hnone
  have hsubset :
      G.neighborSet v ⊆ certificate.cycle.toSubgraph.neighborSet v := by
    intro w hw
    have hwcycle : w ∈ certificate.cycle.support := hnone w hw
    have hedge : s(v, w) ∈ certificate.cycle.edges :=
      hchordless.mem_edges hv hwcycle hw
    exact certificate.cycle.adj_toSubgraph_iff_mem_edges.mpr hedge
  have hcardle :
      (G.neighborSet v).ncard ≤
        (certificate.cycle.toSubgraph.neighborSet v).ncard :=
    Set.ncard_le_ncard hsubset certificate.cycle.finite_neighborSet_toSubgraph
  have hcyclecard :
      (certificate.cycle.toSubgraph.neighborSet v).ncard = 2 :=
    certificate.isCycle.ncard_neighborSet_toSubgraph_eq_two hv
  have hdegree : 3 ≤ G.degree v :=
    degree_ge_three_of_minDegree_ge_three G hmin v
  have hambient : (G.neighborSet v).ncard = G.degree v := by
    rw [Set.ncard_eq_toFinset_card]
    simpa [SimpleGraph.neighborFinset_def] using
      (SimpleGraph.card_neighborFinset_eq_degree G v)
  rw [hambient, hcyclecard] at hcardle
  omega

/-- Two distinct vertices on a simple cycle determine two complementary
simple path arcs after rotating the cycle to the first vertex.-/
theorem SimpleGraph.Walk.IsCycle.exists_path_arcs
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {s : V} {c : G.Walk s s} (hc : c.IsCycle)
    {u v : V} (hu : u ∈ c.support) (hv : v ∈ c.support) (huv : u ≠ v) :
    ∃ (p : G.Path u v) (q : G.Path v u),
      (p : G.Walk u v).append (q : G.Walk v u) = c.rotate u hu := by
  let r := c.rotate u hu
  have hcr : r.IsCycle := by
    dsimp [r]
    exact hc.rotate hu
  have hv' : v ∈ r.support := by
    dsimp [r]
    exact (SimpleGraph.Walk.mem_support_rotate_iff c u hu).2 hv
  let p := r.takeUntil v hv'
  let q := r.dropUntil v hv'
  have hp : p.IsPath := by
    dsimp [p]
    exact hcr.isPath_takeUntil hv'
  have hq : q.IsPath := by
    have hcyc := hcr
    rw [← SimpleGraph.Walk.take_spec r hv'] at hcyc
    dsimp [p, q]
    exact hcyc.isPath_of_append_right
      (SimpleGraph.Walk.not_nil_of_ne huv)
  refine ⟨⟨p, hp⟩, ⟨q, hq⟩, ?_⟩
  simpa [p, q, r] using (SimpleGraph.Walk.take_spec r hv')

/- A globally shortest simple cycle has no chord: a chord splits it into two
shorter simple cycles, and the chord cannot coincide with either cycle arc. -/
theorem ShortestCycleCertificate.isChordless
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (certificate : ShortestCycleCertificate G) :
    certificate.cycle.IsChordless := by
  rw [SimpleGraph.Walk.isChordless_iff_forall_mem_edges]
  intro u v hu hv hadj
  by_contra hnot
  obtain ⟨p, q, hpq⟩ :=
    SimpleGraph.Walk.IsCycle.exists_path_arcs certificate.isCycle hu hv hadj.ne
  have hp_not_nil : ¬(p : G.Walk u v).Nil := by
    intro hnil
    exact hadj.ne ((p.property.nil_iff_eq).mp hnil)
  have hq_not_nil : ¬(q : G.Walk v u).Nil := by
    intro hnil
    exact hadj.ne.symm ((q.property.nil_iff_eq).mp hnil)
  have hp_len : 1 < (p : G.Walk u v).length := by
    have hp_pos : 0 < (p : G.Walk u v).length := by
      by_contra h
      have hzero : (p : G.Walk u v).length = 0 := Nat.eq_zero_of_not_pos h
      exact hp_not_nil (SimpleGraph.Walk.length_eq_zero_iff.mp hzero)
    by_contra hle
    have hple : (p : G.Walk u v).length ≤ 1 := Nat.le_of_not_gt hle
    have heq : (p : G.Walk u v) = hadj.toWalk :=
      SimpleGraph.Walk.eq_of_length_le_one hple (by simp)
    have hpedge : s(u, v) ∈ (p : G.Walk u v).edges := by
      rw [heq, hadj.edges_toWalk]
      simp
    have happedge : s(u, v) ∈
        ((p : G.Walk u v).append (q : G.Walk v u)).edges := by
      rw [SimpleGraph.Walk.edges_append]
      exact List.mem_append_left _ hpedge
    apply hnot
    exact (certificate.cycle.rotate_edges u hu).mem_iff.mp (by
      simpa [hpq] using happedge)
  have hq_len : 1 < (q : G.Walk v u).length := by
    have hq_pos : 0 < (q : G.Walk v u).length := by
      by_contra h
      have hzero : (q : G.Walk v u).length = 0 := Nat.eq_zero_of_not_pos h
      exact hq_not_nil (SimpleGraph.Walk.length_eq_zero_iff.mp hzero)
    by_contra hle
    have hqle : (q : G.Walk v u).length ≤ 1 := Nat.le_of_not_gt hle
    have heq : (q : G.Walk v u) = hadj.toWalk.reverse :=
      SimpleGraph.Walk.eq_of_length_le_one hqle (by simp)
    have hqedge : s(u, v) ∈ (q : G.Walk v u).edges := by
      rw [heq, SimpleGraph.Walk.edges_reverse, hadj.edges_toWalk]
      simp
    have happedge : s(u, v) ∈
        ((p : G.Walk u v).append (q : G.Walk v u)).edges := by
      rw [SimpleGraph.Walk.edges_append]
      exact List.mem_append_right _ hqedge
    apply hnot
    exact (certificate.cycle.rotate_edges u hu).mem_iff.mp (by
      simpa [hpq] using happedge)
  let chordBack : G.Walk v u := hadj.toWalk.reverse
  have hchordBack : chordBack.IsPath := by
    dsimp [chordBack]
    exact hadj.isPath_toWalk.reverse
  have hu_not_mem_tail : u ∉ (p : G.Walk u v).support.tail := by
    have hnodup : (u :: (p : G.Walk u v).support.tail).Nodup := by
      rw [(p : G.Walk u v).cons_tail_support]
      exact p.property.support_nodup
    exact (List.nodup_cons.mp hnodup).1
  have hdis :
      (p : G.Walk u v).support.tail.Disjoint chordBack.support.tail := by
    dsimp [chordBack]
    simp only [List.disjoint_left, List.mem_singleton]
    intro x hx hx'
    exact hu_not_mem_tail (by simpa [hx'] using hx)
  have hcycle :
      ((p : G.Walk u v).append chordBack).IsCycle :=
    p.property.isCycle_append hchordBack hdis (Or.inl hp_len)
  have hsum :
      certificate.cycle.length =
        (p : G.Walk u v).length + (q : G.Walk v u).length := by
    have hlength := congrArg SimpleGraph.Walk.length hpq
    simpa [SimpleGraph.Walk.length_append] using hlength.symm
  have hshorter :
      (p : G.Walk u v).length + 1 < certificate.cycle.length := by
    omega
  have hle := certificate.shortest u ((p : G.Walk u v).append chordBack) hcycle
  have hle' :
      certificate.cycle.length ≤ (p : G.Walk u v).length + 1 := by
    simpa [chordBack, SimpleGraph.Walk.length_append] using hle
  omega

/- Once shortestness has supplied chordlessness, the external-neighbor
conclusion needs no separate chordlessness hypothesis at call sites. -/
theorem ShortestCycleCertificate.exists_external_neighbor_of_minDegree_ge_three
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (certificate : ShortestCycleCertificate G)
    (hmin : G.minDegree ≥ 3)
    {v : V} (hv : v ∈ certificate.cycle.support) :
    ∃ w, G.Adj v w ∧ w ∉ certificate.cycle.support := by
  classical
  exact certificate.exists_external_neighbor_of_chordless
    certificate.isChordless hmin hv

/- A path from outside a cycle has an initial segment ending at its first
cycle vertex, with every earlier support vertex outside the cycle. -/
theorem _root_.SimpleGraph.Walk.exists_first_return_to_cycle
    {V : Type u} {G : SimpleGraph V} {s x y : V}
    {c : G.Walk s s} (_hc : c.IsCycle)
    (p : G.Walk x y) (hp : p.IsPath)
    (hx : x ∉ c.support) (hy : y ∈ c.support) :
    ∃ i : ℕ, 0 < i ∧ i ≤ p.length ∧ p.getVert i ∈ c.support ∧
      (p.take i).IsPath ∧ (p.take i).support.dropLast.Disjoint c.support := by
  classical
  have hex : ∃ i : ℕ, p.getVert i ∈ c.support :=
    ⟨p.length, by simpa using hy⟩
  let i := Nat.find hex
  have hi_cycle : p.getVert i ∈ c.support := Nat.find_spec hex
  have hi_le : i ≤ p.length := Nat.find_min' hex (by simpa using hy)
  have hi_pos : 0 < i := by
    apply Nat.pos_of_ne_zero
    intro hi_zero
    exact hx (by simpa [hi_zero] using hi_cycle)
  have htake_length : (p.take i).length = i := by
    rw [SimpleGraph.Walk.take_length]
    exact inf_eq_left.mpr hi_le
  refine ⟨i, hi_pos, hi_le, hi_cycle, hp.take i, ?_⟩
  apply List.disjoint_left.2
  intro z hz hz_cycle
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hz
  have hj_lt : j < i := by
    simpa only [List.length_dropLast, SimpleGraph.Walk.length_support,
      htake_length, Nat.add_sub_cancel] using hj
  have hj_cycle : p.getVert j ∈ c.support := by
    simpa only [List.getElem_dropLast,
      SimpleGraph.Walk.support_getElem_eq_getVert,
      SimpleGraph.Walk.take_getVert, inf_eq_right.mpr hj_lt.le] using hz_cycle
  have hi_le_j : i ≤ j := Nat.find_min' hex hj_cycle
  omega

/- A same-attachment first return is either the length-one backtrack or a
   genuine simple closed excursion obtained by prefixing the incident edge.
   The degenerate branch is kept explicit because it is not a bridge or a
   simple cycle. -/
theorem _root_.SimpleGraph.Walk.same_attachment_excursion
    {V : Type u} {G : SimpleGraph V} {a x y : V}
    (hax : G.Adj a x) (p : G.Walk x y) (hp : p.IsPath)
    {i : ℕ} (hi_pos : 0 < i) (hi_le : i ≤ p.length)
    (hreturn : p.getVert i = a) :
    (∃ c : G.Walk a a, c.IsCycle ∧ c.length = i + 1) ∨ i = 1 := by
  by_cases hi_two : 2 ≤ i
  · left
    let q : G.Walk x a := (p.take i).copy rfl hreturn
    have hq : q.IsPath := by
      simpa [q] using hp.take i
    have htake_length : (p.take i).length = i := by
      rw [SimpleGraph.Walk.take_length]
      exact inf_eq_left.mpr hi_le
    have hq_length : q.length = i := by
      simpa [q] using htake_length
    have hnot_edge : s(a, x) ∉ q.edges := by
      intro hedge
      have hlength_one :=
        hq.length_eq_one_of_mem_edges (Sym2.eq_swap ▸ hedge)
      omega
    have hcycle : (SimpleGraph.Walk.cons hax q).IsCycle :=
      (SimpleGraph.Walk.cons_isCycle_iff q hax).2 ⟨hq, hnot_edge⟩
    refine ⟨SimpleGraph.Walk.cons hax q, hcycle, ?_⟩
    simp [SimpleGraph.Walk.length_cons, hq_length]
  · right
    omega

/- A nondegenerate same-attachment excursion cannot be shorter than the
   globally shortest cycle. -/
theorem ShortestCycleCertificate.le_same_attachment_excursion_length
    {V : Type u} {G : SimpleGraph V}
    (certificate : ShortestCycleCertificate G)
    {a x : V} (hax : G.Adj a x) (p : G.Walk x a) (hp : p.IsPath)
    {i : ℕ} (hi_pos : 0 < i) (hi_le : i ≤ p.length)
    (hreturn : p.getVert i = a) (hi_two : 2 ≤ i) :
    certificate.cycle.length ≤ i + 1 := by
  obtain ⟨c, hc, hlength⟩ | hi_one :=
    SimpleGraph.Walk.same_attachment_excursion hax p hp
      hi_pos hi_le hreturn
  · have hle := certificate.shortest a c hc
    omega
  · omega

/- An incident edge in a connected graph either is a bridge or admits a
   path between its endpoints that avoids the edge. -/
theorem _root_.SimpleGraph.exists_path_avoiding_edge_or_isBridge
    {V : Type u} {G : SimpleGraph V}
    (hconn : G.Connected) {a x : V} (hax : G.Adj a x) :
    (∃ p : G.Walk x a, p.IsPath ∧ s(a, x) ∉ p.edges) ∨
      G.IsBridge s(a, x) := by
  classical
  by_cases hbridge : G.IsBridge s(a, x)
  · exact Or.inr hbridge
  · left
    have hdeleted :
        (G.deleteEdges {s(a, x)}).Connected :=
      hconn.connected_delete_edge_of_not_isBridge hbridge
    have hreachable :
        (G.deleteEdges {s(a, x)}).Reachable x a :=
      hdeleted.preconnected x a
    obtain ⟨p, hpedge⟩ :=
      (SimpleGraph.reachable_deleteEdges_iff_exists_walk).mp hreachable
    refine ⟨p.toPath, SimpleGraph.Path.isPath p.toPath, ?_⟩
    intro hedge
    exact hpedge (p.edges_toPath_subset_edges hedge)

/- A path external to a chosen cycle, together with its two attachment
   vertices. The path's interior is recorded separately so later bridge
   arguments can state disjointness without re-encoding its endpoints. -/
structure CycleBridgePath {V : Type u} (G : SimpleGraph V)
    {s : V} (cycle : G.Walk s s) where
  left : V
  right : V
  left_mem_cycle : left ∈ cycle.support
  right_mem_cycle : right ∈ cycle.support
  distinct_attachments : left ≠ right
  path : G.Walk left right
  isPath : path.IsPath
  interior_disjoint_cycle :
    path.support.tail.dropLast.Disjoint cycle.support

/- Package a selected first-return prefix as an external bridge. The
   first-return theorem supplies `hinterior`; no attachment distinctness is
   inferred beyond the explicit endpoint inequality. -/
def CycleBridgePath.of_first_return
    {V : Type u} {G : SimpleGraph V} {s a x y : V}
    {cycle : G.Walk s s} (_hcycle : cycle.IsCycle)
    (ha : a ∈ cycle.support) (_hx : x ∉ cycle.support)
    (hax : G.Adj a x) (p : G.Walk x y) (hp : p.IsPath)
    {i : ℕ} (hreturn : p.getVert i ∈ cycle.support)
    (hinterior : (p.take i).support.dropLast.Disjoint cycle.support)
    (hreturn_ne_a : p.getVert i ≠ a) :
    CycleBridgePath G cycle := by
  have ha_not_mem : a ∉ (p.take i).support := by
    intro ha_mem
    by_cases ha_drop : a ∈ (p.take i).support.dropLast
    · exact (List.disjoint_left.mp hinterior ha_drop) ha
    · have ha_last : a = (p.take i).support.getLast (by simp) := by
        by_contra ha_ne_last
        exact ha_drop
          (List.mem_dropLast_of_mem_of_ne_getLast ha_mem ha_ne_last)
      have ha_end : a = p.getVert i :=
        ha_last.trans (p.take i).getLast_support
      exact hreturn_ne_a ha_end.symm
  have hpath : (SimpleGraph.Walk.cons hax (p.take i)).IsPath :=
    (SimpleGraph.Walk.cons_isPath_iff hax (p.take i)).2
      ⟨hp.take i, ha_not_mem⟩
  refine
    { left := a
      right := p.getVert i
      left_mem_cycle := ha
      right_mem_cycle := hreturn
      distinct_attachments := hreturn_ne_a.symm
      path := SimpleGraph.Walk.cons hax (p.take i)
      isPath := hpath
      interior_disjoint_cycle := ?_ }
  simpa [SimpleGraph.Walk.support_cons] using hinterior

/- Connectedness and an external incident edge yield either a genuine bridge
or explicit same-attachment first-return data for the descent branch. -/
theorem CycleBridgePath.exists_of_connected_external_neighbor
    {V : Type u} {G : SimpleGraph V} {s a x : V}
    {cycle : G.Walk s s} (hcycle : cycle.IsCycle)
    (hconn : G.Connected) (ha : a ∈ cycle.support)
    (hx : x ∉ cycle.support) (hax : G.Adj a x) :
    (∃ bridge : CycleBridgePath G cycle, bridge.left = a) ∨
      ∃ (p : G.Walk x a) (i : ℕ),
        p.IsPath ∧ 0 < i ∧ i ≤ p.length ∧ p.getVert i = a ∧
          (p.take i).support.dropLast.Disjoint cycle.support := by
  obtain ⟨p, hp⟩ := hconn.exists_isPath x a
  obtain ⟨i, hi_pos, hi_le, hi_cycle, htake, hinterior⟩ :=
    SimpleGraph.Walk.exists_first_return_to_cycle hcycle p hp hx ha
  by_cases hne : p.getVert i ≠ a
  · left
    refine ⟨CycleBridgePath.of_first_return hcycle ha hx hax p hp
      hi_cycle hinterior hne, rfl⟩
  · right
    exact ⟨p, i, hp, hi_pos, hi_le, Classical.not_not.mp hne, hinterior⟩

/- Every shortest-cycle vertex has an external incident edge, and connectedness
   classifies its first return as either a genuine bridge or a same-attachment
   excursion. -/
theorem ShortestCycleCertificate.exists_attachment_or_same_return
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (certificate : ShortestCycleCertificate G)
    (hconn : G.Connected)
    (hmin : G.minDegree ≥ 3)
    {a : V} (ha : a ∈ certificate.cycle.support) :
    ∃ x, G.Adj a x ∧ x ∉ certificate.cycle.support ∧
      ((∃ bridge : CycleBridgePath G certificate.cycle,
          bridge.left = a) ∨
       ∃ (p : G.Walk x a) (i : ℕ),
          p.IsPath ∧ 0 < i ∧ i ≤ p.length ∧
            p.getVert i = a ∧
            (p.take i).support.dropLast.Disjoint certificate.cycle.support) := by
  obtain ⟨x, hax, hx⟩ :=
    certificate.exists_external_neighbor_of_minDegree_ge_three hmin ha
  obtain hbridge | hreturn :=
    CycleBridgePath.exists_of_connected_external_neighbor
      certificate.isCycle hconn ha hx hax
  · exact ⟨x, hax, hx, Or.inl hbridge⟩
  · exact ⟨x, hax, hx, Or.inr hreturn⟩

/-- Every bridge has two complementary simple cycle arcs between its
attachments, in the orientation obtained by rotating the cycle to the left
attachment.-/
theorem CycleBridgePath.exists_complementary_arcs
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {s : V}
    {cycle : G.Walk s s}
    (bridge : CycleBridgePath G cycle) (hcycle : cycle.IsCycle) :
    ∃ (p : G.Path bridge.left bridge.right)
      (q : G.Path bridge.right bridge.left),
      (p : G.Walk bridge.left bridge.right).append
          (q : G.Walk bridge.right bridge.left) =
        cycle.rotate bridge.left bridge.left_mem_cycle := by
  exact Erdos64.SimpleGraph.Walk.IsCycle.exists_path_arcs hcycle
    bridge.left_mem_cycle
    bridge.right_mem_cycle bridge.distinct_attachments

/-- The two complementary arcs supplied by
`CycleBridgePath.exists_complementary_arcs` have total length equal to the
cycle length.-/
theorem CycleBridgePath.complementary_arcs_length_add
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {s : V}
    {cycle : G.Walk s s}
    (bridge : CycleBridgePath G cycle)
    {p : G.Path bridge.left bridge.right}
    {q : G.Path bridge.right bridge.left}
    (hdecomp :
      (p : G.Walk bridge.left bridge.right).append
          (q : G.Walk bridge.right bridge.left) =
        cycle.rotate bridge.left bridge.left_mem_cycle) :
    (p : G.Walk bridge.left bridge.right).length +
        (q : G.Walk bridge.right bridge.left).length =
      cycle.length := by
  have hlength := congrArg SimpleGraph.Walk.length hdecomp
  simpa [SimpleGraph.Walk.length_append] using hlength

theorem CycleBridgePath.exists_complementary_arc_longer_than_one
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {s : V}
    {cycle : G.Walk s s}
    (bridge : CycleBridgePath G cycle) (hcycle : cycle.IsCycle) :
    ∃ (p : G.Path bridge.left bridge.right)
      (q : G.Path bridge.right bridge.left),
      (p : G.Walk bridge.left bridge.right).append
          (q : G.Walk bridge.right bridge.left) =
        cycle.rotate bridge.left bridge.left_mem_cycle ∧
      ((p : G.Walk bridge.left bridge.right).length > 1 ∨
        (q : G.Walk bridge.right bridge.left).length > 1) := by
  obtain ⟨p, q, hdecomp⟩ := bridge.exists_complementary_arcs hcycle
  refine ⟨p, q, hdecomp, ?_⟩
  by_contra hnot
  push_neg at hnot
  have hsum := bridge.complementary_arcs_length_add hdecomp
  have hcycle_length : 3 ≤ cycle.length := hcycle.three_le_length
  omega

/-- The internal vertices of a bridge path, excluding both attachments.-/
def CycleBridgePath.interior
    {V : Type u} {G : SimpleGraph V} {s : V}
    {cycle : G.Walk s s} (bridge : CycleBridgePath G cycle) : List V :=
  bridge.path.support.tail.dropLast

private lemma list_tail_dropLast_eq_dropLast_tail {α : Type _} : ∀ l : List α,
    l.tail.dropLast = l.dropLast.tail := by
  intro l
  cases l with
  | nil => rfl
  | cons a l =>
    cases l with
    | nil => rfl
    | cons b l =>
      induction l with
      | nil => rfl
      | cons c l ih =>
        simp [List.dropLast]

private lemma list_reverse_tail_dropLast {α : Type _} : ∀ l : List α,
    l.reverse.tail.dropLast = (l.tail.dropLast).reverse := by
  intro l
  rw [List.tail_reverse, List.dropLast_reverse]
  rw [list_tail_dropLast_eq_dropLast_tail]

/- Reversing an external bridge preserves its interior-disjointness
invariant. This supplies the symmetric orientation needed for the other
complementary cycle arc. -/
def CycleBridgePath.reverse
    {V : Type u} {G : SimpleGraph V} {s : V}
    {cycle : G.Walk s s}
    (bridge : CycleBridgePath G cycle) : CycleBridgePath G cycle where
  left := bridge.right
  right := bridge.left
  left_mem_cycle := bridge.right_mem_cycle
  right_mem_cycle := bridge.left_mem_cycle
  distinct_attachments := Ne.symm bridge.distinct_attachments
  path := bridge.path.reverse
  isPath := bridge.isPath.reverse
  interior_disjoint_cycle := by
    rw [SimpleGraph.Walk.support_reverse]
    have hrev := list_reverse_tail_dropLast bridge.path.support
    rw [hrev]
    rw [List.disjoint_left]
    intro x hxinterior hxcycle
    exact (List.disjoint_left.mp bridge.interior_disjoint_cycle
      (List.mem_reverse.mp hxinterior)) hxcycle

/- A cycle arc whose support lies on the chosen cycle is automatically
disjoint from the bridge interior, including the endpoint bookkeeping needed
for the two tails passed to `isCycle_append`. -/
theorem CycleBridgePath.tails_disjoint_of_arc_support_subset
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {s : V}
    {cycle : G.Walk s s}
    (bridge : CycleBridgePath G cycle)
    {arc : G.Walk bridge.left bridge.right}
    (arc_isPath : arc.IsPath)
    (arc_support_subset : arc.support ⊆ cycle.support) :
    bridge.path.support.tail.Disjoint arc.reverse.support.tail := by
  rw [List.disjoint_left]
  intro x hxpath
  intro hxarc
  have htail_ne_nil : bridge.path.support.tail ≠ [] := by
    intro hnil
    have : bridge.right ∉ bridge.path.support.tail := by simpa [hnil]
    exact this (SimpleGraph.Walk.end_mem_tail_support_of_ne
      bridge.distinct_attachments bridge.path)
  have hxarc_support : x ∈ arc.reverse.support := List.mem_of_mem_tail hxarc
  have hxcycle : x ∈ cycle.support := by
    apply arc_support_subset
    rw [SimpleGraph.Walk.support_reverse] at hxarc_support
    exact List.mem_reverse.mp hxarc_support
  have hnotdrop : x ∉ bridge.path.support.tail.dropLast := by
    intro hxdrop
    exact (List.disjoint_left.mp bridge.interior_disjoint_cycle hxdrop) hxcycle
  by_cases hlast : x = bridge.path.support.tail.getLast htail_ne_nil
  · have hlast_right : bridge.path.support.tail.getLast htail_ne_nil = bridge.right := by
      rw [List.getLast_tail]
      exact bridge.path.getLast_support
    have hnotstart : bridge.right ∉ arc.reverse.support.tail := by
      intro hmem
      have hnodup : arc.reverse.support.Nodup := arc_isPath.reverse.support_nodup
      have hnodup' := hnodup
      rw [← SimpleGraph.Walk.cons_tail_support arc.reverse] at hnodup'
      exact (List.nodup_cons.mp hnodup').1 hmem
    have hmem' : bridge.path.support.tail.getLast htail_ne_nil ∈
        arc.reverse.support.tail := by
      exact hlast.symm ▸ hxarc
    have heq :
        (bridge.path.support.tail.getLast htail_ne_nil ∈ arc.reverse.support.tail) =
          (bridge.right ∈ arc.reverse.support.tail) :=
      congrArg (fun z : V => z ∈ arc.reverse.support.tail) hlast_right
    exact hnotstart (heq.mp hmem')
  · exact hnotdrop (List.mem_dropLast_of_mem_of_ne_getLast hxpath hlast)

/-- An external bridge path and an explicitly supplied cycle arc with the
same endpoints form a simple cycle when their tails are disjoint.-/
theorem CycleBridgePath.cycle_of_arc
    {V : Type u} {G : SimpleGraph V} {s : V}
    {cycle : G.Walk s s}
    (bridge : CycleBridgePath G cycle)
    {arc : G.Walk bridge.left bridge.right}
    (arc_isPath : arc.IsPath)
    (tails_disjoint :
      bridge.path.support.tail.Disjoint arc.reverse.support.tail)
    (length_condition :
      1 < bridge.path.length ∨ 1 < arc.length) :
    ∃ c : G.Walk bridge.left bridge.left,
      c.IsCycle ∧ c.length = bridge.path.length + arc.length := by
  let c := bridge.path.append arc.reverse
  refine ⟨c, ?_, ?_⟩
  · exact bridge.isPath.isCycle_append arc_isPath.reverse tails_disjoint
      (by simpa [SimpleGraph.Walk.length_reverse] using length_condition)
  · simp [c, SimpleGraph.Walk.length_append,
      SimpleGraph.Walk.length_reverse, Nat.add_comm]

/- The complementary-arc decomposition supplies the support containment
needed by `tails_disjoint_of_arc_support_subset`, so the bridge construction
can be applied directly to an extracted cycle arc. -/
theorem CycleBridgePath.cycle_of_extracted_arc
    {V : Type u} {G : SimpleGraph V} [DecidableEq V] {s : V}
    {cycle : G.Walk s s}
    (bridge : CycleBridgePath G cycle)
    {p : G.Path bridge.left bridge.right}
    {q : G.Path bridge.right bridge.left}
    (hdecomp :
      (p : G.Walk bridge.left bridge.right).append
          (q : G.Walk bridge.right bridge.left) =
        cycle.rotate bridge.left bridge.left_mem_cycle)
    (hlength :
      1 < bridge.path.length ∨
        1 < (p : G.Walk bridge.left bridge.right).length) :
    ∃ c : G.Walk bridge.left bridge.left,
      c.IsCycle ∧ c.length =
        bridge.path.length + (p : G.Walk bridge.left bridge.right).length := by
  have hp_sub_rotate :
      (p : G.Walk bridge.left bridge.right).support ⊆
        (cycle.rotate bridge.left bridge.left_mem_cycle).support := by
    intro x hx
    have hxappend : x ∈
        ((p : G.Walk bridge.left bridge.right).append
          (q : G.Walk bridge.right bridge.left)).support := by
      simp [hx]
    rw [hdecomp] at hxappend
    exact hxappend
  have hp_sub_cycle :
      (p : G.Walk bridge.left bridge.right).support ⊆ cycle.support := by
    intro x hx
    exact (SimpleGraph.Walk.mem_support_rotate_iff cycle bridge.left
      bridge.left_mem_cycle).mp (hp_sub_rotate hx)
  have hdisjoint := bridge.tails_disjoint_of_arc_support_subset
    p.property hp_sub_cycle
  exact bridge.cycle_of_arc p.property hdisjoint hlength

/-- Expose the bridge-plus-arc construction directly as a cycle-length
  witness for the arithmetic layer.-/
theorem CycleBridgePath.hasSimpleCycleOfLength_of_arc
    {V : Type u} {G : SimpleGraph V} {s : V}
    {cycle : G.Walk s s}
    (bridge : CycleBridgePath G cycle)
    {arc : G.Walk bridge.left bridge.right}
    (arc_isPath : arc.IsPath)
    (tails_disjoint :
      bridge.path.support.tail.Disjoint arc.reverse.support.tail)
    (length_condition :
      1 < bridge.path.length ∨ 1 < arc.length) :
    HasSimpleCycleOfLength G (bridge.path.length + arc.length) := by
  obtain ⟨c, hc, hlength⟩ :=
    bridge.cycle_of_arc arc_isPath tails_disjoint length_condition
  exact ⟨bridge.left, c, hc, hlength⟩

/-- A bridge-plus-arc cycle cannot be shorter than a globally shortest cycle.-/
theorem ShortestCycleCertificate.le_bridge_arc_length
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (certificate : ShortestCycleCertificate G)
    (bridge : CycleBridgePath G certificate.cycle)
    {arc : G.Walk bridge.left bridge.right}
    (arc_isPath : arc.IsPath)
    (tails_disjoint :
      bridge.path.support.tail.Disjoint arc.reverse.support.tail)
    (length_condition :
      1 < bridge.path.length ∨ 1 < arc.length) :
    certificate.cycle.length ≤ bridge.path.length + arc.length := by
  obtain ⟨c, hc, hlength⟩ :=
    bridge.cycle_of_arc arc_isPath tails_disjoint length_condition
  have hle := certificate.shortest bridge.left c hc
  omega

/- The reversed bridge gives the corresponding restriction for an arc in the
opposite orientation. -/
theorem ShortestCycleCertificate.le_reverse_bridge_arc_length
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (certificate : ShortestCycleCertificate G)
    (bridge : CycleBridgePath G certificate.cycle)
    {arc : G.Walk bridge.right bridge.left}
    (arc_isPath : arc.IsPath)
    (arc_support_subset : arc.support ⊆ certificate.cycle.support)
    (length_condition :
      1 < bridge.path.length ∨ 1 < arc.length) :
    certificate.cycle.length ≤ bridge.path.length + arc.length := by
  have hdisjoint := bridge.reverse.tails_disjoint_of_arc_support_subset
    arc_isPath arc_support_subset
  have hlength' :
      1 < bridge.reverse.path.length ∨ 1 < arc.length := by
    simpa [CycleBridgePath.reverse, SimpleGraph.Walk.length_reverse]
      using length_condition
  obtain ⟨c, hc, hcycle_length⟩ :=
    bridge.reverse.cycle_of_arc arc_isPath hdisjoint hlength'
  have hle := certificate.shortest bridge.right c hc
  have hresult :
      certificate.cycle.length ≤ bridge.reverse.path.length + arc.length := by
    calc
      certificate.cycle.length ≤ c.length := hle
      _ = bridge.reverse.path.length + arc.length := hcycle_length
  simpa [CycleBridgePath.reverse, SimpleGraph.Walk.length_reverse] using hresult

/- The same shortest-cycle restriction applies directly to an arc extracted
from the rotated cycle decomposition. -/
theorem ShortestCycleCertificate.le_extracted_arc_length
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (certificate : ShortestCycleCertificate G)
    (bridge : CycleBridgePath G certificate.cycle)
    {p : G.Path bridge.left bridge.right}
    {q : G.Path bridge.right bridge.left}
    (hdecomp :
      (p : G.Walk bridge.left bridge.right).append
          (q : G.Walk bridge.right bridge.left) =
        certificate.cycle.rotate bridge.left bridge.left_mem_cycle)
    (hlength :
      1 < bridge.path.length ∨
        1 < (p : G.Walk bridge.left bridge.right).length) :
    certificate.cycle.length ≤
      bridge.path.length + (p : G.Walk bridge.left bridge.right).length := by
  obtain ⟨c, hc, hcycle_length⟩ :=
    bridge.cycle_of_extracted_arc hdecomp hlength
  have hle := certificate.shortest bridge.left c hc
  omega

/- A shortest cycle forces each complementary cycle arc of an external bridge
to be no longer than the bridge itself, once both reroutings are valid. -/
theorem ShortestCycleCertificate.complementary_arc_le_bridge_length
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    (certificate : ShortestCycleCertificate G)
    (bridge : CycleBridgePath G certificate.cycle)
    {p : G.Path bridge.left bridge.right}
    {q : G.Path bridge.right bridge.left}
    (hdecomp :
      (p : G.Walk bridge.left bridge.right).append
          (q : G.Walk bridge.right bridge.left) =
        certificate.cycle.rotate bridge.left bridge.left_mem_cycle)
    (hp :
      1 < bridge.path.length ∨
        (p : G.Walk bridge.left bridge.right).length > 1)
    (hq :
      1 < bridge.path.length ∨
        (q : G.Walk bridge.right bridge.left).length > 1) :
    (p : G.Walk bridge.left bridge.right).length ≤ bridge.path.length ∧
      (q : G.Walk bridge.right bridge.left).length ≤ bridge.path.length := by
  have hp_sub_cycle :
      (p : G.Walk bridge.left bridge.right).support ⊆
        certificate.cycle.support := by
    intro x hx
    have hxappend : x ∈
        ((p : G.Walk bridge.left bridge.right).append
          (q : G.Walk bridge.right bridge.left)).support := by
      simp [hx]
    rw [hdecomp] at hxappend
    exact (SimpleGraph.Walk.mem_support_rotate_iff certificate.cycle
      bridge.left bridge.left_mem_cycle).mp hxappend
  have hq_sub_cycle :
      (q : G.Walk bridge.right bridge.left).support ⊆
        certificate.cycle.support := by
    intro x hx
    have hxappend : x ∈
        ((p : G.Walk bridge.left bridge.right).append
          (q : G.Walk bridge.right bridge.left)).support := by
      simp [hx]
    rw [hdecomp] at hxappend
    exact (SimpleGraph.Walk.mem_support_rotate_iff certificate.cycle
      bridge.left bridge.left_mem_cycle).mp hxappend
  have hp_bound := certificate.le_extracted_arc_length
    bridge hdecomp hp
  have hq_bound := certificate.le_reverse_bridge_arc_length
    bridge q.property hq_sub_cycle hq
  have hsum := bridge.complementary_arcs_length_add hdecomp
  constructor <;> omega

/-- A smaller counterexample suitable for a minimality contradiction.-/
def IsStrictlySmallerCounterexample
    {V W : Type u} (G : SimpleGraph V) (H : SimpleGraph W)
    [Fintype V] [DecidableRel G.Adj] [Fintype W] [DecidableRel H.Adj] : Prop :=
  IsCounterexample H ∧ Fintype.card W < Fintype.card V

/-- A counterexample together with the vertex-cardinality minimality needed
to close a descent argument. Existence of such an object is a separate
well-founded selection theorem.-/
structure MinimalCounterexample
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] : Prop where
  isCounterexample : IsCounterexample G
  minimal :
    ∀ (W : Type u) (H : SimpleGraph W)
      [Fintype W] [DecidableRel H.Adj],
      IsCounterexample H → Fintype.card V ≤ Fintype.card W

theorem exists_minimalCounterexample
    (hnot :
      ¬ (∀ (V : Type u) (G : SimpleGraph V) [Fintype V]
          [DecidableRel G.Adj],
        G.minDegree ≥ 3 → HasPowerOfTwoCycle G)) :
    ∃ (V : Type u) (G : SimpleGraph V) (_ : Fintype V)
      (_ : DecidableRel G.Adj), MinimalCounterexample G := by
  classical
  let P : ℕ → Prop :=
    fun n =>
      ∃ (W : Type u) (H : SimpleGraph W) (_ : Fintype W)
        (_ : DecidableRel H.Adj),
        Fintype.card W = n ∧ IsCounterexample H
  have hP : ∃ n, P n := by
    by_contra hP
    apply hnot
    intro V G instV instD hmin
    by_contra hno
    apply hP
    refine ⟨Fintype.card V, V, G, instV, instD, rfl, ?_⟩
    exact ⟨hmin, hno⟩
  let n := Nat.find hP
  obtain ⟨W, H, hW, hD, hcard, hcounter⟩ := Nat.find_spec hP
  letI : Fintype W := hW
  letI : DecidableRel H.Adj := hD
  refine ⟨W, H, hW, hD, ?_⟩
  refine
    { isCounterexample := hcounter
      minimal := ?_ }
  intro W' H' hW' hD' hcounter'
  calc
    Fintype.card W = n := hcard
    _ ≤ Fintype.card W' := by
      apply Nat.find_min' hP
      exact ⟨W', H', hW', hD', rfl, hcounter'⟩

/-- A vertex-minimal counterexample that is also minimal under edge deletion.

The edge-minimality field concerns deletion on the same vertex type. The
selection theorem below supplies such an object from a vertex-minimal
counterexample. It does not minimize the edge count over all counterexamples
of that order; comparing unrelated same-order graphs needs that stronger
selection principle, supplied separately in `GlobalEdgeMinimalCounterexample`.
The two interfaces are deliberately distinct.-/
structure EdgeMinimalCounterexample
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] : Prop where
  vertexMinimal : MinimalCounterexample G
  edgeMinimal :
    ∀ (H : SimpleGraph V) [DecidableRel H.Adj],
      IsCounterexample H → H ≤ G → H = G

theorem MinimalCounterexample.exists_edgeMinimalCounterexample
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : MinimalCounterexample G) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      EdgeMinimalCounterexample H := by
  classical
  let P : SimpleGraph V → Prop :=
    fun H =>
      ∃ hH : DecidableRel H.Adj,
        @IsCounterexample V H _ hH ∧ H ≤ G
  let S : Finset ℕ :=
    (Finset.univ.filter P).image (fun H => H.edgeSet.ncard)
  have hGmem : G ∈ Finset.univ.filter P := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    exact ⟨inferInstance, minimalCounterexample.isCounterexample, le_rfl⟩
  have hS : S.Nonempty := by
    refine ⟨G.edgeSet.ncard, ?_⟩
    exact Finset.mem_image.mpr
      ⟨G, hGmem, rfl⟩
  let n : ℕ := S.min' hS
  obtain ⟨H, hHmem, hHcard⟩ :=
    Finset.mem_image.mp (Finset.min'_mem S hS)
  obtain ⟨_, hHdata⟩ := Finset.mem_filter.mp hHmem
  obtain ⟨hHdec, hHcounter, hHle⟩ := hHdata
  letI : DecidableRel H.Adj := hHdec
  refine ⟨H, hHdec, ?_⟩
  refine
    { vertexMinimal :=
        { isCounterexample := hHcounter
          minimal := ?_ }
      edgeMinimal := ?_ }
  · intro W K _ _ hKcounter
    exact minimalCounterexample.minimal W K hKcounter
  · intro K _ hKcounter hKH
    have hKG : K ≤ G := hKH.trans hHle
    have hKmem : K ∈ Finset.univ.filter P :=
      Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ⟨inferInstance, hKcounter, hKG⟩⟩
    have hKcardmem : K.edgeSet.ncard ∈ S :=
      Finset.mem_image.mpr
        ⟨K, hKmem, rfl⟩
    have hmin : S.min' hS ≤ K.edgeSet.ncard :=
      Finset.min'_le S _ hKcardmem
    have hcardKH : K.edgeSet.ncard ≤ H.edgeSet.ncard :=
      Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hKH)
    have hcardeq : H.edgeSet.ncard = K.edgeSet.ncard := by
      omega
    apply (SimpleGraph.edgeSet_inj).mp
    exact Set.eq_of_subset_of_ncard_le
      (SimpleGraph.edgeSet_mono hKH) (by omega)

/-- Minimality rules out the descent branch of the dichotomy.-/
theorem MinimalCounterexample.not_exists_strictly_smaller
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (minimalCounterexample : MinimalCounterexample G)
    {W : Type u} {H : SimpleGraph W}
    [Fintype W] [DecidableRel H.Adj]
    (hsmaller : IsStrictlySmallerCounterexample G H) :
    False := by
  have hcard :
      Fintype.card V ≤ Fintype.card W :=
    minimalCounterexample.minimal W H hsmaller.1
  exact (Nat.not_lt_of_ge hcard) hsmaller.2

/-- A minimal counterexample is connected: a proper connected component would
give a smaller counterexample with the same minimum-degree lower bound.-/
theorem MinimalCounterexample.isConnected
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (minimalCounterexample : MinimalCounterexample G) :
    G.Connected := by
  classical
  haveI : Nonempty V := by
    by_contra hV
    letI : IsEmpty V := ⟨fun v => hV ⟨v⟩⟩
    have hmin : (3 : ℕ) ≤ 0 := by
      simpa using minimalCounterexample.isCounterexample.1
    omega
  refine { preconnected := ?_ }
  intro u w
  by_contra hnot
  let C := G.connectedComponentMk u
  let H := C.toSimpleGraph
  letI : Nonempty C := C.nonempty_supp.to_subtype
  have hwC : w ∉ C.supp := by
    intro hw
    have heq : G.connectedComponentMk w = C :=
      (SimpleGraph.ConnectedComponent.mem_supp_iff C w).mp hw
    apply hnot
    apply SimpleGraph.ConnectedComponent.eq.mp
    simpa [C] using heq.symm
  have hcard : Fintype.card C < Fintype.card V :=
    Fintype.card_subtype_lt hwC
  have hHmin : H.minDegree ≥ 3 := by
    apply H.le_minDegree_of_forall_le_degree
    intro v
    have hdegree : 3 ≤ G.degree v.1 :=
      degree_ge_three_of_minDegree_ge_three G
        minimalCounterexample.isCounterexample.1 v.1
    have hdegree_eq : H.degree v = G.degree v.1 := by
      let e : H.neighborSet v ≃ G.neighborSet v.1 :=
        { toFun := fun z =>
            ⟨z.1.1, by
              apply (G.mem_neighborSet _ _).2
              exact (C.toSimpleGraph_adj v.2 z.1.2).1
                ((H.mem_neighborSet _ _).1 z.2)⟩
          invFun := fun z =>
            ⟨⟨z.1, C.mem_supp_of_adj_mem_supp v.2
                ((G.mem_neighborSet _ _).1 z.2)⟩, by
              apply (H.mem_neighborSet _ _).2
              exact (C.toSimpleGraph_adj v.2 _).2
                ((G.mem_neighborSet _ _).1 z.2)⟩
          left_inv := by
            intro z
            apply Subtype.ext
            rfl
          right_inv := by
            intro z
            rfl }
      simpa only [SimpleGraph.card_neighborSet_eq_degree] using
        Fintype.card_congr e
    rw [hdegree_eq]
    exact hdegree
  have hHno : ¬ HasPowerOfTwoCycle H := by
    intro hcycle
    apply minimalCounterexample.isCounterexample.2
    rcases hcycle with ⟨k, v, c, hk, hc, hlen⟩
    refine ⟨k, C.toSimpleGraph_hom v, c.map C.toSimpleGraph_hom, hk, ?_, ?_⟩
    · exact hc.map Subtype.val_injective
    · rw [SimpleGraph.Walk.length_map]
      exact hlen
  have hsmaller : IsStrictlySmallerCounterexample G H :=
    ⟨⟨hHmin, hHno⟩, hcard⟩
  exact minimalCounterexample.not_exists_strictly_smaller hsmaller

/-- The proof shape required from the graph-theoretic forcing argument.-/
def HasDyadicCertificateOrDescent
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableRel G.Adj] : Prop :=
  HasPowerOfTwoCycle G ∨
    ∃ (W : Type u) (H : SimpleGraph W) (_ : Fintype W)
      (_ : DecidableRel H.Adj),
      IsStrictlySmallerCounterexample G H

/-- The dichotomy closes a minimal counterexample once its forcing theorem is
available.-/
theorem MinimalCounterexample.hasPowerOfTwoCycle_of_dichotomy
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableRel G.Adj]
    (minimalCounterexample : MinimalCounterexample G)
    (hdichotomy : HasDyadicCertificateOrDescent G) :
    HasPowerOfTwoCycle G := by
  rcases hdichotomy with hcycle | ⟨W, H, _, _, hsmaller⟩
  · exact hcycle
  · exact (minimalCounterexample.not_exists_strictly_smaller hsmaller).elim

theorem conjecture_of_minimal_counterexample_dichotomy
    (hforcing :
      ∀ (V : Type u) (G : SimpleGraph V) [Fintype V]
        [DecidableRel G.Adj],
        MinimalCounterexample G → HasDyadicCertificateOrDescent G) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V]
      [DecidableRel G.Adj],
      G.minDegree ≥ 3 → HasPowerOfTwoCycle G := by
  classical
  intro V G hV hD hmin
  letI : Fintype V := hV
  letI : DecidableRel G.Adj := hD
  by_contra hno
  have hnot :
      ¬ (∀ (W : Type u) (K : SimpleGraph W) [Fintype W]
          [DecidableRel K.Adj],
        K.minDegree ≥ 3 → HasPowerOfTwoCycle K) := by
    intro hall
    exact hno (hall V G hmin)
  obtain ⟨W, K, hW, hK, hminimal⟩ :=
    exists_minimalCounterexample hnot
  letI : Fintype W := hW
  letI : DecidableRel K.Adj := hK
  exact hminimal.isCounterexample.2
    (hminimal.hasPowerOfTwoCycle_of_dichotomy
      (hforcing W K hminimal))

theorem conjecture_of_edgeMinimal_counterexample_dichotomy
    (hforcing :
      ∀ (V : Type u) (G : SimpleGraph V) [Fintype V]
        [DecidableRel G.Adj],
        EdgeMinimalCounterexample G → HasDyadicCertificateOrDescent G) :
    ∀ (V : Type u) (G : SimpleGraph V) [Fintype V]
      [DecidableRel G.Adj],
      G.minDegree ≥ 3 → HasPowerOfTwoCycle G := by
  classical
  intro V G hV hD hmin
  letI : Fintype V := hV
  letI : DecidableRel G.Adj := hD
  by_contra hno
  have hnot :
      ¬ (∀ (W : Type u) (K : SimpleGraph W) [Fintype W]
          [DecidableRel K.Adj],
        K.minDegree ≥ 3 → HasPowerOfTwoCycle K) := by
    intro hall
    exact hno (hall V G hmin)
  obtain ⟨W, K, hW, hK, hminimal⟩ :=
    exists_minimalCounterexample hnot
  letI : Fintype W := hW
  letI : DecidableRel K.Adj := hK
  obtain ⟨H, hH, hedge⟩ :=
    hminimal.exists_edgeMinimalCounterexample
  letI : DecidableRel H.Adj := hH
  exact hedge.vertexMinimal.isCounterexample.2
    (hedge.vertexMinimal.hasPowerOfTwoCycle_of_dichotomy
      (hforcing W H hedge))

/-- The number of neighbors of `v` contained in a finite vertex set.-/
def internalDegree {V : Type u} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] (S : Finset V) (v : V) : ℕ :=
  (S.filter (G.Adj v)).card

/-- A finite graph is critical for the minimum-degree-three property if no
proper nonempty induced vertex set still has minimum degree three.-/
def IsSubgraphCritical {V : Type u} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] : Prop :=
  ∀ S : Finset V, S.Nonempty → S ≠ Finset.univ →
    ∃ v, v ∈ S ∧ internalDegree G S v ≤ 2

/-- A vertex-minimal counterexample has no proper induced subgraph of minimum
degree at least three.-/
theorem MinimalCounterexample.isSubgraphCritical
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : MinimalCounterexample G) :
    IsSubgraphCritical G := by
  classical
  intro S hS hSproper
  by_contra hnot
  have hdegree : ∀ v, v ∈ S → 3 ≤ internalDegree G S v := by
    intro v hv
    by_contra hlt
    have hle : internalDegree G S v ≤ 2 := by omega
    exact hnot ⟨v, hv, hle⟩
  let W := (↑S : Set V)
  let H : SimpleGraph W := G.induce (↑S : Set V)
  letI : Nonempty W := hS.to_subtype
  have hHmin : H.minDegree ≥ 3 := by
    apply SimpleGraph.le_minDegree_of_forall_le_degree (G := H) 3
    intro v
    have hcard :
        (G.induce (↑S : Set V)).degree v =
          internalDegree G S v.1 := by
      change ((G.induce (↑S : Set V)).neighborFinset v).card =
        (S.filter (G.Adj v.1)).card
      have hfin :
          (((G.induce (↑S : Set V)).neighborFinset v).map
              (.subtype (· ∈ (↑S : Set V)))) =
            G.neighborFinset v ∩ (↑S : Set V).toFinset := by
        ext w
        simp [SimpleGraph.neighborFinset_eq_filter]
      have hcardmap := congrArg Finset.card hfin
      have hinter :
          G.neighborFinset v ∩ (↑S : Set V).toFinset =
            S.filter (G.Adj v.1) := by
        ext w
        simp [SimpleGraph.neighborFinset_eq_filter, and_comm]
      calc
        ((G.induce (↑S : Set V)).neighborFinset v).card =
            (((G.induce (↑S : Set V)).neighborFinset v).map
              (.subtype (· ∈ (↑S : Set V)))).card := by
                rw [Finset.card_map]
        _ = (G.neighborFinset v ∩ (↑S : Set V).toFinset).card := hcardmap
        _ = (S.filter (G.Adj v.1)).card := congrArg Finset.card hinter
    have hcardH : H.degree v = internalDegree G S v.1 := by
      simpa only [H] using hcard
    exact hcardH ▸ hdegree v.1 v.2
  have hHcounter : IsCounterexample H := by
    refine ⟨hHmin, ?_⟩
    intro hpow
    rcases hpow with ⟨k, v, c, hk, hc, hlen⟩
    let c' :=
      c.map (SimpleGraph.Embedding.induce (G := G)
        (s := (↑S : Set V))).toHom
    have hc' : c'.IsCycle := by
      dsimp [c']
      exact hc.map Subtype.val_injective
    have hlen' : c'.length = 2 ^ k := by
      dsimp [c']
      exact (SimpleGraph.Walk.length_map
        (SimpleGraph.Embedding.induce (G := G)
          (s := (↑S : Set V))).toHom c).trans hlen
    exact minimalCounterexample.isCounterexample.2
      ⟨k, (SimpleGraph.Embedding.induce (G := G)
        (s := (↑S : Set V))).toHom v, c', hk, hc', hlen'⟩
  have hcardS : S.card < (Finset.univ : Finset V).card := by
    apply Finset.card_lt_card
    exact Finset.ssubset_iff_subset_ne.mpr
      ⟨Finset.subset_univ S, hSproper⟩
  have hminimal := minimalCounterexample.minimal W H hHcounter
  have hcardW : Fintype.card W = S.card := by
    simpa [W] using Fintype.card_coe S
  have hcardV : Fintype.card V = (Finset.univ : Finset V).card := by simp
  rw [hcardW, hcardV] at hminimal
  omega

theorem internalDegree_erase_add_one_of_adj
    {V : Type u} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj] {v w : V}
    (hvw : G.Adj v w) :
    internalDegree G (Finset.univ.erase v) w + 1 = G.degree w := by
  classical
  have hfin :
      (Finset.univ.erase v).filter (G.Adj w) =
        (G.neighborFinset w).erase v := by
    ext x
    simp [SimpleGraph.neighborFinset_eq_filter, and_comm]
  rw [internalDegree, hfin, Finset.card_erase_of_mem]
  · change (G.neighborFinset w).card - 1 + 1 =
      (G.neighborFinset w).card
    have hv_mem : v ∈ G.neighborFinset w := by
      simpa [SimpleGraph.neighborFinset_eq_filter] using hvw.symm
    have hpos : 0 < (G.neighborFinset w).card :=
      Finset.card_pos.mpr ⟨v, hv_mem⟩
    omega
  · simpa [SimpleGraph.neighborFinset_eq_filter] using hvw.symm

theorem MinimalCounterexample.exists_adjacent_degree_eq_three
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : MinimalCounterexample G) (v : V) :
    ∃ w, G.Adj v w ∧ G.degree w = 3 := by
  classical
  have hmin := minimalCounterexample.isCounterexample.1
  have hvdeg := degree_ge_three_of_minDegree_ge_three G hmin v
  obtain ⟨u, huv⟩ :=
    (G.degree_pos_iff_exists_adj v).mp (by omega)
  let S : Finset V := Finset.univ.erase v
  have hS_nonempty : S.Nonempty := by
    refine ⟨u, ?_⟩
    simp [S, huv.ne.symm]
  have hS_proper : S ≠ Finset.univ := by
    intro hS
    have hvS : v ∈ S := hS ▸ Finset.mem_univ v
    simpa [S] using hvS
  obtain ⟨w, _, hwlow⟩ :=
    minimalCounterexample.isSubgraphCritical S hS_nonempty hS_proper
  have hwd : 3 ≤ G.degree w :=
    degree_ge_three_of_minDegree_ge_three G hmin w
  have hadj : G.Adj v w := by
    by_contra hnot
    have hnot' : ¬G.Adj w v := fun h => hnot h.symm
    have hfin :
        S.filter (G.Adj w) = G.neighborFinset w := by
      ext x
      by_cases hx : x = v
      · subst x
        simp [S, SimpleGraph.neighborFinset_eq_filter, hnot']
      · simp [S, SimpleGraph.neighborFinset_eq_filter, hx]
    have hinter : internalDegree G S w = G.degree w := by
      change (S.filter (G.Adj w)).card = G.degree w
      rw [hfin]
      rfl
    have hlow' : 3 ≤ internalDegree G S w := by
      rw [hinter]
      exact hwd
    omega
  have hsum :=
    internalDegree_erase_add_one_of_adj G hadj
  have hsum' : internalDegree G S w + 1 = G.degree w := by
    simpa [S] using hsum
  refine ⟨w, hadj, ?_⟩
  omega

theorem neighborFinset_deleteEdges_singleton_eq_erase
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) :
    (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).neighborFinset u =
      (G.neighborFinset u).erase v := by
  classical
  ext x
  simp only [SimpleGraph.neighborFinset_eq_filter, Finset.mem_filter,
    Finset.mem_erase, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, hAdj, hne⟩
    refine ⟨?_, Finset.mem_univ _, hAdj⟩
    intro hxv
    apply hne
    simpa [hxv]
  · rintro ⟨hxv, _, hAdj⟩
    refine ⟨Finset.mem_univ _, hAdj, ?_⟩
    intro heq
    rcases Sym2.eq_iff.mp heq with hcases | hcases
    · exact hxv hcases.2
    · exact huv.ne hcases.1

theorem neighborFinset_deleteEdges_singleton_eq_erase_right
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v : V} (huv : G.Adj u v) :
    (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).neighborFinset v =
      (G.neighborFinset v).erase u := by
  classical
  ext x
  simp only [SimpleGraph.neighborFinset_eq_filter, Finset.mem_filter,
    Finset.mem_erase, SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, hAdj, hne⟩
    refine ⟨?_, Finset.mem_univ _, hAdj⟩
    intro hxu
    apply hne
    rw [hxu, Sym2.eq_swap]
  · rintro ⟨hxu, _, hAdj⟩
    refine ⟨Finset.mem_univ _, hAdj, ?_⟩
    intro heq
    rcases Sym2.eq_iff.mp heq with hcases | hcases
    · exact huv.ne hcases.1.symm
    · exact hxu hcases.2

theorem neighborFinset_deleteEdges_singleton_eq_self_of_ne
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {u v x : V} (huv : G.Adj u v) (hxu : x ≠ u) (hxv : x ≠ v) :
    (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).neighborFinset x =
      G.neighborFinset x := by
  classical
  ext y
  simp only [SimpleGraph.neighborFinset_eq_filter, Finset.mem_filter,
    SimpleGraph.deleteEdges_adj, Set.mem_singleton_iff]
  constructor
  · rintro ⟨_, hAdj, hne⟩
    exact ⟨Finset.mem_univ _, hAdj⟩
  · rintro ⟨_, hAdj⟩
    refine ⟨Finset.mem_univ _, hAdj, ?_⟩
    intro heq
    rcases Sym2.eq_iff.mp heq with hcases | hcases
    · exact hxu hcases.1
    · exact hxv hcases.1

theorem minDegree_deleteEdges_singleton_ge_three
    {V : Type u} (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (hmin : G.minDegree ≥ 3) {u v : V} (huv : G.Adj u v)
    (hu : 4 ≤ G.degree u) (hv : 4 ≤ G.degree v) :
    (G.deleteEdges ({s(u, v)} : Set (Sym2 V))).minDegree ≥ 3 := by
  classical
  let H := G.deleteEdges ({s(u, v)} : Set (Sym2 V))
  letI : Nonempty V := ⟨u⟩
  apply H.le_minDegree_of_forall_le_degree 3
  intro x
  by_cases hxu : x = u
  · subst x
    have hmem : v ∈ G.neighborFinset u := by
      simpa [SimpleGraph.neighborFinset_eq_filter] using huv
    rw [← SimpleGraph.card_neighborFinset_eq_degree H u,
      neighborFinset_deleteEdges_singleton_eq_erase G huv,
      Finset.card_erase_of_mem hmem,
      SimpleGraph.card_neighborFinset_eq_degree]
    omega
  by_cases hxv : x = v
  · subst x
    have hmem : u ∈ G.neighborFinset v := by
      simpa [SimpleGraph.neighborFinset_eq_filter] using huv.symm
    rw [← SimpleGraph.card_neighborFinset_eq_degree H v,
      neighborFinset_deleteEdges_singleton_eq_erase_right G huv,
      Finset.card_erase_of_mem hmem,
      SimpleGraph.card_neighborFinset_eq_degree]
    omega
  · rw [← SimpleGraph.card_neighborFinset_eq_degree H x,
      neighborFinset_deleteEdges_singleton_eq_self_of_ne G huv hxu hxv,
      SimpleGraph.card_neighborFinset_eq_degree G x]
    exact le_trans hmin (G.minDegree_le_degree x)

theorem EdgeMinimalCounterexample.high_degree_vertices_independent
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : EdgeMinimalCounterexample G)
    {u v : V} (hu : 4 ≤ G.degree u) (hv : 4 ≤ G.degree v) :
    ¬G.Adj u v := by
  classical
  intro huv
  let H := G.deleteEdges ({s(u, v)} : Set (Sym2 V))
  have hHmin : H.minDegree ≥ 3 := by
    exact minDegree_deleteEdges_singleton_ge_three G
      minimalCounterexample.vertexMinimal.isCounterexample.1 huv hu hv
  have hHno : ¬HasPowerOfTwoCycle H := by
    intro hcycle
    rcases hcycle with ⟨k, w, c, hk, hc, hlen⟩
    let f : H →g G :=
      SimpleGraph.Hom.ofLE (SimpleGraph.deleteEdges_le _)
    have hc' : (c.map f).IsCycle := hc.map (by
      intro x y hxy
      exact hxy)
    have hlen' : (c.map f).length = 2 ^ k := by
      rw [SimpleGraph.Walk.length_map]
      exact hlen
    exact minimalCounterexample.vertexMinimal.isCounterexample.2
      ⟨k, w, c.map f, hk, hc', hlen'⟩
  have hHcounter : IsCounterexample H := ⟨hHmin, hHno⟩
  have hle : H ≤ G := SimpleGraph.deleteEdges_le _
  have heq : H = G := minimalCounterexample.edgeMinimal H hHcounter hle
  have hnot : ¬H.Adj u v := by
    simp [H]
  exact hnot (by simpa [heq] using huv)

theorem EdgeMinimalCounterexample.neighbor_degree_eq_three_of_degree_ge_four
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : EdgeMinimalCounterexample G)
    {u v : V} (hu : 4 ≤ G.degree u) (huv : G.Adj u v) :
    G.degree v = 3 := by
  have hmin := degree_ge_three_of_minDegree_ge_three G
    minimalCounterexample.vertexMinimal.isCounterexample.1 v
  by_contra hv
  have hv4 : 4 ≤ G.degree v := by omega
  exact (minimalCounterexample.high_degree_vertices_independent hu hv4) huv

theorem ShortestCycleCertificate.exists_external_degree_three_neighbor_of_high_degree
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (certificate : ShortestCycleCertificate G)
    (minimalCounterexample : EdgeMinimalCounterexample G)
    (hmin : G.minDegree ≥ 3)
    {v : V} (hv : v ∈ certificate.cycle.support)
    (hvhigh : 4 ≤ G.degree v) :
    ∃ w, G.Adj v w ∧ w ∉ certificate.cycle.support ∧
      G.degree w = 3 := by
  obtain ⟨w, hvw, hw⟩ :=
    certificate.exists_external_neighbor_of_minDegree_ge_three hmin hv
  have hwdeg :=
    minimalCounterexample.neighbor_degree_eq_three_of_degree_ge_four
      hvhigh hvw
  exact ⟨w, hvw, hw, hwdeg⟩

theorem ShortestCycleCertificate.exists_degree_three_bridge_or_same_return
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (certificate : ShortestCycleCertificate G)
    (minimalCounterexample : EdgeMinimalCounterexample G)
    (hconn : G.Connected)
    (hmin : G.minDegree ≥ 3)
    {v : V} (hv : v ∈ certificate.cycle.support)
    (hvhigh : 4 ≤ G.degree v) :
    ∃ w, G.Adj v w ∧ w ∉ certificate.cycle.support ∧
      G.degree w = 3 ∧
      ((∃ bridge : CycleBridgePath G certificate.cycle,
          bridge.left = v) ∨
       ∃ (p : G.Walk w v) (i : ℕ),
          p.IsPath ∧ 0 < i ∧ i ≤ p.length ∧
            p.getVert i = v ∧
            (p.take i).support.dropLast.Disjoint certificate.cycle.support) := by
  obtain ⟨w, hvw, hw, hwdeg⟩ :=
    certificate.exists_external_degree_three_neighbor_of_high_degree
      minimalCounterexample hmin hv hvhigh
  obtain hbridge | hreturn :=
    CycleBridgePath.exists_of_connected_external_neighbor
      certificate.isCycle hconn hv hw hvw
  · exact ⟨w, hvw, hw, hwdeg, Or.inl hbridge⟩
  · exact ⟨w, hvw, hw, hwdeg, Or.inr hreturn⟩

theorem ShortestCycleCertificate.exists_degree_three_bridge_or_excursion
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (certificate : ShortestCycleCertificate G)
    (minimalCounterexample : EdgeMinimalCounterexample G)
    (hconn : G.Connected)
    (hmin : G.minDegree ≥ 3)
    {v : V} (hv : v ∈ certificate.cycle.support)
    (hvhigh : 4 ≤ G.degree v) :
    ∃ w, G.Adj v w ∧ w ∉ certificate.cycle.support ∧
      G.degree w = 3 ∧
      ((∃ bridge : CycleBridgePath G certificate.cycle,
          bridge.left = v) ∨
       (∃ (p : G.Walk w v) (i : ℕ),
          p.IsPath ∧ 0 < i ∧ i ≤ p.length ∧
            p.getVert i = v ∧
            (p.take i).support.dropLast.Disjoint certificate.cycle.support ∧
            ((∃ c : G.Walk v v, c.IsCycle ∧ c.length = i + 1) ∨
              i = 1))) := by
  obtain ⟨w, hvw, hw, hwdeg, hcase⟩ :=
    certificate.exists_degree_three_bridge_or_same_return
      minimalCounterexample hconn hmin hv hvhigh
  rcases hcase with hbridge | ⟨p, i, hp, hi_pos, hi_le, hreturn, hinterior⟩
  · exact ⟨w, hvw, hw, hwdeg, Or.inl hbridge⟩
  · obtain hcycle | hi_one :=
      SimpleGraph.Walk.same_attachment_excursion hvw p hp
        hi_pos hi_le hreturn
    · exact ⟨w, hvw, hw, hwdeg, Or.inr
        ⟨p, i, hp, hi_pos, hi_le, hreturn, hinterior, Or.inl hcycle⟩⟩
    · exact ⟨w, hvw, hw, hwdeg, Or.inr
        ⟨p, i, hp, hi_pos, hi_le, hreturn, hinterior, Or.inr hi_one⟩⟩

/- A degree-three attachment vertex has two distinct neighbors besides the
   already chosen attachment edge. -/
theorem exists_two_other_neighbors_of_degree_three
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {v w : V} (hvw : G.Adj v w) (hw : G.degree w = 3) :
    ∃ x y, x ≠ y ∧ G.Adj w x ∧ G.Adj w y ∧ x ≠ v ∧ y ≠ v := by
  classical
  have hvw' : G.Adj w v := hvw.symm
  have hv_mem : v ∈ G.neighborFinset w := by
    simpa [SimpleGraph.neighborFinset_eq_filter] using hvw'
  let N := (G.neighborFinset w).erase v
  have hNcard : N.card = 2 := by
    dsimp [N]
    rw [Finset.card_erase_of_mem hv_mem,
      SimpleGraph.card_neighborFinset_eq_degree, hw]
  have hNone : 1 < N.card := by omega
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hNone
  have hx' : x ≠ v ∧ x ∈ G.neighborFinset w :=
    Finset.mem_erase.mp hx
  have hy' : y ≠ v ∧ y ∈ G.neighborFinset w :=
    Finset.mem_erase.mp hy
  have hxadj : G.Adj w x := by
    simpa [SimpleGraph.neighborFinset_eq_filter] using hx'.2
  have hyadj : G.Adj w y := by
    simpa [SimpleGraph.neighborFinset_eq_filter] using hy'.2
  exact ⟨x, y, hxy, hxadj, hyadj, hx'.1, hy'.1⟩

theorem EdgeMinimalCounterexample.high_degree_neighborFinset_card_le_two_of_degree_eq_three
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : EdgeMinimalCounterexample G)
    {v : V} (hv : G.degree v = 3) :
    ((Finset.univ.filter (fun w => 4 ≤ G.degree w)).filter (G.Adj v)).card ≤ 2 := by
  classical
  let H : Finset V := Finset.univ.filter (fun w => 4 ≤ G.degree w)
  let N : Finset V := H.filter (G.Adj v)
  obtain ⟨u, huv, hdu⟩ :=
    minimalCounterexample.vertexMinimal.exists_adjacent_degree_eq_three v
  have hu_mem : u ∈ G.neighborFinset v := by
    simpa [SimpleGraph.neighborFinset_eq_filter] using huv
  have hsub : N ⊆ (G.neighborFinset v).erase u := by
    intro x hx
    have hxN : x ∈ H ∧ G.Adj v x := by
      simpa [N] using hx
    have hxhigh : 4 ≤ G.degree x := by
      simpa [H] using hxN.1
    refine Finset.mem_erase.mpr ⟨?_, ?_⟩
    · intro hxu
      subst x
      omega
    · simpa [SimpleGraph.neighborFinset_eq_filter] using hxN.2
  have hcard : N.card ≤ ((G.neighborFinset v).erase u).card :=
    Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hu_mem,
    SimpleGraph.card_neighborFinset_eq_degree, hv] at hcard
  simpa [N] using hcard

/- A two-edge route through an external vertex is an explicit bridge when its
   two endpoints are distinct cycle vertices. -/
def CycleBridgePath.of_two_edge_ear
    {V : Type u} {G : SimpleGraph V} [DecidableEq V]
    {s v w x : V} {cycle : G.Walk s s}
    (hcycle : cycle.IsCycle)
    (hv : v ∈ cycle.support) (hx : x ∈ cycle.support)
    (hvw : G.Adj v w) (hw : w ∉ cycle.support)
    (hwx : G.Adj w x) (hneq : v ≠ x) :
    CycleBridgePath G cycle := by
  let p : G.Walk v x :=
    SimpleGraph.Walk.cons hvw
      (SimpleGraph.Walk.cons hwx SimpleGraph.Walk.nil)
  have hp : p.IsPath := by
    apply (SimpleGraph.Walk.cons_isPath_iff hvw _).2
    constructor
    · simpa [hwx.ne]
    · simpa [p, hneq, hvw.ne]
  refine
    { left := v
      right := x
      left_mem_cycle := hv
      right_mem_cycle := hx
      distinct_attachments := hneq
      path := p
      isPath := hp
      interior_disjoint_cycle := ?_ }
  simpa [p] using hw

/- A two-edge ear attached to a shortest cycle already forces a 4-cycle.
   The two complementary cycle arcs sum to the shortest-cycle length, while
   shortestness bounds each arc by the ear length. -/
theorem ShortestCycleCertificate.hasPowerOfTwoCycle_of_two_edge_ear
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (certificate : ShortestCycleCertificate G)
    (bridge : CycleBridgePath G certificate.cycle)
    (hpath : bridge.path.length = 2) :
    HasPowerOfTwoCycle G := by
  obtain ⟨p, q, hdecomp⟩ :=
    bridge.exists_complementary_arcs certificate.isCycle
  have hpvalid :
      1 < bridge.path.length ∨
        1 < (p : G.Walk bridge.left bridge.right).length :=
    Or.inl (by omega)
  have hqvalid :
      1 < bridge.path.length ∨
        1 < (q : G.Walk bridge.right bridge.left).length :=
    Or.inl (by omega)
  have hbounds :=
    certificate.complementary_arc_le_bridge_length
      bridge hdecomp hpvalid hqvalid
  have hsum := bridge.complementary_arcs_length_add hdecomp
  have hp_pos : 0 < (p : G.Walk bridge.left bridge.right).length := by
    apply Nat.pos_of_ne_zero
    intro hp_zero
    have hp_nil :=
      SimpleGraph.Walk.length_eq_zero_iff.mp hp_zero
    exact bridge.distinct_attachments
      ((p.property.nil_iff_eq).mp hp_nil)
  have hq_pos : 0 < (q : G.Walk bridge.right bridge.left).length := by
    apply Nat.pos_of_ne_zero
    intro hq_zero
    have hq_nil :=
      SimpleGraph.Walk.length_eq_zero_iff.mp hq_zero
    exact bridge.distinct_attachments.symm
      ((q.property.nil_iff_eq).mp hq_nil)
  have hcycle_ge : 3 ≤ certificate.cycle.length :=
    certificate.isCycle.three_le_length
  have hor :
      (p : G.Walk bridge.left bridge.right).length = 2 ∨
        (q : G.Walk bridge.right bridge.left).length = 2 := by
    omega
  rcases hor with hp_two | hq_two
  · obtain ⟨c, hc, hlength⟩ :=
      bridge.cycle_of_extracted_arc hdecomp hpvalid
    refine hasPowerOfTwoCycle_of_witness (k := 2) c (by omega) hc ?_
    omega
  · have hq_sub_cycle :
        (q : G.Walk bridge.right bridge.left).support ⊆
          certificate.cycle.support := by
      intro z hz
      have hzappend : z ∈
          ((p : G.Walk bridge.left bridge.right).append
            (q : G.Walk bridge.right bridge.left)).support := by
        simp [hz]
      rw [hdecomp] at hzappend
      exact (SimpleGraph.Walk.mem_support_rotate_iff certificate.cycle
        bridge.left bridge.left_mem_cycle).mp hzappend
    have hdisjoint :=
      bridge.reverse.tails_disjoint_of_arc_support_subset
        q.property hq_sub_cycle
    have hqvalid' :
        1 < bridge.reverse.path.length ∨
          (q : G.Walk bridge.right bridge.left).length > 1 := by
      simpa [CycleBridgePath.reverse, SimpleGraph.Walk.length_reverse] using hqvalid
    obtain ⟨c, hc, hlength⟩ :=
      bridge.reverse.cycle_of_arc q.property hdisjoint hqvalid'
    have hlength' : c.length =
        bridge.path.length +
          (q : G.Walk bridge.right bridge.left).length := by
      simpa [CycleBridgePath.reverse, SimpleGraph.Walk.length_reverse] using
        hlength
    refine hasPowerOfTwoCycle_of_witness (k := 2) c (by omega) hc ?_
    omega

/- A degree-three attachment either gives a direct ear back to the cycle or
   exposes two distinct continuations that are both still external. -/
theorem exists_direct_ear_or_two_external_branches_of_degree_three
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {s v w : V} {cycle : G.Walk s s}
    (hcycle : cycle.IsCycle)
    (hv : v ∈ cycle.support) (hw : w ∉ cycle.support)
    (hvw : G.Adj v w) (hwdeg : G.degree w = 3) :
    (∃ x, x ∈ cycle.support ∧ x ≠ v ∧ G.Adj w x ∧
      ∃ bridge : CycleBridgePath G cycle,
        bridge.left = v ∧ bridge.right = x) ∨
    (∃ x y, x ≠ y ∧ G.Adj w x ∧ G.Adj w y ∧
      x ≠ v ∧ y ≠ v ∧ x ∉ cycle.support ∧ y ∉ cycle.support) := by
  obtain ⟨x, y, hxy, hwx, hwy, hxv, hyv⟩ :=
    exists_two_other_neighbors_of_degree_three hvw hwdeg
  by_cases hx : x ∈ cycle.support
  · left
    refine ⟨x, hx, hxv, hwx, ?_⟩
    let bridge := CycleBridgePath.of_two_edge_ear hcycle hv hx
      hvw hw hwx (Ne.symm hxv)
    exact ⟨bridge, rfl, rfl⟩
  · by_cases hy : y ∈ cycle.support
    · left
      refine ⟨y, hy, hyv, hwy, ?_⟩
      let bridge := CycleBridgePath.of_two_edge_ear hcycle hv hy
        hvw hw hwy (Ne.symm hyv)
      exact ⟨bridge, rfl, rfl⟩
    · right
      exact ⟨x, y, hxy, hwx, hwy, hxv, hyv, hx, hy⟩

theorem EdgeMinimalCounterexample.high_degree_count_mul_four_le_degree_three_count_mul_two
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : EdgeMinimalCounterexample G) :
    (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card * 4 ≤
      (Finset.univ.filter (fun v => G.degree v = 3)).card * 2 := by
  classical
  let H : Finset V := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  let L : Finset V := Finset.univ.filter (fun v => G.degree v = 3)
  have hdouble : H.card * 4 ≤ L.card * 2 := by
    apply Finset.card_mul_le_card_mul (fun u v => G.Adj u v)
    · intro u hu
      have hu4 : 4 ≤ G.degree u := by
        simpa [H] using hu
      have hcard :
          (L.bipartiteAbove (fun u v => G.Adj u v) u).card =
            G.degree u := by
        rw [← SimpleGraph.card_neighborFinset_eq_degree]
        congr 1
        ext v
        constructor
        · intro hv
          have hv' : v ∈ L ∧ G.Adj u v := by
            simpa [Finset.bipartiteAbove] using hv
          have huv : G.Adj u v := hv'.2
          simpa [SimpleGraph.neighborFinset_eq_filter] using huv
        · intro hv
          have huv : G.Adj u v := by
            simpa [SimpleGraph.neighborFinset_eq_filter] using hv
          have hv3 :
              G.degree v = 3 :=
            minimalCounterexample.neighbor_degree_eq_three_of_degree_ge_four
              hu4 huv
          simpa [Finset.bipartiteAbove] using
            (show v ∈ L ∧ G.Adj u v from ⟨by
              simpa [L] using hv3, huv⟩)
      rw [hcard]
      exact hu4
    · intro v hv
      have hv3 : G.degree v = 3 := by
        simpa [L] using hv
      have hbound :=
        minimalCounterexample.high_degree_neighborFinset_card_le_two_of_degree_eq_three
          hv3
      have hcard :
          (H.bipartiteBelow (fun u v => G.Adj u v) v).card =
            ((Finset.univ.filter (fun u => 4 ≤ G.degree u)).filter
              (G.Adj v)).card := by
        congr 1
        ext u
        simp only [Finset.bipartiteBelow, Finset.mem_filter]
        constructor
        · rintro ⟨hu, huv⟩
          exact ⟨by simpa [H] using hu, huv.symm⟩
        · rintro ⟨hu, huv⟩
          exact ⟨by simpa [H] using hu, huv.symm⟩
      rw [hcard]
      exact hbound
  simpa [H, L] using hdouble

theorem EdgeMinimalCounterexample.high_degree_count_mul_two_le_degree_three_count
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : EdgeMinimalCounterexample G) :
    (Finset.univ.filter (fun v => 4 ≤ G.degree v)).card * 2 ≤
      (Finset.univ.filter (fun v => G.degree v = 3)).card := by
  have hinc :=
    minimalCounterexample.high_degree_count_mul_four_le_degree_three_count_mul_two
  omega

theorem EdgeMinimalCounterexample.exists_degree_eq_three
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : EdgeMinimalCounterexample G) :
    (Finset.univ.filter (fun v => G.degree v = 3)).Nonempty := by
  classical
  let H : Finset V := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  let L : Finset V := Finset.univ.filter (fun v => G.degree v = 3)
  change L.Nonempty
  have hmin : G.minDegree ≥ 3 :=
    minimalCounterexample.vertexMinimal.isCounterexample.1
  have hV : Nonempty V := by
    by_contra hV
    letI : IsEmpty V := ⟨fun v => hV ⟨v⟩⟩
    have hzero : (3 : ℕ) ≤ 0 := by
      simpa using hmin
    omega
  by_contra hL
  have hLempty : L = ∅ :=
    Finset.not_nonempty_iff_eq_empty.mp hL
  have hLcard : L.card = 0 :=
    Finset.card_eq_zero.mpr hLempty
  have hinc :
      H.card * 4 ≤ L.card * 2 := by
    simpa [H, L] using
      minimalCounterexample.high_degree_count_mul_four_le_degree_three_count_mul_two
  have hHcard : H.card = 0 := by
    have hbound : H.card * 4 ≤ 0 := by
      simpa [hLcard] using hinc
    omega
  have hHempty : H = ∅ := Finset.card_eq_zero.mp hHcard
  obtain ⟨v⟩ := hV
  have hvdeg : G.degree v ≥ 3 :=
    degree_ge_three_of_minDegree_ge_three G hmin v
  have hvnot3 : G.degree v ≠ 3 := by
    intro hv3
    apply hL
    exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ v, hv3⟩⟩
  have hvhigh : 4 ≤ G.degree v := by
    omega
  have hvH : v ∈ H := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ v, hvhigh⟩
  rw [hHempty] at hvH
  simpa using hvH

/-- Deleting an outside component forces a deficient boundary vertex.

The separation hypothesis says that vertices outside both `U` and `K` have
no neighbors in `K`. Thus `K` behaves as one component of the complement of
`U`, without requiring a formal connected-component API.-/
theorem exists_deficient_boundary_vertex
    {V : Type u} (G : SimpleGraph V) [Fintype V]
    [DecidableEq V] [DecidableRel G.Adj]
    (hmin : ∀ v, 3 ≤ (Finset.univ.filter (G.Adj v)).card)
    (hcritical : IsSubgraphCritical G)
    {U K : Finset V}
    (hU_nonempty : U.Nonempty)
    (hK_nonempty : K.Nonempty)
    (hdisjoint : Disjoint U K)
    (hU_degree : ∀ v, v ∈ U → 2 ≤ internalDegree G U v)
    (hseparated :
      ∀ x, x ∉ U → x ∉ K → ∀ y, y ∈ K → ¬G.Adj x y) :
    ∃ v, v ∈ U ∧ 2 ≤ internalDegree G U v ∧
      internalDegree G (Finset.univ \ K) v ≤ 2 ∧
      ∃ w, w ∈ K ∧ G.Adj v w := by
  classical
  let S := Finset.univ \ K
  have hS_nonempty : S.Nonempty := by
    obtain ⟨u, hu⟩ := hU_nonempty
    have huK : u ∉ K := by
      intro huK
      exact (Finset.disjoint_left.1 hdisjoint) hu huK
    exact ⟨u, Finset.mem_sdiff.mpr ⟨Finset.mem_univ u, huK⟩⟩
  have hS_proper : S ≠ Finset.univ := by
    intro hS
    obtain ⟨k, hk⟩ := hK_nonempty
    have hkS : k ∈ S := hS ▸ Finset.mem_univ k
    exact (Finset.mem_sdiff.mp hkS).2 hk
  obtain ⟨v, hvS, hvlow⟩ := hcritical S hS_nonempty hS_proper
  have hvU : v ∈ U := by
    by_contra hvU
    have hvK : v ∉ K := by
      intro hvK
      exact (Finset.mem_sdiff.mp hvS).2 hvK
    have hsubset :
        (Finset.univ.filter (G.Adj v)) ⊆ (S.filter (G.Adj v)) := by
      intro w hw
      have hwAdj : G.Adj v w := (Finset.mem_filter.mp hw).2
      have hwS : w ∈ S := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ w, ?_⟩
        intro hwK
        exact (hseparated v hvU hvK w hwK) hwAdj
      exact Finset.mem_filter.mpr ⟨hwS, hwAdj⟩
    have hthree :
        3 ≤ (S.filter (G.Adj v)).card :=
      le_trans (hmin v) (Finset.card_le_card hsubset)
    have hbad : 3 ≤ 2 := le_trans hthree hvlow
    omega
  have hvK_neighbor : ∃ w, w ∈ K ∧ G.Adj v w := by
    by_contra hnone
    have hno : ∀ w, w ∈ K → ¬G.Adj v w := by
      intro w hwK hwAdj
      exact hnone ⟨w, hwK, hwAdj⟩
    have hsubset :
        (Finset.univ.filter (G.Adj v)) ⊆ (S.filter (G.Adj v)) := by
      intro w hw
      have hwAdj : G.Adj v w := (Finset.mem_filter.mp hw).2
      have hwS : w ∈ S := by
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_univ w, ?_⟩
        intro hwK
        exact (hno w hwK) hwAdj
      exact Finset.mem_filter.mpr ⟨hwS, hwAdj⟩
    have hthree :
        3 ≤ (S.filter (G.Adj v)).card :=
      le_trans (hmin v) (Finset.card_le_card hsubset)
    have hbad : 3 ≤ 2 := le_trans hthree hvlow
    omega
  exact ⟨v, hvU, hU_degree v hvU, hvlow, hvK_neighbor⟩

/- Expose the deficient-boundary certificate directly for a minimal
   counterexample, converting its minimum-degree statement to the finset
   form used by the general lemma. -/
theorem MinimalCounterexample.exists_deficient_boundary_vertex
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : MinimalCounterexample G)
    {U K : Finset V}
    (hU_nonempty : U.Nonempty)
    (hK_nonempty : K.Nonempty)
    (hdisjoint : Disjoint U K)
    (hU_degree : ∀ v, v ∈ U → 2 ≤ internalDegree G U v)
    (hseparated :
      ∀ x, x ∉ U → x ∉ K → ∀ y, y ∈ K → ¬G.Adj x y) :
    ∃ v, v ∈ U ∧ 2 ≤ internalDegree G U v ∧
      internalDegree G (Finset.univ \ K) v ≤ 2 ∧
      ∃ w, w ∈ K ∧ G.Adj v w := by
  have hmin : ∀ v, 3 ≤ (Finset.univ.filter (G.Adj v)).card := by
    intro v
    have hv := degree_ge_three_of_minDegree_ge_three G
      minimalCounterexample.isCounterexample.1 v
    have hv' : 3 ≤ (G.neighborFinset v).card := by
      simpa only [SimpleGraph.card_neighborFinset_eq_degree] using hv
    simpa [SimpleGraph.neighborFinset_def] using hv'
  exact Erdos64.exists_deficient_boundary_vertex G hmin
    minimalCounterexample.isSubgraphCritical hU_nonempty hK_nonempty
    hdisjoint hU_degree hseparated

/- An edge-minimal counterexample is predominantly cubic: at least two thirds
   of its vertices have degree exactly three. -/
theorem EdgeMinimalCounterexample.degree_three_count_ge_two_thirds
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : EdgeMinimalCounterexample G) :
    2 * Fintype.card V ≤
      3 * (Finset.univ.filter (fun v => G.degree v = 3)).card := by
  classical
  let H : Finset V := Finset.univ.filter (fun v => 4 ≤ G.degree v)
  let L : Finset V := Finset.univ.filter (fun v => G.degree v = 3)
  have hmin : G.minDegree ≥ 3 :=
    minimalCounterexample.vertexMinimal.isCounterexample.1
  have hpartition : L ∪ H = Finset.univ := by
    ext v
    simp only [L, H, Finset.mem_union, Finset.mem_filter, Finset.mem_univ,
      true_and]
    change (G.degree v = 3 ∨ 4 ≤ G.degree v) ↔ True
    have hv : 3 ≤ G.degree v :=
      degree_ge_three_of_minDegree_ge_three G hmin v
    constructor
    · intro _
      trivial
    · intro _
      by_cases hv3 : G.degree v = 3
      · exact Or.inl hv3
      · exact Or.inr (by omega)
  have hdisjoint : Disjoint L H := by
    refine Finset.disjoint_left.2 ?_
    intro v hvL hvH
    have hv3 : G.degree v = 3 := by
      simpa [L] using hvL
    have hv4 : 4 ≤ G.degree v := by
      simpa [H] using hvH
    omega
  have hcard :
      Fintype.card V = L.card + H.card := by
    calc
      Fintype.card V = (Finset.univ : Finset V).card := by
        simp
      _ = (L ∪ H).card := by rw [hpartition]
      _ = L.card + H.card := Finset.card_union_of_disjoint hdisjoint
  have hcount : 2 * H.card ≤ L.card := by
    simpa [Nat.mul_comm, H, L] using
      minimalCounterexample.high_degree_count_mul_two_le_degree_three_count
  rw [hcard]
  change 2 * (L.card + H.card) ≤ 3 * L.card
  omega

/- The predominantly-cubic invariant can be attached to a refinement of any
   vertex-minimal counterexample, rather than assumed for the original graph. -/
theorem MinimalCounterexample.exists_edgeMinimal_predominantly_cubic
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (minimalCounterexample : MinimalCounterexample G) :
    ∃ (H : SimpleGraph V) (_ : DecidableRel H.Adj),
      EdgeMinimalCounterexample H ∧
        2 * Fintype.card V ≤
          3 * (Finset.univ.filter (fun v => H.degree v = 3)).card := by
  obtain ⟨H, hH, hedge⟩ :=
    minimalCounterexample.exists_edgeMinimalCounterexample
  letI : DecidableRel H.Adj := hH
  exact ⟨H, hH, hedge,
    hedge.degree_three_count_ge_two_thirds⟩

end Erdos64
