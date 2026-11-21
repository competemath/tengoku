import Tengoku.Erdos64.Erdos64.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u
variable {V : Type u} (G : SimpleGraph V) (a b : V)

/-- Internal vertices and the terminal-identification vertex type.-/
abbrev Internal (a b : V) := {v : V // v ≠ a ∧ v ≠ b}
abbrev QuotientVertex (a b : V) := Option (Internal a b)

/-- Both terminals map to none; every other vertex maps to its internal value.-/
def quotientVertexMap [DecidableEq V] : V → QuotientVertex a b :=
  fun v => if h : v = a ∨ v = b then none
    else some ⟨v, fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩

/--
@isnad1 id=eq.0h3v.s4.88f214c0d349 from=translated src=- shape=e25799eb vocab=48ff5883
-/
@[simp] theorem quotientVertexMap_a [DecidableEq V] :
    quotientVertexMap a b a = none := by simp [quotientVertexMap]

/--
@isnad1 id=eq.0h3v.s4.de3d1c65eb98 from=translated src=- shape=8cc66701 vocab=48ff5883
-/
@[simp] theorem quotientVertexMap_b [DecidableEq V] :
    quotientVertexMap a b b = none := by simp [quotientVertexMap]

/--
@isnad1 id=eq.0h4v.s5.8f7cf7dd483d from=translated src=- shape=ec854486 vocab=eb92d86b
-/
@[simp] theorem quotientVertexMap_internal [DecidableEq V] (v : Internal a b) :
    quotientVertexMap a b v.1 = some v := by
  simp [quotientVertexMap, v.2.1, v.2.2]

/-- Simple quotient: loops are discarded and parallel root edges are merged.-/
def terminalQuotientGraph : SimpleGraph (QuotientVertex a b) where
  Adj x y := match x, y with
    | none, none => False
    | none, some y => G.Adj a y.1 ∨ G.Adj b y.1
    | some x, none => G.Adj x.1 a ∨ G.Adj x.1 b
    | some x, some y => G.Adj x.1 y.1
  symm := ⟨fun x y h => by
    cases x <;> cases y <;> simp_all [G.adj_comm]⟩
  loopless := ⟨fun x h => by
    cases x with
    | none => exact h
    | some x => exact G.irrefl h⟩

noncomputable instance quotient_decidableRel [DecidableRel G.Adj] :
    DecidableRel (terminalQuotientGraph G a b).Adj := by
  classical exact fun x y => Classical.propDecidable _

/--
@isnad1 id=iff.0h5v.s6.8bea22cef579 from=translated src=- shape=72cdcc9c vocab=1fc5624a
-/
@[simp] theorem quotient_adj_root_internal (v : Internal a b) :
    (terminalQuotientGraph G a b).Adj none (some v) ↔
      G.Adj a v.1 ∨ G.Adj b v.1 := Iff.rfl

/--
@isnad1 id=iff.0h6v.s6.1ac9ed080740 from=translated src=- shape=228a1367 vocab=7b377674
-/
@[simp] theorem quotient_adj_internal_internal (v w : Internal a b) :
    (terminalQuotientGraph G a b).Adj (some v) (some w) ↔
      G.Adj v.1 w.1 := Iff.rfl

/-- The induced internal graph embeds into the quotient.-/
def internalEmbedding :
    (G.induce {v : V | v ≠ a ∧ v ≠ b}) ↪g terminalQuotientGraph G a b where
  toFun v := some v
  inj' := by
    intro v w h
    change some (v : Internal a b) = some w at h
    exact Option.some.inj h
  map_rel_iff' := by intro v w; rfl

/--
@isnad1 id=eq.0h5v.s7.c1904bf7764b from=translated src=- shape=0a705d4c vocab=0ae709cf
-/
@[simp] theorem internalEmbedding_apply (v : Internal a b) :
    internalEmbedding G a b v = some v := rfl

/--
@isnad1 id=eq.0h3v.s6.aaceb953deba from=translated src=- shape=7779e478 vocab=e8475a9f
-/
theorem quotient_card_internal [DecidableEq V] [Fintype V] :
    Fintype.card (QuotientVertex a b) = Fintype.card (Internal a b) + 1 := by
  simp [QuotientVertex]

/-- Exact description of the quotient root's neighbors, including the
deduplication when a vertex is adjacent to both terminals.-/
def rootNeighborEquiv :
    (terminalQuotientGraph G a b).neighborSet none ≃
      {v : V // v ≠ a ∧ v ≠ b ∧ (G.Adj a v ∨ G.Adj b v)} where
  toFun
    | ⟨none, h⟩ => False.elim h
    | ⟨some v, h⟩ => ⟨v.1, v.2.1, v.2.2, h⟩
  invFun x := ⟨some ⟨x.1, x.2.1, x.2.2.1⟩, x.2.2.2⟩
  left_inv := by
    rintro ⟨(_ | v), h⟩
    · exact False.elim h
    · rfl
  right_inv := by intro x; rfl

/--
@isnad1 id=eq.0h4v.s8.76c0a6e2e761 from=translated src=- shape=e867d690 vocab=65aeb2d7
-/
theorem quotient_root_degree [DecidableEq V] [Fintype V] [DecidableRel G.Adj] :
    (terminalQuotientGraph G a b).degree none =
      Fintype.card {v : V // v ≠ a ∧ v ≠ b ∧ (G.Adj a v ∨ G.Adj b v)} := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact Fintype.card_congr (rootNeighborEquiv G a b)

/-- A simple internal path between distinct root neighbors gives a simple
root cycle. The root-neighbor disjunction permits either terminal at each end.
@isnad1 id=ex.5h7v.s7.675ec9a243cf from=translated src=- shape=7a6a1c6f vocab=fd77c325
-/
theorem root_cycle_of_internal_path
    (_hnadj : ¬ G.Adj a b)
    {x y : Internal a b}
    (p : (G.induce {v : V | v ≠ a ∧ v ≠ b}).Walk x y)
    (hp : p.IsPath) (hxy : x ≠ y)
    (hx : G.Adj a x.1 ∨ G.Adj b x.1)
    (hy : G.Adj a y.1 ∨ G.Adj b y.1) :
    ∃ c : (terminalQuotientGraph G a b).Walk none none, c.IsCycle := by
  let e := internalEmbedding G a b
  have hroot_x : (terminalQuotientGraph G a b).Adj none (some x) := hx
  have hroot_y : (terminalQuotientGraph G a b).Adj none (some y) := hy
  have hnone : none ∉ (p.map e.toHom).support := by
    simp [SimpleGraph.Walk.support_map, e, internalEmbedding]
  let r : (terminalQuotientGraph G a b).Walk none (some y) :=
    SimpleGraph.Walk.cons hroot_x (p.map e.toHom)
  let s : (terminalQuotientGraph G a b).Walk (some y) none :=
    hroot_y.symm.toWalk
  have hr : r.IsPath := (hp.map e.injective).cons hnone
  have hs : s.IsPath := hroot_y.symm.isPath_toWalk
  have hdis : r.support.tail.Disjoint s.support.tail := by
    rw [List.disjoint_left]
    intro z hz_r hz_s
    have hz : z = none := by simpa [s] using hz_s
    subst z
    change none ∈ (p.map e.toHom).support at hz_r
    exact hnone hz_r
  have hpos : 0 < p.length := by
    cases p with
    | nil => exact False.elim (hxy rfl)
    | cons h p => simp
  have hlong : 1 < r.length := by
    change 1 < (p.map e.toHom).length + 1
    rw [SimpleGraph.Walk.length_map]
    omega
  exact ⟨r.append s, hr.isCycle_append hs hdis (Or.inl hlong)⟩

/-- The restricted quotient cycle has the expected root-plus-path length.
@isnad1 id=ex.5h7v.s8.5e5508806b22 from=translated src=- shape=7365e187 vocab=ba6c54e0
-/
theorem root_cycle_of_internal_path_length
    (_hnadj : ¬ G.Adj a b)
    {x y : Internal a b}
    (p : (G.induce {v : V | v ≠ a ∧ v ≠ b}).Walk x y)
    (hp : p.IsPath) (hxy : x ≠ y)
    (hx : G.Adj a x.1 ∨ G.Adj b x.1)
    (hy : G.Adj a y.1 ∨ G.Adj b y.1) :
    ∃ c : (terminalQuotientGraph G a b).Walk none none,
      c.IsCycle ∧ c.length = p.length + 2 := by
  let e := internalEmbedding G a b
  have hroot_x : (terminalQuotientGraph G a b).Adj none (some x) := hx
  have hroot_y : (terminalQuotientGraph G a b).Adj none (some y) := hy
  have hnone : none ∉ (p.map e.toHom).support := by
    simp [SimpleGraph.Walk.support_map, e, internalEmbedding]
  let r : (terminalQuotientGraph G a b).Walk none (some y) :=
    SimpleGraph.Walk.cons hroot_x (p.map e.toHom)
  let s : (terminalQuotientGraph G a b).Walk (some y) none :=
    hroot_y.symm.toWalk
  have hr : r.IsPath := (hp.map e.injective).cons hnone
  have hs : s.IsPath := hroot_y.symm.isPath_toWalk
  have hdis : r.support.tail.Disjoint s.support.tail := by
    rw [List.disjoint_left]
    intro z hz_r hz_s
    have hz : z = none := by simpa [s] using hz_s
    subst z
    change none ∈ (p.map e.toHom).support at hz_r
    exact hnone hz_r
  have hpos : 0 < p.length := by
    cases p with
    | nil => exact False.elim (hxy rfl)
    | cons h p => simp
  have hlong : 1 < r.length := by
    change 1 < (p.map e.toHom).length + 1
    rw [SimpleGraph.Walk.length_map]
    omega
  refine ⟨r.append s, hr.isCycle_append hs hdis (Or.inl hlong), ?_⟩
  have hr_length : r.length = p.length + 1 := by
    change (p.map e.toHom).length + 1 = p.length + 1
    rw [SimpleGraph.Walk.length_map]
  rw [SimpleGraph.Walk.length_append]
  rw [hr_length]
  simp only [s, SimpleGraph.Adj.length_toWalk]

/-- In the opposite-attachment case, a root cycle corresponds to an a-b
path through the same internal path.
@isnad1 id=and.6h7v.s7.37272f41b3ce from=translated src=- shape=e55d8f05 vocab=fd77c325
-/
theorem root_cycle_correspondence (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    {x y : Internal a b}
    (p : (G.induce {v : V | v ≠ a ∧ v ≠ b}).Walk x y)
    (hp : p.IsPath) (hxy : x ≠ y)
    (hax : G.Adj a x.1) (hby : G.Adj b y.1) :
    (∃ c : (terminalQuotientGraph G a b).Walk none none, c.IsCycle) ∧
    (∃ q : G.Walk a b, q.IsPath) := by
  refine ⟨root_cycle_of_internal_path G a b hnadj p hp hxy
      (Or.inl hax) (Or.inr hby), ?_⟩
  let i : (G.induce {v : V | v ≠ a ∧ v ≠ b}) ↪g G :=
    SimpleGraph.Embedding.induce _
  let m : G.Walk x.1 y.1 := p.map i.toHom
  have hm : m.IsPath := hp.map i.injective
  have hna : a ∉ m.support := by
    intro ha
    change a ∈ (p.map i.toHom).support at ha
    rw [SimpleGraph.Walk.support_map] at ha
    rw [List.mem_map] at ha
    rcases ha with ⟨z, hz, hza⟩
    change z.1 = a at hza
    exact z.2.1 hza
  have hnb : b ∉ m.support := by
    intro hb
    change b ∈ (p.map i.toHom).support at hb
    rw [SimpleGraph.Walk.support_map] at hb
    rw [List.mem_map] at hb
    rcases hb with ⟨z, hz, hzb⟩
    change z.1 = b at hzb
    exact z.2.2 hzb
  have hma : (SimpleGraph.Walk.cons hax m).IsPath := hm.cons hna
  exact ⟨(SimpleGraph.Walk.cons hax m).concat hby.symm,
    hma.concat (by simp [hnb, hab.symm]) hby.symm⟩

/-- From the supplied internal path and opposite terminal attachments,
construct a quotient cycle and an ambient terminal path of length
`p.length + 2`. This conclusion states the terminal-path length only;
`root_cycle_of_internal_path_length` separately supplies a quotient cycle
with the same length equation.
@isnad1 id=ex.6h7v.s8.68af78eba0e0 from=translated src=- shape=18a44610 vocab=ba6c54e0
-/
theorem root_cycle_correspondence_length (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    {x y : Internal a b}
    (p : (G.induce {v : V | v ≠ a ∧ v ≠ b}).Walk x y)
    (hp : p.IsPath) (hxy : x ≠ y)
    (hax : G.Adj a x.1) (hby : G.Adj b y.1) :
    ∃ c : (terminalQuotientGraph G a b).Walk none none,
      ∃ q : G.Walk a b,
        c.IsCycle ∧ q.IsPath ∧ q.length = p.length + 2 := by
  obtain ⟨c, hc, _hclen⟩ :=
    root_cycle_of_internal_path_length G a b hnadj p hp hxy
      (Or.inl hax) (Or.inr hby)
  let i : (G.induce {v : V | v ≠ a ∧ v ≠ b}) ↪g G :=
    SimpleGraph.Embedding.induce _
  let m : G.Walk x.1 y.1 := p.map i.toHom
  have hm : m.IsPath := hp.map i.injective
  have hna : a ∉ m.support := by
    intro ha
    change a ∈ (p.map i.toHom).support at ha
    rw [SimpleGraph.Walk.support_map] at ha
    rw [List.mem_map] at ha
    rcases ha with ⟨z, _hz, hza⟩
    change z.1 = a at hza
    exact z.2.1 hza
  have hnb : b ∉ m.support := by
    intro hb
    change b ∈ (p.map i.toHom).support at hb
    rw [SimpleGraph.Walk.support_map] at hb
    rw [List.mem_map] at hb
    rcases hb with ⟨z, _hz, hzb⟩
    change z.1 = b at hzb
    exact z.2.2 hzb
  have hma : (SimpleGraph.Walk.cons hax m).IsPath := hm.cons hna
  have hq :
      ((SimpleGraph.Walk.cons hax m).concat hby.symm).IsPath :=
    hma.concat (by simp [hnb, hab.symm]) hby.symm
  refine ⟨c, (SimpleGraph.Walk.cons hax m).concat hby.symm, hc, hq, ?_⟩
  rw [SimpleGraph.Walk.length_concat]
  change (p.map i.toHom).length + 1 + 1 = p.length + 2
  rw [SimpleGraph.Walk.length_map]

/-- Internal simple cycles survive the quotient through the internal embedding.
@isnad1 id=iscycle.1h6v.s8.c2afcd04b97e from=translated src=- shape=32bd9b61 vocab=8ad096c1
-/
theorem quotient_cycle_of_internal_cycle
    {x : Internal a b}
    (c : (G.induce {v : V | v ≠ a ∧ v ≠ b}).Walk x x)
    (hc : c.IsCycle) :
    (c.map (internalEmbedding G a b).toHom).IsCycle := by
  exact hc.map (internalEmbedding G a b).injective

/-- The terminal quotient is in bijection with the original vertex type
    after deleting only `b`: the quotient root represents `a`.-/
private def quotientToNotBEquiv
    {V : Type u} [DecidableEq V] {a b : V} (hab : a ≠ b) :
    QuotientVertex a b ≃ {v : V // v ≠ b} where
  toFun q := match q with
    | none => ⟨a, hab⟩
    | some v => ⟨v.1, v.2.2⟩
  invFun x := if hx : x.1 = a then none else
    some ⟨x.1, hx, x.2⟩
  left_inv := by
    intro q
    cases q with
    | none =>
      change (if h : a = a then none else _) = none
      simp
    | some v =>
      change (if h : v.1 = a then none else some _) = some v
      simp [v.2.1]
  right_inv := by
    rintro ⟨x, hx⟩
    by_cases hxa : x = a
    · dsimp
      simp [hxa]
    · dsimp
      simp [hxa]

/--
@isnad1 id=lt.1h3v.s6.750f62a7b7f7 from=translated src=- shape=09ae83d5 vocab=ea6c9eb5
-/
theorem terminalQuotient_card_lt
    {V : Type u} [Fintype V] [DecidableEq V] {a b : V} (hab : a ≠ b) :
    Fintype.card (QuotientVertex a b) < Fintype.card V := by
  rw [Fintype.card_congr (quotientToNotBEquiv hab)]
  have hb : ¬ (b ≠ b) := by simp
  exact Fintype.card_subtype_lt hb

private theorem terminalQuotient_root_degree_ge_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : G.minDegree ≥ 3) (hnadj : ¬ G.Adj a b) :
    3 ≤ (terminalQuotientGraph G a b).degree none := by
  classical
  let T := {v : V // v ≠ a ∧ v ≠ b ∧ (G.Adj a v ∨ G.Adj b v)}
  let f : G.neighborSet a → T := fun x =>
    ⟨x.1, by
      have hax : G.Adj a x.1 := (G.mem_neighborSet a x.1).mp x.2
      have hxa : x.1 ≠ a := by
        intro h
        have haa : G.Adj a a := by simpa [h] using hax
        exact G.loopless.irrefl a haa
      have hxb : x.1 ≠ b := by
        intro h
        exact hnadj (by simpa [h] using hax)
      exact ⟨hxa, hxb, Or.inl hax⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    change x.1 = y.1
    exact congrArg (fun z : T => z.1) hxy
  have hcard : Fintype.card (G.neighborSet a) ≤ Fintype.card T :=
    Fintype.card_le_of_injective f hf
  rw [SimpleGraph.card_neighborSet_eq_degree] at hcard
  rw [quotient_root_degree]
  exact (degree_ge_three_of_minDegree_ge_three G hmin a).trans hcard

private theorem terminalQuotient_internal_degree_ge_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : G.minDegree ≥ 3)
    (hcommon : ∀ z, z ≠ a → z ≠ b →
      ¬ (G.Adj a z ∧ G.Adj b z))
    {v : Internal a b} :
    3 ≤ (terminalQuotientGraph G a b).degree (some v) := by
  classical
  letI : DecidableRel (terminalQuotientGraph G a b).Adj :=
    quotient_decidableRel G a b
  let f : G.neighborSet v.1 →
      (terminalQuotientGraph G a b).neighborSet (some v) := fun x =>
    if hx : x.1 = a ∨ x.1 = b then
      ⟨none, by
        rcases hx with hxa | hxb
        · exact Or.inl (by simpa [hxa] using
            (G.mem_neighborSet v.1 x.1).mp x.2)
        · exact Or.inr (by simpa [hxb] using
            (G.mem_neighborSet v.1 x.1).mp x.2)⟩
    else
      ⟨some ⟨x.1, by
        exact ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩⟩,
        (G.mem_neighborSet v.1 x.1).mp x.2⟩
  have hf : Function.Injective f := by
    intro x y hxy
    by_cases hx : x.1 = a ∨ x.1 = b
    · by_cases hy : y.1 = a ∨ y.1 = b
      · rcases hx with hxa | hxb <;> rcases hy with hya | hyb
        · apply Subtype.ext
          exact hxa.trans hya.symm
        · exfalso
          have hva : G.Adj v.1 a := by simpa [hxa] using
            (G.mem_neighborSet v.1 x.1).mp x.2
          have hvb : G.Adj v.1 b := by simpa [hyb] using
            (G.mem_neighborSet v.1 y.1).mp y.2
          exact hcommon v.1 v.2.1 v.2.2 ⟨hva.symm, hvb.symm⟩
        · exfalso
          have hvb : G.Adj v.1 b := by simpa [hxb] using
            (G.mem_neighborSet v.1 x.1).mp x.2
          have hva : G.Adj v.1 a := by simpa [hya] using
            (G.mem_neighborSet v.1 y.1).mp y.2
          exact hcommon v.1 v.2.1 v.2.2 ⟨hva.symm, hvb.symm⟩
        · apply Subtype.ext
          exact hxb.trans hyb.symm
      · have hval := congrArg Subtype.val hxy
        simp [f, hx, hy] at hval
    · by_cases hy : y.1 = a ∨ y.1 = b
      · have hval := congrArg Subtype.val hxy
        simp [f, hx, hy] at hval
      · have hval := congrArg Subtype.val hxy
        simp [f, hx, hy] at hval
        apply Subtype.ext
        exact hval
  have hcard : Fintype.card (G.neighborSet v.1) ≤
      Fintype.card ((terminalQuotientGraph G a b).neighborSet (some v)) :=
    Fintype.card_le_of_injective f hf
  rw [SimpleGraph.card_neighborSet_eq_degree] at hcard
  have hqdeg :
      Fintype.card ((terminalQuotientGraph G a b).neighborSet (some v)) =
        (terminalQuotientGraph G a b).degree (some v) :=
    SimpleGraph.card_neighborSet_eq_degree _ _
  rw [hqdeg] at hcard
  exact (degree_ge_three_of_minDegree_ge_three G hmin v.1).trans hcard

/-- Identifying two nonadjacent terminals preserves minimum degree when no
    internal vertex is adjacent to both terminals.  The hypothesis is
    explicit: terminal identification otherwise merges two neighbors and can
    lower an internal degree by one.
@isnad1 id=le.4h4v.s7.8352ce28ec62 from=translated src=- shape=ed768f75 vocab=6894df76
-/
theorem terminalQuotient_minDegree_ge_three
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : G.minDegree ≥ 3) (_hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hcommon : ∀ z, z ≠ a → z ≠ b →
      ¬ (G.Adj a z ∧ G.Adj b z)) :
    (terminalQuotientGraph G a b).minDegree ≥ 3 := by
  classical
  letI : Nonempty (QuotientVertex a b) := ⟨none⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
    (terminalQuotientGraph G a b) 3
  intro q
  cases q with
  | none => exact terminalQuotient_root_degree_ge_three hmin hnadj
  | some v => exact terminalQuotient_internal_degree_ge_three hmin hcommon

/-- In a minimal counterexample, the safe terminal quotient must itself
    contain a dyadic cycle.  This is the maximal conclusion available before
    solving the quotient-cycle lifting obstruction.
@isnad1 id=haspower.4h4v.s6.5f0042eab771 from=translated src=- shape=00f0d49d vocab=c4dc006a
-/
theorem MinimalCounterexample.terminalQuotient_hasPowerOfTwoCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : MinimalCounterexample G) {a b : V}
    (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hcommon : ∀ z, z ≠ a → z ≠ b →
      ¬ (G.Adj a z ∧ G.Adj b z)) :
    HasPowerOfTwoCycle (terminalQuotientGraph G a b) := by
  classical
  letI : DecidableRel (terminalQuotientGraph G a b).Adj :=
    quotient_decidableRel G a b
  by_contra hno
  have hsmall :
      IsStrictlySmallerCounterexample G (terminalQuotientGraph G a b) := by
    refine ⟨⟨terminalQuotient_minDegree_ge_three M.isCounterexample.1
        hab hnadj hcommon, hno⟩, ?_⟩
    exact terminalQuotient_card_lt hab
  exact M.not_exists_strictly_smaller hsmall

/-
The unrestricted converse requested for root cycles is false.

A triangle a-x-y-a with b isolated becomes a simple cycle through none,
although the internal graph is acyclic and there is no a-b path. Thus a
root cycle can lift through a only, through b only, or through both terminals.
The first two cases need an added hypothesis excluding one-terminal cycles.

Also, an a-x-b path of length two maps to none-x-none, which repeats one
simple-graph edge and is not a Walk.IsCycle. The normal form above therefore
requires distinct internal endpoints.
-/

end Erdos64
