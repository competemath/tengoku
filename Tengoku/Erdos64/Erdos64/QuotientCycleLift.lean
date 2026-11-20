import Tengoku.Erdos64.Erdos64.HighDegreeTerminalQuotient
import Tengoku.Erdos64.Erdos64.Arithmetic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-
The internal part of a terminal quotient embeds back into the ambient graph.
This is the missing transport needed to distinguish quotient cycles that use
the identified terminal from cycles that were already present internally.
-/
/--
@isnad1 id=ex.2h6v.s7.ceab46b419c0 from=translated src=- shape=9d632b2a vocab=eda80154
-/
theorem quotient_cycle_lift_of_avoids_none
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} {z : QuotientVertex a b}
    {c : (terminalQuotientGraph G a b).Walk z z}
    (hc : c.IsCycle)
    (hnone : none ∉ c.support) :
    ∃ u : V, ∃ d : G.Walk u u, d.IsCycle ∧ d.length = c.length := by
  let S : Set (QuotientVertex a b) := Set.range
    (fun v : Internal a b => some v)
  have hcS : ∀ v, v ∈ c.support → v ∈ S := by
    intro v hv
    cases v with
    | none => exact (hnone hv).elim
    | some v => exact ⟨v, rfl⟩
  let ci := c.induce S hcS
  let e : (terminalQuotientGraph G a b).induce S →g G :=
    { toFun := fun q => (Classical.choose q.property).1
      map_rel' := by
        intro q₁ q₂ hq
        let v₁ := Classical.choose q₁.property
        let v₂ := Classical.choose q₂.property
        have hv₁ : some v₁ = q₁.1 := Classical.choose_spec q₁.property
        have hv₂ : some v₂ = q₂.1 := Classical.choose_spec q₂.property
        change (terminalQuotientGraph G a b).Adj q₁.1 q₂.1 at hq
        rw [← hv₁, ← hv₂] at hq
        exact hq }
  have he : Function.Injective e := by
    intro q₁ q₂ hq
    let v₁ := Classical.choose q₁.property
    let v₂ := Classical.choose q₂.property
    have hv₁ : some v₁ = q₁.1 := Classical.choose_spec q₁.property
    have hv₂ : some v₂ = q₂.1 := Classical.choose_spec q₂.property
    have hval : v₁.1 = v₂.1 := by
      change v₁.1 = v₂.1 at hq
      exact hq
    apply Subtype.ext
    rw [← hv₁, ← hv₂]
    congr
    exact Subtype.ext hval
  let emb : (terminalQuotientGraph G a b).induce S ↪g
      terminalQuotientGraph G a b := SimpleGraph.Embedding.induce S
  have hmap : ci.map emb.toHom = c := by
    dsimp [ci]
    exact SimpleGraph.Walk.map_induce c hcS
  have hci_map : (ci.map emb.toHom).IsCycle := by
    rw [hmap]
    exact hc
  have hci : ci.IsCycle :=
    (SimpleGraph.Walk.isCycle_map_iff_of_injective emb.injective).mp hci_map
  refine ⟨_, ci.map e, hci.map he, ?_⟩
  rw [SimpleGraph.Walk.length_map]
  have hlen_induce : ∀ {u v : QuotientVertex a b}
      (w : (terminalQuotientGraph G a b).Walk u v)
      (hw : ∀ x ∈ w.support, x ∈ S),
      (w.induce S hw).length = w.length := by
    intro u v w
    induction w with
    | nil => intro hw; rfl
    | @cons u v w huv q ih =>
        intro hw
        simp [SimpleGraph.Walk.induce, ih]
  exact hlen_induce c hcS

/- A path in the quotient that avoids the identified terminal lifts to the
ambient graph, while retaining which original terminal is adjacent at each
endpoint. -/
/--
@isnad1 id=ex.4h7v.s7.62b1e288bda4 from=translated src=- shape=6b3ee5f2 vocab=b94571f6
-/
theorem quotient_path_lift_of_avoids_none
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} {z₁ z₂ : QuotientVertex a b}
    {p : (terminalQuotientGraph G a b).Walk z₁ z₂}
    (hp : p.IsPath)
    (hnone : ∀ v, v ∈ p.support → v ≠ none)
    (hstart : (terminalQuotientGraph G a b).Adj none z₁)
    (hend : (terminalQuotientGraph G a b).Adj z₂ none) :
    ∃ x y : V, ∃ q : G.Walk x y,
      q.IsPath ∧ q.length = p.length ∧
      (G.Adj a x ∨ G.Adj b x) ∧
      (G.Adj a y ∨ G.Adj b y) ∧
      (∀ v, v ∈ q.support → v ≠ a ∧ v ≠ b) := by
  let S : Set (QuotientVertex a b) := Set.range
    (fun v : Internal a b => some v)
  have hpS : ∀ v, v ∈ p.support → v ∈ S := by
    intro v hv
    cases v with
    | none => exact (hnone none hv rfl).elim
    | some v => exact ⟨v, rfl⟩
  let s₁ : {v : QuotientVertex a b // v ∈ S} :=
    ⟨z₁, hpS z₁ p.start_mem_support⟩
  let s₂ : {v : QuotientVertex a b // v ∈ S} :=
    ⟨z₂, hpS z₂ p.end_mem_support⟩
  let pi : ((terminalQuotientGraph G a b).induce S).Walk s₁ s₂ := by
    simpa [s₁, s₂] using p.induce S hpS
  let e : (terminalQuotientGraph G a b).induce S →g G :=
    { toFun := fun q => (Classical.choose q.property).1
      map_rel' := by
        intro q₁ q₂ hq
        let v₁ := Classical.choose q₁.property
        let v₂ := Classical.choose q₂.property
        have hv₁ : some v₁ = q₁.1 := Classical.choose_spec q₁.property
        have hv₂ : some v₂ = q₂.1 := Classical.choose_spec q₂.property
        change (terminalQuotientGraph G a b).Adj q₁.1 q₂.1 at hq
        rw [← hv₁, ← hv₂] at hq
        exact hq }
  have he : Function.Injective e := by
    intro q₁ q₂ hq
    let v₁ := Classical.choose q₁.property
    let v₂ := Classical.choose q₂.property
    have hv₁ : some v₁ = q₁.1 := Classical.choose_spec q₁.property
    have hv₂ : some v₂ = q₂.1 := Classical.choose_spec q₂.property
    have hval : v₁.1 = v₂.1 := by
      change v₁.1 = v₂.1 at hq
      exact hq
    apply Subtype.ext
    rw [← hv₁, ← hv₂]
    congr
    exact Subtype.ext hval
  let emb : (terminalQuotientGraph G a b).induce S ↪g
      terminalQuotientGraph G a b := SimpleGraph.Embedding.induce S
  have hmap : pi.map emb.toHom = p := by
    dsimp [pi]
    exact SimpleGraph.Walk.map_induce p hpS
  have hpi : pi.IsPath := by
    apply (SimpleGraph.Walk.isPath_map_iff_of_injective
      (p := pi) (f := emb.toHom) emb.injective).mp
    rw [hmap]
    exact hp
  let q : G.Walk (e s₁) (e s₂) := pi.map e
  have hq : q.IsPath := by
    exact hpi.map he
  have hlen_induce : ∀ {u v : QuotientVertex a b}
      (w : (terminalQuotientGraph G a b).Walk u v)
      (hw : ∀ x ∈ w.support, x ∈ S),
      (w.induce S hw).length = w.length := by
    intro u v w
    induction w with
    | nil => intro hw; rfl
    | @cons u v w huv r ih =>
        intro hw
        simp [SimpleGraph.Walk.induce, ih]
  have hroot_start : G.Adj a (e s₁) ∨ G.Adj b (e s₁) := by
    let v := Classical.choose s₁.property
    have hv : some v = s₁.1 := Classical.choose_spec s₁.property
    have hs : (terminalQuotientGraph G a b).Adj none (some v) := by
      rw [hv]
      simpa [emb, s₁] using hstart
    change G.Adj a v.1 ∨ G.Adj b v.1
    simpa [q, e, v] using hs
  have hroot_end : G.Adj a (e s₂) ∨ G.Adj b (e s₂) := by
    let v := Classical.choose s₂.property
    have hv : some v = s₂.1 := Classical.choose_spec s₂.property
    have he' : (terminalQuotientGraph G a b).Adj (some v) none := by
      rw [hv]
      simpa [emb, s₂] using hend
    change G.Adj a v.1 ∨ G.Adj b v.1
    simpa [q, e, v] using he'.symm
  have havoid : ∀ v, v ∈ q.support → v ≠ a ∧ v ≠ b := by
    intro v hv
    change v ∈ (pi.map e).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨z, hz, hze⟩ := List.mem_map.mp hv
    let w := Classical.choose z.property
    have hw : some w = z.1 := Classical.choose_spec z.property
    have hval : w.1 = v := by
      change w.1 = v at hze
      exact hze
    exact ⟨fun h => w.2.1 (hval.trans h),
      fun h => w.2.2 (hval.trans h)⟩
  refine ⟨e s₁, e s₂, q, hq, ?_, hroot_start, hroot_end, havoid⟩
  change (pi.map e).length = p.length
  rw [SimpleGraph.Walk.length_map]
  exact hlen_induce p hpS

/- A dyadic quotient cycle through the identified terminal either lifts to an
ambient dyadic cycle or exposes an opposite-port path with the exact residual
length. -/
/--
@isnad1 id=or.4h7v.s8.3649b6ef7c9c from=translated src=- shape=9ee49c54 vocab=aeebf9fa
-/
theorem quotient_dyadic_cycle_through_none_lift_or_cross_path
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    {a b : V} {z : QuotientVertex a b}
    {c : (terminalQuotientGraph G a b).Walk z z}
    (hc : c.IsCycle)
    (hnone : none ∈ c.support)
    {k : ℕ} (hk : 2 ≤ k)
    (hlen : c.length = 2 ^ k) :
    (∃ u : V, ∃ d : G.Walk u u,
      d.IsCycle ∧ d.length = 2 ^ k) ∨
    (∃ x y : V, ∃ p : G.Walk x y,
      p.IsPath ∧
      (∀ v, v ∈ p.support → v ≠ a ∧ v ≠ b) ∧
      p.length + 2 = 2 ^ k ∧
      ((G.Adj a x ∧ G.Adj b y) ∨
        (G.Adj b x ∧ G.Adj a y))) := by
  let r := c.rotate none hnone
  have hr : r.IsCycle := hc.rotate hnone
  cases hR : r with
  | nil =>
      have : (SimpleGraph.Walk.nil :
          (terminalQuotientGraph G a b).Walk none none).IsCycle := by
        simpa [hR] using hr
      exact (SimpleGraph.Walk.not_isCycle_nil this).elim
  | @cons u v w h q =>
      have hr' :
          (SimpleGraph.Walk.cons h q).IsCycle := by
        simpa [hR] using hr
      have hqnotnil : ¬q.Nil :=
        SimpleGraph.Walk.not_nil_of_isCycle_cons hr'
      have hqpath : q.IsPath := by
        simpa using hr'.isPath_tail
      have hdropnone : ∀ t, t ∈ q.dropLast.support → t ≠ none := by
        intro t ht
        have hnodup : (q.dropLast.support ++ [none]).Nodup := by
          rw [q.support_dropLast_concat hqnotnil]
          exact hqpath.support_nodup
        intro ht_none
        exact (List.disjoint_left.mp (List.disjoint_of_nodup_append hnodup))
          ht (by simpa [ht_none])
      obtain ⟨x, y, p, hp, hpl, hxa, hya, havoid⟩ :=
        quotient_path_lift_of_avoids_none
          (p := q.dropLast) hqpath.dropLast hdropnone h
          (q.adj_penultimate hqnotnil)
      have hclen : c.length = q.dropLast.length + 2 := by
        calc
          c.length = r.length := by
            symm
            exact SimpleGraph.Walk.length_rotate c none hnone
          _ = (SimpleGraph.Walk.cons h q).length := by rw [hR]
          _ = q.length + 1 := by simp
          _ = q.dropLast.length + 2 := by
            rw [← q.length_dropLast_add_one hqnotnil]
      have hcrosslen : p.length + 2 = 2 ^ k := by
        omega
      have hpow : 4 ≤ 2 ^ k := four_le_pow_two hk
      have hlong : 1 < p.length := by omega
      have hxy : x ≠ y := by
        intro hxy
        have hget : p.getVert 0 = p.getVert p.length := by
          simpa [hxy]
        have hidx := hp.getVert_injOn
          (x₁ := 0) (x₂ := p.length)
          (show 0 ≤ p.length by exact Nat.zero_le _)
          (show p.length ≤ p.length by exact le_rfl) hget
        omega
      rcases hxa with hxa | hxb <;> rcases hya with hya | hyb
      · obtain ⟨d, hd, hdl⟩ := endpoint_fan_cycle_certificate
          hp hxa hya (fun ht => (havoid a ht).1 rfl) hxy hlong
        left
        refine ⟨x, d, hd, ?_⟩
        omega
      · right
        refine ⟨x, y, p, hp, havoid, hcrosslen, ?_⟩
        exact Or.inl ⟨hxa, hyb⟩
      · right
        refine ⟨x, y, p, hp, havoid, hcrosslen, ?_⟩
        exact Or.inr ⟨hxb, hya⟩
      · obtain ⟨d, hd, hdl⟩ := endpoint_fan_cycle_certificate
          hp hxb hyb (fun ht => (havoid b ht).2 rfl) hxy hlong
        left
        refine ⟨x, d, hd, ?_⟩
        omega

/- Minimality forces the quotient-cycle alternative to land in the
opposite-port residual path branch whenever the ambient graph is dyadic-free. -/
/--
@isnad1 id=ex.4h4v.s7.09eacacb60d0 from=translated src=- shape=c18035a5 vocab=8896c3cb
-/
theorem MinimalCounterexample.nonadjacent_terminal_cross_path
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    {a b : V} (hab : a ≠ b) (hnadj : ¬G.Adj a b)
    (hcommon : ∀ z, z ≠ a → z ≠ b →
      ¬ (G.Adj a z ∧ G.Adj b z)) :
    ∃ k : ℕ, ∃ x y : V, ∃ p : G.Walk x y,
      k ≥ 2 ∧
      p.IsPath ∧
      (∀ v, v ∈ p.support → v ≠ a ∧ v ≠ b) ∧
      p.length + 2 = 2 ^ k ∧
      ((G.Adj a x ∧ G.Adj b y) ∨
        (G.Adj b x ∧ G.Adj a y)) := by
  classical
  letI : DecidableRel (terminalQuotientGraph G a b).Adj :=
    quotient_decidableRel G a b
  obtain ⟨k, z, c, hk, hc, hlen⟩ :=
    M.terminalQuotient_hasPowerOfTwoCycle hab hnadj hcommon
  have hnone : none ∈ c.support := by
    by_contra hnone
    obtain ⟨u, d, hd, hdl⟩ :=
      quotient_cycle_lift_of_avoids_none hc hnone
    exact M.isCounterexample.2 ⟨k, u, d, hk, hd, hdl.trans hlen⟩
  obtain hbranch :=
    quotient_dyadic_cycle_through_none_lift_or_cross_path
      hc hnone hk hlen
  rcases hbranch with ⟨u, d, hd, hdl⟩ | hcross
  · exact (M.isCounterexample.2 ⟨k, u, d, hk, hd, hdl⟩).elim
  · rcases hcross with ⟨x, y, p, hp, hav, hlenp, hadj⟩
    exact ⟨k, x, y, p, hk, hp, hav, hlenp, hadj⟩

/- The same residual-path certificate remains available when the two
   terminals share a common internal vertex, provided every such common
   vertex has degree at least four. -/
/--
@isnad1 id=ex.4h4v.s7.848c6b85f4bc from=translated src=- shape=dddad306 vocab=ece15bbb
-/
theorem MinimalCounterexample.nonadjacent_terminal_cross_path_of_common_degree_ge_four
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    {a b : V} (hab : a ≠ b) (hnadj : ¬G.Adj a b)
    (hcommon4 : ∀ z, z ≠ a → z ≠ b →
      (G.Adj a z ∧ G.Adj b z) → 4 ≤ G.degree z) :
    ∃ k : ℕ, ∃ x y : V, ∃ p : G.Walk x y,
      k ≥ 2 ∧
      p.IsPath ∧
      (∀ v, v ∈ p.support → v ≠ a ∧ v ≠ b) ∧
      p.length + 2 = 2 ^ k ∧
      ((G.Adj a x ∧ G.Adj b y) ∨
        (G.Adj b x ∧ G.Adj a y)) := by
  classical
  letI : DecidableRel (terminalQuotientGraph G a b).Adj :=
    quotient_decidableRel G a b
  obtain ⟨k, z, c, hk, hc, hlen⟩ :=
    M.terminalQuotient_hasPowerOfTwoCycle_of_common_degree_ge_four
      hab hnadj hcommon4
  have hnone : none ∈ c.support := by
    by_contra hnone
    obtain ⟨u, d, hd, hdl⟩ :=
      quotient_cycle_lift_of_avoids_none hc hnone
    exact M.isCounterexample.2 ⟨k, u, d, hk, hd, hdl.trans hlen⟩
  obtain hbranch :=
    quotient_dyadic_cycle_through_none_lift_or_cross_path
      hc hnone hk hlen
  rcases hbranch with ⟨u, d, hd, hdl⟩ | hcross
  · exact (M.isCounterexample.2 ⟨k, u, d, hk, hd, hdl⟩).elim
  · rcases hcross with ⟨x, y, p, hp, hav, hlenp, hadj⟩
    exact ⟨k, x, y, p, hk, hp, hav, hlenp, hadj⟩

end Erdos64
