import Tengoku.Erdos64.Erdos64.ExactTwoPortCaseSplit
import Tengoku.Erdos64.Erdos64.TwoPortDistinctRoutes

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Terminal identification preserves minimum degree when the identified vertex
has at least three neighbors and any common neighbor can absorb one lost edge.
Unlike the nonadjacent-terminal interface, this includes edge contraction.-/
theorem terminalQuotient_minDegree_ge_three_of_root_and_common
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : G.minDegree ≥ 3)
    (hroot : 3 ≤ (terminalQuotientGraph G a b).degree none)
    (hcommon4 : ∀ z, z ≠ a → z ≠ b →
      (G.Adj a z ∧ G.Adj b z) → 4 ≤ G.degree z) :
    (terminalQuotientGraph G a b).minDegree ≥ 3 := by
  classical
  let : DecidableRel (terminalQuotientGraph G a b).Adj :=
    quotient_decidableRel G a b
  let : Nonempty (QuotientVertex a b) := ⟨none⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
    (terminalQuotientGraph G a b) 3
  intro q
  cases q with
  | none => exact hroot
  | some v =>
      let fFull : G.neighborSet v.1 →
          (terminalQuotientGraph G a b).neighborSet (some v) := fun x =>
        if hx : x.1 = a ∨ x.1 = b then
          ⟨none, by
            rcases hx with hxa | hxb
            · exact Or.inl (by simpa [hxa] using x.2)
            · exact Or.inr (by simpa [hxb] using x.2)⟩
        else
          ⟨some ⟨x.1, by
            exact ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩⟩,
            x.2⟩
      have hfFull : ∀ hnot : ¬ (G.Adj a v.1 ∧ G.Adj b v.1),
          Function.Injective fFull := by
        intro hnot x y hxy
        by_cases hx : x.1 = a ∨ x.1 = b
        · by_cases hy : y.1 = a ∨ y.1 = b
          · rcases hx with hxa | hxb <;> rcases hy with hya | hyb
            · apply Subtype.ext
              exact hxa.trans hya.symm
            · exfalso
              apply hnot
              have hax : G.Adj a v.1 := by
                simpa [hxa] using x.2.symm
              have hby : G.Adj b v.1 := by
                simpa [hyb] using y.2.symm
              exact ⟨hax, hby⟩
            · exfalso
              apply hnot
              have hay : G.Adj a v.1 := by
                simpa [hya] using y.2.symm
              have hbx : G.Adj b v.1 := by
                simpa [hxb] using x.2.symm
              exact ⟨hay, hbx⟩
            · apply Subtype.ext
              exact hxb.trans hyb.symm
          · have hval := congrArg Subtype.val hxy
            simp [fFull, hx, hy] at hval
        · by_cases hy : y.1 = a ∨ y.1 = b
          · have hval := congrArg Subtype.val hxy
            simp [fFull, hx, hy] at hval
          · have hval := congrArg Subtype.val hxy
            simp [fFull, hx, hy] at hval
            apply Subtype.ext
            exact hval
      have hdeg : 3 ≤ G.degree v.1 :=
        degree_ge_three_of_minDegree_ge_three G hmin v.1
      have hcardN : Fintype.card (G.neighborSet v.1) = G.degree v.1 :=
        SimpleGraph.card_neighborSet_eq_degree G v.1
      by_cases hboth : G.Adj v.1 a ∧ G.Adj v.1 b
      · let S := {x : G.neighborSet v.1 // x.1 ≠ a}
        let f : S → (terminalQuotientGraph G a b).neighborSet (some v) :=
          fun x =>
            if hx : x.1.1 = a ∨ x.1.1 = b then
              ⟨none, by
                rcases hx with hxa | hxb
                · exact Or.inl (by simpa [hxa] using x.1.2)
                · exact Or.inr (by simpa [hxb] using x.1.2)⟩
            else
              ⟨some ⟨x.1.1, by
                exact ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩⟩,
                x.1.2⟩
        have hf : Function.Injective f := by
          intro x y hxy
          by_cases hx : x.1.1 = b
          · by_cases hy : y.1.1 = b
            · apply Subtype.ext
              apply Subtype.ext
              exact hx.trans hy.symm
            · have hval := congrArg Subtype.val hxy
              exfalso
              simp [f, hx, hy, y.2] at hval
          · by_cases hy : y.1.1 = b
            · have hval := congrArg Subtype.val hxy
              exfalso
              simp [f, hx, hy, x.2] at hval
            · have hval := congrArg Subtype.val hxy
              simp [f, hx, hy, x.2, y.2] at hval
              apply Subtype.ext
              apply Subtype.ext
              exact hval
        have hcardS : Fintype.card S ≤
            Fintype.card ((terminalQuotientGraph G a b).neighborSet (some v)) :=
          Fintype.card_le_of_injective f hf
        rw [SimpleGraph.card_neighborSet_eq_degree] at hcardS
        have hcardS_eq : Fintype.card S =
            Fintype.card (G.neighborSet v.1) -
              Fintype.card {x : G.neighborSet v.1 // x.1 = a} := by
          simp [S, Fintype.card_subtype_compl]
        have hcardA : Fintype.card {x : G.neighborSet v.1 // x.1 = a} = 1 := by
          apply (Fintype.card_eq_one_iff.mpr)
          refine ⟨⟨⟨a, (G.mem_neighborSet v.1 a).mpr hboth.1⟩, rfl⟩, ?_⟩
          intro x
          apply Subtype.ext
          apply Subtype.ext
          exact x.2
        rw [hcardS_eq, hcardA, hcardN] at hcardS
        have hhigh : 4 ≤ G.degree v.1 := by
          apply hcommon4 v.1 v.2.1 v.2.2
          exact ⟨hboth.1.symm, hboth.2.symm⟩
        omega
      · have hnot : ¬ (G.Adj a v.1 ∧ G.Adj b v.1) := by
          intro h
          exact hboth ⟨h.1.symm, h.2.symm⟩
        have hcardFull : Fintype.card (G.neighborSet v.1) ≤
            Fintype.card ((terminalQuotientGraph G a b).neighborSet (some v)) :=
          Fintype.card_le_of_injective fFull (hfFull hnot)
        rw [SimpleGraph.card_neighborSet_eq_degree] at hcardFull
        have hqdeg :
            Fintype.card ((terminalQuotientGraph G a b).neighborSet (some v)) =
              (terminalQuotientGraph G a b).degree (some v) :=
          SimpleGraph.card_neighborSet_eq_degree _ _
        rw [hqdeg] at hcardFull
        exact hdeg.trans hcardFull

/-- A sufficiently large quotient root forces the existing cross-path residual.-/
theorem MinimalCounterexample.terminal_cross_path_of_root_and_common
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    {a b : V} (hab : a ≠ b)
    (hroot : 3 ≤ (terminalQuotientGraph G a b).degree none)
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
  let : DecidableRel (terminalQuotientGraph G a b).Adj :=
    quotient_decidableRel G a b
  have hyes : HasPowerOfTwoCycle (terminalQuotientGraph G a b) := by
    by_contra hno
    exact M.not_exists_strictly_smaller
      ⟨⟨terminalQuotient_minDegree_ge_three_of_root_and_common
        M.isCounterexample.1 hroot hcommon4, hno⟩, terminalQuotient_card_lt hab⟩
  obtain ⟨k, z, c, hk, hc, hlen⟩ := hyes
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

/-- Exclude either residual endpoint being the shared root without assuming that
the terminals are nonadjacent.-/
theorem MinimalCounterexample.shared_root_residual_path_of_quotient_root_degree
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    {r x y : V}
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hxy : x ≠ y)
    (hqroot : 3 ≤ (terminalQuotientGraph G x y).degree none)
    (hroot_degree : 4 ≤ G.degree r) :
    ∃ k : ℕ, ∃ u v : V, ∃ p : G.Walk u v,
      k ≥ 2 ∧
      p.IsPath ∧
      (∀ w, w ∈ p.support → w ≠ x ∧ w ≠ y) ∧
      p.length + 2 = 2 ^ k ∧
      ((G.Adj x u ∧ G.Adj y v ∧ u ≠ r ∧ v ≠ r) ∨
        (G.Adj y u ∧ G.Adj x v ∧ u ≠ r ∧ v ≠ r)) := by
  classical
  have hcommon4 : ∀ z, z ≠ x → z ≠ y →
      (G.Adj x z ∧ G.Adj y z) → 4 ≤ G.degree z := by
    intro z hzx hzy hz
    have hzroot := M.common_neighbor_eq_root_of_nonadjacent_ports
      hrx hry hxy hz.1 hz.2 hzx hzy
    subst z
    exact hroot_degree
  obtain ⟨k, u, v, p, hk, hp, havoid, hlen, hadj⟩ :=
    M.terminal_cross_path_of_root_and_common
      hxy hqroot hcommon4
  have hne : u ≠ v := by
    intro huv
    have hget : p.getVert 0 = p.getVert p.length := by
      simp [huv]
    have hidx := hp.getVert_injOn
      (x₁ := 0) (x₂ := p.length)
      (show 0 ≤ p.length by exact Nat.zero_le _)
      (show p.length ≤ p.length by exact le_rfl) hget
    have hpow : 4 ≤ 2 ^ k := four_le_pow_two hk
    omega
  have hlong : 1 < p.length := by
    have hpow : 4 ≤ 2 ^ k := four_le_pow_two hk
    omega
  rcases hadj with ⟨hxu, hyv⟩ | ⟨hyu, hxv⟩
  · by_cases hur : u = r
    · exfalso
      subst u
      have hyavoid : y ∉ p.support := by
        intro hy
        exact (havoid y hy).2 rfl
      have hcycle : HasPowerOfTwoCycle G := by
        obtain ⟨c, hc, hclen⟩ := endpoint_fan_cycle_certificate
          hp hry.symm hyv hyavoid hne hlong
        refine ⟨k, r, c, hk, hc, ?_⟩
        exact hclen.trans hlen
      exact M.isCounterexample.2 hcycle
    · by_cases hvr : v = r
      · exfalso
        subst v
        have hxavoid : x ∉ p.support := by
          intro hx
          exact (havoid x hx).1 rfl
        have hcycle : HasPowerOfTwoCycle G := by
          obtain ⟨c, hc, hclen⟩ := endpoint_fan_cycle_certificate
            hp hxu hrx.symm hxavoid hne hlong
          refine ⟨k, u, c, hk, hc, ?_⟩
          exact hclen.trans hlen
        exact M.isCounterexample.2 hcycle
      · exact ⟨k, u, v, p, hk, hp, havoid, hlen,
          Or.inl ⟨hxu, hyv, hur, hvr⟩⟩
  · by_cases hvr : v = r
    · exfalso
      subst v
      have hyavoid : y ∉ p.support := by
        intro hy
        exact (havoid y hy).2 rfl
      have hcycle : HasPowerOfTwoCycle G := by
        obtain ⟨c, hc, hclen⟩ := endpoint_fan_cycle_certificate
          hp hyu hry.symm hyavoid hne hlong
        refine ⟨k, u, c, hk, hc, ?_⟩
        exact hclen.trans hlen
      exact M.isCounterexample.2 hcycle
    · by_cases hur : u = r
      · exfalso
        subst u
        have hxavoid : x ∉ p.support := by
          intro hx
          exact (havoid x hx).1 rfl
        have hcycle : HasPowerOfTwoCycle G := by
          obtain ⟨c, hc, hclen⟩ := endpoint_fan_cycle_certificate
            hp hrx.symm hxv hxavoid hne hlong
          refine ⟨k, r, c, hk, hc, ?_⟩
          exact hclen.trans hlen
        exact M.isCounterexample.2 hcycle
      · exact ⟨k, u, v, p, hk, hp, havoid, hlen,
          Or.inr ⟨hyu, hxv, hur, hvr⟩⟩

/-- Close the generalized residual inside an exact two-port side.-/
theorem MinimalCounterexample.exact_two_port_side_dyadic_path_of_quotient_root_degree
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hxy : x ≠ y)
    (hqroot : 3 ≤ (terminalQuotientGraph G x y).degree none)
    (hroot_degree : 4 ≤ G.degree r)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hports : ∀ a, a ∈ D → G.Adj a r → a = x ∨ a = y) :
    ∃ k : ℕ, ∃ q : G.Walk x y,
      2 ≤ k ∧ q.IsPath ∧ q.length = 2 ^ k ∧
      (∀ a, a ∈ q.support → a ∈ D) ∧ r ∉ q.support := by
  obtain ⟨k, u, v, p, hk, hp, havoid, hlen, hadj⟩ :=
    M.shared_root_residual_path_of_quotient_root_degree hrx hry hxy hqroot hroot_degree
  have hur : u ≠ r := hadj.elim (fun h => h.2.2.1) (fun h => h.2.2.1)
  have hvr : v ≠ r := hadj.elim (fun h => h.2.2.2) (fun h => h.2.2.2)
  have hattach : (G.Adj x u ∧ G.Adj y v) ∨ (G.Adj y u ∧ G.Adj x v) :=
    hadj.imp (fun h => ⟨h.1, h.2.1⟩) (fun h => ⟨h.1, h.2.1⟩)
  obtain ⟨_, _, _, hroot⟩ := cross_residual_in_exact_two_port_side
    hr hx hy hboundary hports hur hvr havoid hattach
  have hpath := cross_residual_path_to_dyadic_port_path
    hrx hry hxy hp havoid hroot hlen hattach
  have hnormalized : ∃ q : G.Walk x y,
      q.IsPath ∧ r ∉ q.support ∧ q.length = 2 ^ k := by
    rcases hpath with hforward | ⟨q, hq, hqr, hqlen⟩
    · exact hforward
    · exact ⟨q.reverse, hq.reverse, by simpa using hqr, by simpa using hqlen⟩
  obtain ⟨q, hq, hqr, hqlen⟩ := hnormalized
  exact ⟨k, q, hk, hq, hqlen,
    SimpleGraph.Walk.IsPath.support_subset_of_boundary_avoiding_root
      hq hx hqr hboundary, hqr⟩

/-- Adjacent exact ports also force a dyadic path inside their side. Their
identification has at least three distinct neighbors: the shared root and
one additional neighbor at each port. A forbidden four-cycle prevents those
additional neighbors from coinciding.-/
theorem MinimalCounterexample.exact_adjacent_two_port_side_dyadic_path
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hxy : x ≠ y) (hadj : G.Adj x y)
    (hroot_degree : 4 ≤ G.degree r)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hports : ∀ a, a ∈ D → G.Adj a r → a = x ∨ a = y) :
    ∃ k : ℕ, ∃ q : G.Walk x y,
      2 ≤ k ∧ q.IsPath ∧ q.length = 2 ^ k ∧
      (∀ a, a ∈ q.support → a ∈ D) ∧ r ∉ q.support := by
  classical
  have hexact : ∀ a, a ∈ D → (G.Adj a r ↔ a = x ∨ a = y) := by
    intro a ha
    refine ⟨hports a ha, ?_⟩
    rintro (rfl | rfl)
    · exact hrx.symm
    · exact hry.symm
  obtain ⟨z, w, _, _, hzr, hzx, hzy, hxz, hwr, hwx, hwy, hyw⟩ :=
    adjacent_exact_two_ports_have_internal_third_neighbors D r x y
      hr ⟨hx, hy, hxy⟩ hboundary hexact M.isCounterexample.1 hadj
  have hzw : z ≠ w := by
    intro hzw
    have hzy' : G.Adj y z := hzw ▸ hyw
    exact hzr (M.common_neighbor_eq_root_of_nonadjacent_ports
      hrx hry hxy hxz hzy' hzx hzy)
  let rr : Internal x y := ⟨r, hrx.ne, hry.ne⟩
  let zz : Internal x y := ⟨z, hzx, hzy⟩
  let ww : Internal x y := ⟨w, hwx, hwy⟩
  have hthree : ({some rr, some zz, some ww} : Finset (QuotientVertex x y)).card = 3 := by
    simp [rr, zz, ww, hzr.symm, hwr.symm, hzw]
  have hsub : ({some rr, some zz, some ww} : Finset (QuotientVertex x y)) ⊆
      (terminalQuotientGraph G x y).neighborFinset none := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl
    · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Or.inl hrx.symm)
    · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Or.inl hxz)
    · exact (SimpleGraph.mem_neighborFinset _ _ _).mpr (Or.inr hyw)
  have hqroot := Finset.card_le_card hsub
  rw [hthree, SimpleGraph.card_neighborFinset_eq_degree] at hqroot
  exact M.exact_two_port_side_dyadic_path_of_quotient_root_degree
    D r x y hr hx hy hrx hry hxy hqroot hroot_degree hboundary hports

/-- The dyadic port path is available in both adjacency branches. This still
has a two-edge offset when closed through the root, so it is not itself a
contradiction to the absence of dyadic cycles.-/
theorem MinimalCounterexample.exact_two_port_side_dyadic_path_unrestricted
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : x ≠ y)
    (hroot_degree : 4 ≤ G.degree r)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hports : ∀ a, a ∈ D → G.Adj a r → a = x ∨ a = y) :
    ∃ k : ℕ, ∃ q : G.Walk x y,
      2 ≤ k ∧ q.IsPath ∧ q.length = 2 ^ k ∧
      (∀ a, a ∈ q.support → a ∈ D) ∧ r ∉ q.support := by
  by_cases hadj : G.Adj x y
  · exact M.exact_adjacent_two_port_side_dyadic_path
      D r x y hr hx hy hrx hry hxy hadj hroot_degree hboundary hports
  · exact M.exact_two_port_side_dyadic_path
      D r x y hr hx hy hrx hry hxy hadj hroot_degree hboundary hports

/-- Every exact two-port side at a root of degree at least four is
nonbipartite. Adjacent ports provide an odd edge; nonadjacent ports provide
an odd path from edge completion. Neither branch requires cubic ports.-/
theorem MinimalCounterexample.exact_two_port_side_not_isBipartite_unrestricted
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    (D : Finset V) (r x y : V)
    (hr : r ∉ D) (hx : x ∈ D) (hy : y ∈ D)
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : x ≠ y)
    (hroot_degree : 4 ≤ G.degree r)
    (hboundary : ∀ a, a ∈ D → ∀ b, b ∉ D → G.Adj a b → b = r)
    (hports : ∀ a, a ∈ D → G.Adj a r → a = x ∨ a = y) :
    ¬ (G.induce (↑D : Set V)).IsBipartite := by
  by_cases hadj : G.Adj x y
  · obtain ⟨k, q, hk, _, hlen, hinside, _⟩ :=
      M.exact_adjacent_two_port_side_dyadic_path
        D r x y hr hx hy hrx hry hxy hadj hroot_degree hboundary hports
    let q' := q.induce (↑D : Set V) hinside
    have hq'len : q'.length = q.length := by
      have h := congrArg (fun w : G.Walk x y => w.length) (q.map_induce hinside)
      exact (SimpleGraph.Walk.length_map
        (SimpleGraph.Embedding.induce (↑D : Set V)).toHom q').symm.trans h
    have hedge : (G.induce (↑D : Set V)).Adj ⟨x, hx⟩ ⟨y, hy⟩ := hadj
    have heven : Even q'.length := by
      rw [hq'len, hlen]
      exact (show Even (2 : ℕ) by decide).pow_of_ne_zero (by omega)
    exact not_isBipartite_of_opposite_parity_routes hedge.toWalk q'
      (by simp) heven
  · exact M.exact_two_port_side_not_isBipartite
      D r x y hr hx hy hrx hry hxy hadj hroot_degree hboundary hports

/-- Both components at a cut vertex of a vertex-minimal counterexample are
nonbipartite, regardless of whether their two root ports are adjacent.-/
theorem MinimalCounterexample.rootDeleted_cut_side_not_isBipartite
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G) (r : V)
    (C D : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (hCD : C ≠ D) :
    ¬ (G.induce (↑(rootDeletedComponentCarrier G r C) : Set V)).IsBipartite := by
  classical
  let := Fintype.ofFinite ((G.induce {v : V | v ≠ r}).ConnectedComponent)
  obtain ⟨_, _, hcard, _, hdegree⟩ :=
    M.rootDeleted_two_components_exact_balanced r C D hCD
  obtain ⟨x, y, hx, hy, hxy, hrx, hry, hports⟩ :=
    rootDeletedComponent_twoPort_attachment_exact r C hcard
  have hboundary : ∀ a, a ∈ rootDeletedComponentCarrier G r C →
      ∀ b, b ∉ rootDeletedComponentCarrier G r C → G.Adj a b → b = r := by
    intro a ha b hb hab
    rcases (rootDeletedComponent_boundary r M.isConnected C).1 a ha b hab with
      hbC | hbr
    · exact (hb hbC).elim
    · exact hbr
  exact M.exact_two_port_side_not_isBipartite_unrestricted
    (rootDeletedComponentCarrier G r C) r x y
    (rootDeletedComponentCarrier_nonempty_not_mem G r C).2
    hx hy hrx hry hxy (by omega) hboundary hports

end Erdos64
