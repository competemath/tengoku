import Tengoku.Erdos64.Erdos64.QuotientCycleLift

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- In a dyadic-free graph, two distinct ports sharing a root have no other
common neighbor: such a vertex would make a 4-cycle through the root.
Despite the historical name, the ports need not be nonadjacent.
@isnad1 id=eq.8h6v.s6.e9ef9835e19e from=translated src=- shape=977c2d71 vocab=b8f8c50f
-/
theorem MinimalCounterexample.common_neighbor_eq_root_of_nonadjacent_ports
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    {r x y z : V}
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : x ≠ y)
    (hxz : G.Adj x z) (hyz : G.Adj y z)
    (hzx : z ≠ x) (hzy : z ≠ y) :
    z = r := by
  by_contra hzroot
  let q : G.Walk r z :=
    SimpleGraph.Walk.cons hry (SimpleGraph.Walk.cons hyz
      SimpleGraph.Walk.nil)
  have hq : q.IsPath := by
    have hq' : q.IsPath := by
      dsimp [q]
      refine (SimpleGraph.Walk.cons_isPath_iff hry _).2 ⟨?_, ?_⟩
      · exact (SimpleGraph.Walk.cons_isPath_iff hyz _).2
          ⟨SimpleGraph.Walk.IsPath.nil, by
            simpa only [SimpleGraph.Walk.support_nil, List.mem_singleton] using
              (Ne.symm hzy)⟩
      · simp only [SimpleGraph.Walk.support_cons, SimpleGraph.Walk.support_nil,
          List.mem_cons]
        intro hrq
        rcases hrq with hrq | hrq
        · exact hry.ne hrq
        · rcases hrq with hrq | hrq
          · exact (Ne.symm hzroot) hrq
          · simp at hrq
    simpa using hq'
  have hxnot : x ∉ q.support := by
    intro hxq
    simpa [q, hrx.ne.symm, hxy, hzx.symm] using hxq
  obtain ⟨c, hc, hclen⟩ := endpoint_fan_cycle_certificate
    hq hrx.symm hxz hxnot (Ne.symm hzroot) (by simp [q])
  apply M.isCounterexample.2
  refine ⟨2, r, c, by omega, hc, ?_⟩
  calc
    c.length = q.length + 2 := hclen
    _ = 4 := by rfl
    _ = 2 ^ 2 := by rfl

/-- The shared-root quotient residual path must attach to both ports away from
the shared root.  If either endpoint attached through the root, the residual
path itself would close with that port to a forbidden dyadic cycle.
@isnad1 id=ex.6h5v.s7.e77911ce830e from=translated src=- shape=5eb24010 vocab=ece15bbb
-/
theorem MinimalCounterexample.shared_root_quotient_residual_path
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    (M : MinimalCounterexample G)
    {r x y : V}
    (hrx : G.Adj r x) (hry : G.Adj r y)
    (hxy : x ≠ y) (hnadj : ¬ G.Adj x y)
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
    M.nonadjacent_terminal_cross_path_of_common_degree_ge_four
      hxy hnadj hcommon4
  have hne : u ≠ v := by
    intro huv
    have hget : p.getVert 0 = p.getVert p.length := by
      simpa [huv]
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

end Erdos64
