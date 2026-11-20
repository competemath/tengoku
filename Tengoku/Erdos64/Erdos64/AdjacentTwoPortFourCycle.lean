import Tengoku.Erdos64.Erdos64.AdjacentTwoPortThirdNeighbors

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- Two adjacent root-attached ports yield a certified 4-cycle when their
    explicitly supplied third neighbors coincide or are adjacent.
@isnad1 id=haspower.13h7v.s6.0cc857ad2172 from=translated src=- shape=892d7f65 vocab=6d261217
-/
theorem hasPowerOfTwoCycle_of_adjacent_two_port_third_neighbors
    {V : Type u} {G : SimpleGraph V}
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj]
    {r x y z w : V}
    (hxy_ne : x ≠ y)
    (hrx : G.Adj r x) (hry : G.Adj r y) (hxy : G.Adj x y)
    (hzr : z ≠ r) (hzx : z ≠ x) (hzy : z ≠ y) (hxz : G.Adj x z)
    (hwr : w ≠ r) (hwx : w ≠ x) (hwy : w ≠ y) (hyw : G.Adj y w)
    (hcase : z = w ∨ G.Adj z w) :
    HasPowerOfTwoCycle G := by
  rcases hcase with rfl | hzw
  · let q : G.Walk x y :=
      SimpleGraph.Walk.cons hxz
        (SimpleGraph.Walk.cons hyw.symm SimpleGraph.Walk.nil)
    have hq : q.IsPath := by
      dsimp [q]
      refine (SimpleGraph.Walk.cons_isPath_iff hxz _).2 ⟨?_, ?_⟩
      · exact (SimpleGraph.Walk.cons_isPath_iff hyw.symm _).2
          ⟨SimpleGraph.Walk.IsPath.nil, by simp [hzy]⟩
      · simp [hzx.symm, hxy_ne]
    have hroot : r ∉ q.support := by
      simp [q, hrx.ne, hry.ne, hzr.symm]
    obtain ⟨c, hc, hlen⟩ := endpoint_fan_cycle_certificate
      hq hrx hry hroot hxy_ne (by simp [q])
    refine ⟨2, x, c, by omega, hc, ?_⟩
    calc
      c.length = 4 := by simpa [q] using hlen
      _ = 2 ^ 2 := by rfl
  · let q : G.Walk z y :=
      SimpleGraph.Walk.cons hzw
        (SimpleGraph.Walk.cons hyw.symm SimpleGraph.Walk.nil)
    have hq : q.IsPath := by
      dsimp [q]
      refine (SimpleGraph.Walk.cons_isPath_iff hzw _).2 ⟨?_, ?_⟩
      · exact (SimpleGraph.Walk.cons_isPath_iff hyw.symm _).2
          ⟨SimpleGraph.Walk.IsPath.nil, by simp [hwy]⟩
      · simp [hzw.ne, hzy]
    have hroot : x ∉ q.support := by
      simp [q, hzx.symm, hwx.symm, hxy_ne]
    obtain ⟨c, hc, hlen⟩ := endpoint_fan_cycle_certificate
      hq hxz hxy hroot hzy (by simp [q])
    refine ⟨2, z, c, by omega, hc, ?_⟩
    calc
      c.length = 4 := by simpa [q] using hlen
      _ = 2 ^ 2 := by rfl

end Erdos64
