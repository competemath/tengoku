import Tengoku.BurningPathTokenGraphs.BurningPathTokenGraphs.PathMetricGraphLower

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The ordered-coordinate distance is attained by a path-token walk

We repeatedly perform a legal move that decreases `pathConfigurationDist` by one. Right-moving
coordinates are processed from the greatest outstanding index; once none remain, left-moving
coordinates are processed from the least outstanding index.
-/

namespace BurningPath

private theorem coordinate_mem' {n k : ℕ} (A : Configuration (Fin n) k) (i : Fin k) :
    coordinate A i ∈ A.1 := by
  change A.1.orderEmbOfFin A.2 i ∈ A.1
  exact Finset.orderEmbOfFin_mem A.1 A.2 i

private theorem coordinate_eq_update_of_move {n k : ℕ}
    {A C : Configuration (Fin n) k} (i : Fin k) (v : Fin n) (hvA : v ∉ A.1)
    (hC : C.1 = insert v (A.1.erase (coordinate A i)))
    (hAC : (pathTokenGraph n k).Adj A C) :
    coordinate C = Function.update (coordinate A) i v := by
  obtain ⟨r, w, _, hwA, hcoordinate⟩ :=
    pathTokenGraph_adj_exists_coordinate_update A C hAC
  have hwC : w ∈ C.1 := by
    have hrw : coordinate C r = w := by
      rw [hcoordinate, Function.update_self]
    rw [← hrw]
    exact coordinate_mem' C r
  have hwv : w = v := by
    rw [hC] at hwC
    rcases Finset.mem_insert.mp hwC with hwv | hwErase
    · exact hwv
    · exact (hwA (Finset.mem_of_mem_erase hwErase)).elim
  subst w
  have hremoved : coordinate A r ∉ C.1 := by
    intro hrC
    have hrRange : coordinate A r ∈ Set.range (C.1.orderEmbOfFin C.2) := by
      rw [Finset.range_orderEmbOfFin]
      exact hrC
    obtain ⟨s, hs'⟩ := hrRange
    have hs : coordinate C s = coordinate A r := by
      change C.1.orderEmbOfFin C.2 s = coordinate A r
      exact hs'
    rw [hcoordinate] at hs
    by_cases hsr : s = r
    · subst s
      rw [Function.update_self] at hs
      exact hvA (hs ▸ coordinate_mem' A r)
    · rw [Function.update_of_ne hsr] at hs
      exact hsr ((coordinate_strictMono A).injective hs)
  have hri : r = i := by
    apply (coordinate_strictMono A).injective
    rw [hC] at hremoved
    by_contra hne
    apply hremoved
    exact Finset.mem_insert.mpr <|
      Or.inr (Finset.mem_erase.mpr ⟨hne, coordinate_mem' A r⟩)
  subst r
  exact hcoordinate

private theorem pathConfigurationDist_eq_succ_of_update {n k : ℕ}
    {A B C : Configuration (Fin n) k} (i : Fin k) (v : Fin n)
    (hcoordinate : coordinate C = Function.update (coordinate A) i v)
    (hstep :
      Nat.dist (coordinate A i).val (coordinate B i).val =
        Nat.dist v.val (coordinate B i).val + 1) :
    pathConfigurationDist A B = pathConfigurationDist C B + 1 := by
  classical
  let fA := fun j : Fin k ↦ Nat.dist (coordinate A j).val (coordinate B j).val
  let fC := fun j : Fin k ↦ Nat.dist (coordinate C j).val (coordinate B j).val
  have hi : fA i = fC i + 1 := by
    simp only [fA, fC]
    rw [hcoordinate, Function.update_self]
    exact hstep
  have hrest :
      (Finset.univ.erase i).sum fA = (Finset.univ.erase i).sum fC := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    simp only [fA, fC]
    rw [hcoordinate, Function.update_of_ne hji]
  change ∑ j, fA j = (∑ j, fC j) + 1
  calc
    ∑ j, fA j = fA i + (Finset.univ.erase i).sum fA :=
      (Finset.add_sum_erase Finset.univ fA (Finset.mem_univ i)).symm
    _ = (fC i + 1) + (Finset.univ.erase i).sum fC := by rw [hi, hrest]
    _ = (fC i + (Finset.univ.erase i).sum fC) + 1 := by omega
    _ = (∑ j, fC j) + 1 := by
      rw [Finset.add_sum_erase Finset.univ fC (Finset.mem_univ i)]

private theorem exists_adj_pathConfigurationDist_eq_succ {n k : ℕ}
    (A B : Configuration (Fin n) k) (hAB : A ≠ B) :
    ∃ C : Configuration (Fin n) k,
      (pathTokenGraph n k).Adj A C ∧
        pathConfigurationDist A B = pathConfigurationDist C B + 1 := by
  classical
  let right : Finset (Fin k) :=
    Finset.univ.filter fun i ↦ coordinate A i < coordinate B i
  by_cases hright : right.Nonempty
  · let i := right.max' hright
    have hiRight : coordinate A i < coordinate B i := by
      have hiMem : i ∈ right := by
        simpa [i] using right.max'_mem hright
      exact (Finset.mem_filter.mp hiMem).2
    let u := coordinate A i
    let v : Fin n := ⟨u.val + 1, by
      have hiVal : u.val < (coordinate B i).val := hiRight
      exact lt_of_le_of_lt (Nat.add_one_le_iff.mpr hiVal) (coordinate B i).isLt⟩
    have hvVal : v.val = u.val + 1 := rfl
    have huA : u ∈ A.1 := by
      exact coordinate_mem' A i
    have huv : (SimpleGraph.pathGraph n).Adj u v := by
      apply SimpleGraph.pathGraph_adj.mpr
      exact Or.inl rfl
    have hvA : v ∉ A.1 := by
      intro hvMem
      have hvRange : v ∈ Set.range (A.1.orderEmbOfFin A.2) := by
        rw [Finset.range_orderEmbOfFin]
        exact hvMem
      obtain ⟨j, hj'⟩ := hvRange
      have hj : coordinate A j = v := by
        change A.1.orderEmbOfFin A.2 j = v
        exact hj'
      have hij : i < j := by
        apply lt_of_not_ge
        intro hji
        have hmono := (coordinate_strictMono A).monotone hji
        have hjVal := congrArg Fin.val hj
        change (coordinate A j).val ≤ u.val at hmono
        change (coordinate A j).val = v.val at hjVal
        omega
      have hjNotRight : j ∉ right := by
        intro hjRight
        have hji : j ≤ i := by
          simpa [i] using right.le_max' j hjRight
        exact (not_le_of_gt hij) hji
      have hjBA : coordinate B j ≤ coordinate A j := by
        apply le_of_not_gt
        intro hjRight
        exact hjNotRight (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjRight⟩)
      have hBmono := coordinate_strictMono B hij
      have hiVal : u.val < (coordinate B i).val := hiRight
      have hjVal := congrArg Fin.val hj
      change (coordinate B j).val ≤ (coordinate A j).val at hjBA
      change (coordinate B i).val < (coordinate B j).val at hBmono
      change (coordinate A j).val = v.val at hjVal
      omega
    have hkPos : 0 < k := by
      rw [← A.2]
      exact Finset.card_pos.mpr ⟨u, huA⟩
    let C : Configuration (Fin n) k :=
      ⟨insert v (A.1.erase u), by
        simp [huA, hvA, A.2]
        omega⟩
    have hAC : (pathTokenGraph n k).Adj A C := by
      apply (tokenGraph_adj_iff_exists_move (SimpleGraph.pathGraph n) k A C).mpr
      exact ⟨u, huA, v, hvA, huv, rfl⟩
    have hcoordinate : coordinate C = Function.update (coordinate A) i v := by
      apply coordinate_eq_update_of_move i v hvA
      · rfl
      · exact hAC
    have hstep :
        Nat.dist (coordinate A i).val (coordinate B i).val =
          Nat.dist v.val (coordinate B i).val + 1 := by
      have hiVal : u.val < (coordinate B i).val := hiRight
      change Nat.dist u.val (coordinate B i).val =
        Nat.dist (u.val + 1) (coordinate B i).val + 1
      unfold Nat.dist
      omega
    exact ⟨C, hAC, pathConfigurationDist_eq_succ_of_update i v hcoordinate hstep⟩
  · have hnoRight : ∀ j, ¬coordinate A j < coordinate B j := by
      intro j hj
      exact hright ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hj⟩⟩
    have hcoordne : coordinate A ≠ coordinate B := by
      intro hcoordinate
      apply hAB
      apply (configurationEquivOrderEmbedding (Fin n) k).injective
      apply RelEmbedding.ext
      intro j
      change coordinate A j = coordinate B j
      exact congrFun hcoordinate j
    obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hcoordne
    have hj₀Left : coordinate B j₀ < coordinate A j₀ :=
      lt_of_le_of_ne (le_of_not_gt (hnoRight j₀)) hj₀.symm
    let left : Finset (Fin k) :=
      Finset.univ.filter fun i ↦ coordinate B i < coordinate A i
    have hleft : left.Nonempty :=
      ⟨j₀, Finset.mem_filter.mpr ⟨Finset.mem_univ j₀, hj₀Left⟩⟩
    let i := left.min' hleft
    have hiLeft : coordinate B i < coordinate A i := by
      have hiMem : i ∈ left := by
        simpa [i] using left.min'_mem hleft
      exact (Finset.mem_filter.mp hiMem).2
    let u := coordinate A i
    let v : Fin n := ⟨u.val - 1, by
      exact (Nat.sub_le u.val 1).trans_lt u.isLt⟩
    have hvVal : v.val = u.val - 1 := rfl
    have huPos : 0 < u.val := by
      have hiVal : (coordinate B i).val < u.val := hiLeft
      omega
    have huA : u ∈ A.1 := coordinate_mem' A i
    have huv : (SimpleGraph.pathGraph n).Adj u v := by
      apply SimpleGraph.pathGraph_adj.mpr
      exact Or.inr (by change u.val - 1 + 1 = u.val; omega)
    have hvA : v ∉ A.1 := by
      intro hvMem
      have hvRange : v ∈ Set.range (A.1.orderEmbOfFin A.2) := by
        rw [Finset.range_orderEmbOfFin]
        exact hvMem
      obtain ⟨j, hj'⟩ := hvRange
      have hj : coordinate A j = v := by
        change A.1.orderEmbOfFin A.2 j = v
        exact hj'
      have hji : j < i := by
        apply lt_of_not_ge
        intro hij
        have hmono := (coordinate_strictMono A).monotone hij
        have hjVal := congrArg Fin.val hj
        change u.val ≤ (coordinate A j).val at hmono
        change (coordinate A j).val = v.val at hjVal
        omega
      have hjNotLeft : j ∉ left := by
        intro hjLeft
        have hij : i ≤ j := by
          simpa [i] using left.min'_le j hjLeft
        exact (not_le_of_gt hji) hij
      have hjAB : coordinate A j ≤ coordinate B j := by
        apply le_of_not_gt
        intro hjLeft
        exact hjNotLeft (Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjLeft⟩)
      have hBmono := coordinate_strictMono B hji
      have hiVal : (coordinate B i).val < u.val := hiLeft
      have hjVal := congrArg Fin.val hj
      change (coordinate A j).val ≤ (coordinate B j).val at hjAB
      change (coordinate B j).val < (coordinate B i).val at hBmono
      change (coordinate A j).val = v.val at hjVal
      omega
    have hkPos : 0 < k := by
      rw [← A.2]
      exact Finset.card_pos.mpr ⟨u, huA⟩
    let C : Configuration (Fin n) k :=
      ⟨insert v (A.1.erase u), by
        simp [huA, hvA, A.2]
        omega⟩
    have hAC : (pathTokenGraph n k).Adj A C := by
      apply (tokenGraph_adj_iff_exists_move (SimpleGraph.pathGraph n) k A C).mpr
      exact ⟨u, huA, v, hvA, huv, rfl⟩
    have hcoordinate : coordinate C = Function.update (coordinate A) i v := by
      apply coordinate_eq_update_of_move i v hvA
      · rfl
      · exact hAC
    have hstep :
        Nat.dist (coordinate A i).val (coordinate B i).val =
          Nat.dist v.val (coordinate B i).val + 1 := by
      have hiVal : (coordinate B i).val < u.val := hiLeft
      change Nat.dist u.val (coordinate B i).val =
        Nat.dist (u.val - 1) (coordinate B i).val + 1
      unfold Nat.dist
      omega
    exact ⟨C, hAC, pathConfigurationDist_eq_succ_of_update i v hcoordinate hstep⟩

/-- There is a path-token walk attaining the ordered-coordinate distance.-/
theorem exists_pathTokenGraph_walk_length_eq_pathConfigurationDist {n k : ℕ}
    (A B : Configuration (Fin n) k) :
    ∃ p : (pathTokenGraph n k).Walk A B,
      p.length = pathConfigurationDist A B := by
  classical
  by_cases hAB : A = B
  · subst B
    exact ⟨.nil, by simp⟩
  · obtain ⟨C, hAC, hdist⟩ :=
      exists_adj_pathConfigurationDist_eq_succ A B hAB
    obtain ⟨p, hp⟩ :=
      exists_pathTokenGraph_walk_length_eq_pathConfigurationDist C B
    refine ⟨.cons hAC p, ?_⟩
    simp only [SimpleGraph.Walk.length_cons, hp]
    exact hdist.symm
termination_by pathConfigurationDist A B
decreasing_by omega

/-- Any two path-token configurations are reachable.-/
theorem pathTokenGraph_reachable {n k : ℕ} (A B : Configuration (Fin n) k) :
    (pathTokenGraph n k).Reachable A B := by
  obtain ⟨p, _⟩ := exists_pathTokenGraph_walk_length_eq_pathConfigurationDist A B
  exact p.reachable

/-- The graph distance on the path token graph is the ordered-coordinate distance.-/
theorem pathTokenGraph_dist_eq_pathConfigurationDist {n k : ℕ}
    (A B : Configuration (Fin n) k) :
    (pathTokenGraph n k).dist A B = pathConfigurationDist A B := by
  let hreach := pathTokenGraph_reachable A B
  obtain ⟨p, hp⟩ := exists_pathTokenGraph_walk_length_eq_pathConfigurationDist A B
  apply le_antisymm
  · simpa [hp] using (pathTokenGraph n k).dist_le p
  · obtain ⟨q, hq⟩ := hreach.exists_walk_length_eq_dist
    simpa [hq] using pathConfigurationDist_le_walk_length q

/-- The extended graph distance has the same finite value.-/
theorem pathTokenGraph_edist_eq_pathConfigurationDist {n k : ℕ}
    (A B : Configuration (Fin n) k) :
    (pathTokenGraph n k).edist A B = (pathConfigurationDist A B : ℕ∞) := by
  have hreach := pathTokenGraph_reachable A B
  rw [← hreach.coe_dist_eq_edist, pathTokenGraph_dist_eq_pathConfigurationDist]

end BurningPath
