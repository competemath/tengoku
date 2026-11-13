/-- **A tree is the graft of its cut at a path and the subtree there.**-/
theorem graft_cutAt_subAt : ∀ (t : BTree E) (p : List Bool), p ∈ t.paths →
    (t.cutAt p).graft (t.posAt p) (t.subAt p) = t
  | leaf, [], _ => rfl
  | node e l r, [], _ => rfl
  | leaf, _ :: _, h => absurd h (cons_not_mem_paths_leaf _ _)
  | node e l r, false :: p, h => by
    rw [cons_false_mem_paths] at h
    have hlt := posAt_lt_arity_cutAt l p h
    simp only [cutAt_false, posAt_false, subAt_false]
    rw [graft_node_of_lt r _ hlt, graft_cutAt_subAt l p h]
  | node e l r, true :: p, h => by
    rw [cons_true_mem_paths] at h
    simp only [cutAt_true, posAt_true, subAt_true]
    rw [graft_node_of_ge l _ (by omega), show l.arity + r.posAt p - l.arity = r.posAt p by omega,
      graft_cutAt_subAt r p h]
where
  /-- The cut-off leaf is a leaf of the cut tree.-/
  posAt_lt_arity_cutAt : ∀ (t : BTree E) (p : List Bool), p ∈ t.paths →
      t.posAt p < (t.cutAt p).arity
    | leaf, [], _ => by simp
    | node e l r, [], _ => by simp
    | leaf, _ :: _, h => absurd h (cons_not_mem_paths_leaf _ _)
    | node e l r, false :: p, h => by
      rw [cons_false_mem_paths] at h
      have := posAt_lt_arity_cutAt l p h
      simp only [cutAt_false, posAt_false, arity_node]
      omega
    | node e l r, true :: p, h => by
      rw [cons_true_mem_paths] at h
      have := posAt_lt_arity_cutAt r p h
      simp only [cutAt_true, posAt_true, arity_node]
      omega
