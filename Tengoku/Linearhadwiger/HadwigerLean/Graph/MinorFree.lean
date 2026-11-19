import Tengoku.Linearhadwiger.HadwigerLean.Graph.Minor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Complete-minor order and the public branch-set condition

Restricting a complete-minor model to fewer branch sets gives monotonicity in
the order of the excluded complete graph. The final equivalence unfolds our
minor-model structure into a branch-set statement using only graph and set
terminology.
-/

namespace HadwigerLean

universe u

/-- A complete-minor model can be restricted to any smaller order.
@isnad1 id=hascliqu.2h4v.s4.81c598f4a69b from=translated src=- shape=57e186f0 vocab=c54cc7a8
-/
theorem hasCliqueMinor_order_mono {V : Type u} {G : SimpleGraph V}
    {m n : ℕ} (hmn : m ≤ n) (hn : HasCliqueMinor G n) :
    HasCliqueMinor G m := by
  obtain ⟨M⟩ := hn
  let e : Fin m ↪ Fin n := Fin.castLEEmb hmn
  refine ⟨{
    branch := fun i => M.branch (e i)
    connected := fun i => M.connected (e i)
    disjoint := ?_
    adjacent := ?_
  }⟩
  · intro i j hij
    exact M.disjoint (fun heq => hij (e.injective heq))
  · intro i j hij
    apply M.adjacent
    have hne : e i ≠ e j := fun heq => hij.ne (e.injective heq)
    simpa using hne

/-- A finite graph excludes `K_t` exactly when its largest complete-minor
order is strictly below `t`. This includes `t = 0` and the empty graph.
@isnad1 id=iff.0h3v.s4.74b7e5ca7f29 from=translated src=- shape=c333ca72 vocab=1fae612a
-/
theorem not_hasCliqueMinor_iff_cliqueMinorNumber_lt
    {V : Type u} [Fintype V] (G : SimpleGraph V) (t : ℕ) :
    ¬ HasCliqueMinor G t ↔ cliqueMinorNumber G < t := by
  constructor
  · intro hnot
    by_contra hlt
    have hle : t ≤ cliqueMinorNumber G := Nat.le_of_not_gt hlt
    exact hnot (hasCliqueMinor_order_mono hle (hasCliqueMinor_cliqueMinorNumber G))
  · intro hlt ht
    exact (Nat.not_le_of_gt hlt) (hasCliqueMinor_le_cliqueMinorNumber ht)

/-- The complete-minor predicate is equivalent to its expanded branch-set
description. In particular the branch sets are connected induced subgraphs,
pairwise disjoint, and every distinct pair touches by an edge.
@isnad1 id=iff.0h3v.s7.9f4b85c09910 from=translated src=- shape=194b85d3 vocab=069fa9a5
-/
theorem hasCliqueMinor_iff_branchSets {V : Type u}
    (G : SimpleGraph V) (t : ℕ) :
    HasCliqueMinor G t ↔
      ∃ B : Fin t → Set V,
        (∀ i, (G.induce (B i)).Connected) ∧
        (Pairwise fun i j => Disjoint (B i) (B j)) ∧
        (∀ i j : Fin t, i ≠ j →
          ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y) := by
  constructor
  · rintro ⟨M⟩
    refine ⟨M.branch, M.connected, M.disjoint, ?_⟩
    intro i j hij
    exact M.adjacent (by simpa using hij)
  · rintro ⟨B, hconn, hdisj, hadj⟩
    refine ⟨{
      branch := B
      connected := hconn
      disjoint := hdisj
      adjacent := ?_
    }⟩
    intro i j hij
    exact hadj i j (by simpa using hij)

end HadwigerLean
