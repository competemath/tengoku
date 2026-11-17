import Tengoku.TunnellTwoToOneMap.TunnellMap.GloballyRanked

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Strict preference lists from a global edge ranking

At each source, sorting all targets by the global edge key gives the finite
strict preference list consumed by deferred acceptance.
-/

namespace TunnellMap

namespace GloballyRanked

variable {K S T : Type*} [LinearOrder K] [Fintype T] [DecidableEq T]

noncomputable def preferenceList (I : GloballyRanked K S T) (s : S) : List T :=
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  (Finset.univ : Finset T).sort (· ≤ ·)

/--
@isnad1 id=pairwise.0h5v.s6.3868eca30d3f from=translated src=- shape=18dcd106 vocab=cd4db943
-/
theorem preferenceList_pairwise (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).Pairwise fun t₁ t₂ => I.rank s t₁ ≤ I.rank s t₂ := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  exact Finset.pairwise_sort (Finset.univ : Finset T) (· ≤ ·)

/--
@isnad1 id=nodup.0h5v.s5.00e9d6521abf from=translated src=- shape=14490688 vocab=cdd99b83
-/
theorem preferenceList_nodup (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).Nodup := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  exact Finset.sort_nodup (Finset.univ : Finset T) (· ≤ ·)

/--
@isnad1 id=mem.0h6v.s5.c08873ca3bed from=translated src=- shape=c061067c vocab=68fd5712
-/
@[simp] theorem mem_preferenceList (I : GloballyRanked K S T) (s : S) (t : T) :
    t ∈ I.preferenceList s := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  have h : t ∈ (Finset.univ : Finset T).sort (α := T) (· ≤ ·) := by
    simp
  exact h

/--
@isnad1 id=eq.0h5v.s5.aef8d242fdef from=translated src=- shape=a77c9a54 vocab=3735e739
-/
@[simp] theorem length_preferenceList (I : GloballyRanked K S T) (s : S) :
    (I.preferenceList s).length = Fintype.card T := by
  letI : LinearOrder T := LinearOrder.lift' (I.rank s) (I.source_injective s)
  have h : ((Finset.univ : Finset T).sort (α := T) (· ≤ ·)).length = Fintype.card T := by
    simp
  exact h

/-- Incident keys occur in strictly increasing order in the generated
preference list.
@isnad1 id=lt.1h7v.s6.226eab257ffb from=translated src=- shape=c13a1b47 vocab=bdbbf21a
-/
theorem preferenceList_strict (I : GloballyRanked K S T) (s : S)
    {i j : Fin (I.preferenceList s).length} (hij : i < j) :
    I.rank s ((I.preferenceList s).get i) <
      I.rank s ((I.preferenceList s).get j) := by
  have hle := (I.preferenceList_pairwise s).rel_get_of_lt hij
  have htne : (I.preferenceList s).get i ≠ (I.preferenceList s).get j := by
    intro h
    exact (ne_of_lt hij) ((I.preferenceList_nodup s).injective_get h)
  apply lt_of_le_of_ne hle
  intro hrank
  exact htne (I.source_injective s hrank)

end GloballyRanked

end TunnellMap
