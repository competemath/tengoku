module

public import Tengoku

variable {α} (l l₁ l₂ : List α) (a : α)

public section

/--
@isnad1 id=eq.0h2v.s4.3b0a92ea60e4 from=translated src=- shape=a92ae804 vocab=1008a29d
-/
theorem Set.range_list_get_eq_toFinset_toSet [DecidableEq α] :
    Set.range l.get = l.toFinset := by
  simp

/--
@isnad1 id=eq.0h1v.s4.963333289b52 from=translated src=- shape=93b86a09 vocab=3afdb63c
-/
theorem Set.range_get_nil : Set.range ([] : List α).get = ∅ := by
  simp

/--
@isnad1 id=eq.0h2v.s4.fc7a82f2d57b from=translated src=- shape=05c59210 vocab=8fdfa3fb
-/
theorem Set.range_get_singleton : Set.range ([a] : List α).get = {a} := by
  simp

/--
@isnad1 id=eq.0h3v.s5.0853f80a9a7b from=translated src=- shape=22cebfb9 vocab=49daa295
-/
theorem Set.range_get_cons_list {a} : Set.range (a :: l).get = insert a (Set.range l.get) := by
  classical
  rw [Set.range_list_get_eq_toFinset_toSet, Set.range_list_get_eq_toFinset_toSet]
  simp

/--
@isnad1 id=eq.0h2v.s4.dc10ac6ebe5c from=translated src=- shape=64091962 vocab=d5b1f292
-/
theorem List.toFinset_singleton [DecidableEq α] : [a].toFinset = {a} := by
  rfl
