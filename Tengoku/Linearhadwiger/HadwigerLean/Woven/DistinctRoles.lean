import Tengoku.Linearhadwiger.HadwigerLean.Woven.BranchPairPath

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Woven solutions from a rooted clique model with distinct roles

When all root and terminal roles have distinct vertices, a rooted clique
model at those vertices directly supplies a woven solution: retain the root
branches and connect each terminal pair through its two branches.
-/

namespace HadwigerLean

universe v

namespace RootedMinorModel

variable {V : Type v} {G : SimpleGraph V} {n a j : ℕ}
  {role : Fin n → V}

/-- Restrict a rooted clique model to injectively selected branches.-/
def selectClique (M : RootedMinorModel (SimpleGraph.completeGraph (Fin n)) G role)
    (f : Fin a ↪ Fin n) :
    RootedMinorModel (SimpleGraph.completeGraph (Fin a)) G (role ∘ f) where
  branch := fun i => M.branch (f i)
  connected := fun i => M.connected (f i)
  disjoint := by
    intro i k hik
    exact M.disjoint (f.injective.ne hik)
  adjacent := by
    intro i k hik
    exact M.adjacent (f.injective.ne hik)
  root_mem := fun i => M.root_mem (f i)

end RootedMinorModel

namespace Woven

variable {V : Type v} {G : SimpleGraph V} {n a j : ℕ}
  {role : Fin n → V}

/-- Role slots for roots and the two ends of each terminal pair.-/
abbrev DistinctRoleIndex (a j : ℕ) := Fin a ⊕ (Fin j ⊕ Fin j)

/-- Enumerate exactly one slot per root and two slots per terminal pair.-/
noncomputable def distinctRoleEquiv (a j : ℕ) :
    DistinctRoleIndex a j ≃ Fin (a + 2 * j) :=
  Fintype.equivOfCardEq (by simp [DistinctRoleIndex]; omega)

/-- Assign the original vertex to each root or terminal role slot.-/
def originalRole (root : Fin a → V) (P : IndexedPairs (Fin j) V) :
    DistinctRoleIndex a j → V
  | Sum.inl i => root i
  | Sum.inr (Sum.inl i) => P.start i
  | Sum.inr (Sum.inr i) => P.finish i
/-- The root role selected by a global injection of role slots.-/
def selectedRoots (f : DistinctRoleIndex a j ↪ Fin n) (role : Fin n → V) :
    Fin a → V := fun i => role (f (Sum.inl i))

/-- The pair roles selected by a global injection of role slots.-/
def selectedPairs (f : DistinctRoleIndex a j ↪ Fin n) (role : Fin n → V) :
    IndexedPairs (Fin j) V where
  start := fun i => role (f (Sum.inr (Sum.inl i)))
  finish := fun i => role (f (Sum.inr (Sum.inr i)))

/-- Distinct proxy role slots keep proxy roots disjoint from proxy
terminal vertices.-/
theorem selectedRoles_disjoint
    (f : DistinctRoleIndex a j ↪ Fin n) (role : Fin n → V)
    (hrole : Function.Injective role) :
    Disjoint (Set.range (selectedRoots f role))
      (selectedPairs f role).allTerminals := by
  apply Set.disjoint_left.mpr
  intro x hxroot hxterm
  rcases hxroot with ⟨i, rfl⟩
  rcases Set.mem_iUnion.mp hxterm with ⟨k, hk⟩
  rcases hk with hs | ht
  · have heq : f (Sum.inl i) = f (Sum.inr (Sum.inl k)) :=
      hrole (by simpa [selectedRoots, selectedPairs] using hs)
    simpa using (f.injective heq)
  · have heq : f (Sum.inl i) = f (Sum.inr (Sum.inr k)) :=
      hrole (by simpa [selectedRoots, selectedPairs] using ht)
    simpa using (f.injective heq)

end Woven

end HadwigerLean
