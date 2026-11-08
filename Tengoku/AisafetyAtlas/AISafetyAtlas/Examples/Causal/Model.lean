module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.Model

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A genuinely categorical causal model

This mirror example witnesses the non-binary surface of `AISafetyAtlas.Causal.Model`.
The root has three states, its binary child depends on that root, and the intervention
profile combines a ternary translation with a non-injective binary state map.
-/

namespace AISafetyAtlas.Examples.Causal.Model

open AISafetyAtlas.Causal

/-- A ternary root and a binary child.-/
@[expose] public def categoricalDim : Bool → ℕ
  | false => 3
  | true => 2

/-- The sole edge is from the ternary root to the binary child.-/
@[expose] public def categoricalParents : Bool → Finset Bool
  | false => ∅
  | true => {false}

/-- The child's probability of state one at each ternary parent state.-/
@[expose] public def childOne (x : Fin 3) : ℚ :=
  if x = 0 then 1 / 4 else if x = 1 then 1 / 2 else 3 / 4

/-- Full-simplex CPTs for the ternary-root, binary-child model.-/
@[expose] public def categoricalCpt :
    (c : Bool) → Fin (categoricalDim c) → Assignment Bool categoricalDim → ℚ
  | false, _, _ => 1 / 3
  | true, a, v => if a.val = 1 then childOne (v false) else 1 - childOne (v false)

private theorem childOne_bounds (x : Fin 3) : 0 ≤ childOne x ∧ childOne x ≤ 1 := by
  fin_cases x <;> norm_num [childOne]

/-- A non-binary model with a nontrivial parent-dependent CPT.-/
@[expose] public def categoricalModel :
    AISafetyAtlas.Causal.Model Bool categoricalDim ℚ where
  dim_pos := by intro c; cases c <;> decide
  parents := categoricalParents
  acyclic := ⟨fun c ↦ if c then 1 else 0, by decide⟩
  cpt := categoricalCpt
  cpt_parents := by
    intro c a v w h
    cases c
    · rfl
    · have hvw : v false = w false := h false (by simp [categoricalParents])
      simp only [categoricalCpt, hvw]
  cpt_nonneg := by
    intro c a v
    cases c
    · norm_num [categoricalCpt]
    · by_cases ha : a.val = 1
      · simp only [categoricalCpt, ite_eq_left ha]
        exact (childOne_bounds (v false)).1
      · simp only [categoricalCpt, ite_eq_right ha]
        linarith [(childOne_bounds (v false)).2]
  cpt_sum := by
    intro c v
    cases c
    · change (∑ _a : Fin 3, (1 / 3 : ℚ)) = 1
      norm_num [Fin.sum_univ_succ]
    · change (∑ a : Fin 2,
        if a.val = 1 then childOne (v false) else 1 - childOne (v false)) = 1
      rw [Fin.sum_univ_two]
      simp

/-- Translation by one modulo three.-/
@[expose] public def ternaryShift (a : Fin 3) : Fin 3 :=
  ⟨(a.val + 1) % 3, Nat.mod_lt _ (by decide)⟩

/-- Translate the ternary root and collapse both child states to zero.-/
@[expose] public def shiftCollapse : InterventionProfile Bool categoricalDim
  | false => ternaryShift
  | true => fun _ ↦ ⟨0, by simp [categoricalDim]⟩

/-- A state used to expose both intervention factors numerically.-/
@[expose] public def witness : Assignment Bool categoricalDim
  | false => ⟨2, by simp [categoricalDim]⟩
  | true => ⟨0, by simp [categoricalDim]⟩

end AISafetyAtlas.Examples.Causal.Model
