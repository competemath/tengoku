import Tengoku.Erdos278.Erdos278.AsymptoticDensity
import Tengoku.Erdos278.Erdos278.Maximization
import Tengoku.Erdos278.Erdos278.Towers

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos278

open Finset

def exampleModuli : Fin 3 → ℕ := ![2, 6, 10]
def exampleResidues : Fin 3 → ℤ := ![0, 1, 1]

/--
@isnad1 id=lt.0h1v.s4.51937a168f02 from=translated src=- shape=dfc00b87 vocab=30fba7ad
-/
theorem example_moduli_positive (i : Fin 3) : 0 < exampleModuli i := by
  fin_cases i <;> decide

/--
@isnad1 id=eq.0h1v.s5.7f867581da5c from=translated src=- shape=e81ce265 vocab=0c666e0c
-/
theorem example_interaction (i : Fin 3) : interactionModulus exampleModuli i = 2 := by
  fin_cases i <;> decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/--
@isnad1 id=eq.0h0v.s5.e0abd4116be7 from=translated src=- shape=a800cc78 vocab=a1213e52
-/
theorem example_density : density univ exampleModuli exampleResidues = 11 / 15 := by
  rw [density, ← count_coveredNat_period]
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/--
@isnad1 id=le.0h1v.s6.dfd888c4be1f from=translated src=- shape=285c27f2 vocab=46b6efbb
-/
theorem example_compressed_bound (a : Fin 3 → Fin 2) :
    density univ exampleModuli (fun i => (a i : ℤ)) ≤ 11 / 15 := by
  rw [density, ← count_coveredNat_period]
  revert a
  decide +kernel

/-- An all-integer, global optimality theorem for the former root counterexample.
The finite check above is proved by kernel reduction (`decide`), not native_decide.
@isnad1 id=and.0h0v.s6.68d073f7501d from=translated src=- shape=31c811f9 vocab=a4465060
-/
theorem example_global_maximum :
    density univ exampleModuli exampleResidues = 11 / 15 ∧
      ∀ a : Fin 3 → ℤ, density univ exampleModuli a ≤ 11 / 15 := by
  refine ⟨example_density, fun a => ?_⟩
  obtain ⟨b, hb⟩ := canonical_representatives (fun _ : Fin 3 => 2) (by decide) a
  have heq : density univ exampleModuli (fun i => (b i : ℤ)) =
      density univ exampleModuli a := by
    apply density_eq_of_compatible univ exampleModuli
      (fun i _ => example_moduli_positive i)
    apply interaction_compression
    intro i
    rw [example_interaction, hb i]
    exact Int.mod_modEq _ _
  rw [← heq]
  exact example_compressed_bound b

/-- The impossible graph would predict 23/30 if all intersections were discarded.
@isnad1 id=and.0h0v.s6.2581a6af54ae from=translated src=- shape=903c21ab vocab=9c632427
-/
theorem impossible_empty_graph_value :
    (1 : ℚ)/2 + 1/6 + 1/10 = 23/30 ∧ (11 : ℚ)/15 < 23/30 := by norm_num

end Erdos278
