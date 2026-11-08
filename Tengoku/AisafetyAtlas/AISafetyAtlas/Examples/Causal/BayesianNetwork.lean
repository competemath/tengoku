module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.BayesianNetwork
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.BehavioralCollision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Worked model of Pearl's Definition 1.3.1

`AISafetyAtlas.Causal.BayesianNetwork` renders Definition 1.3.1 as a condition on
a family of interventional distributions. Two things about that rendering are
easy to assert and easy to get wrong, and this module checks both.

* **The kernel really is an instance.** `Model.isCausalBayesNetwork` says every
  atlas model presents a compatible family; `edgeless_isCausalBayesNetwork` runs
  it on a checked model rather than leaving it general.
* **Condition (iii) has teeth.** The invariance clause is the one that ties the
  members of the family together, and a rendering where each member carried its
  own private factorization would constrain nothing. `badFamily` is the witness:
  each of its two exhibited members *is* a truncated product — so conditions (i)
  and (ii) hold of them — and yet no single mechanism family works for both, so
  the family is not a causal Bayesian network.
-/

namespace AISafetyAtlas.Examples.Causal.BayesianNetwork

open AISafetyAtlas.Causal

/-! ## The kernel is an instance -/

/-! ## Condition (iii) has teeth

The graph below is the one-edge shape `0 → 1`. Two mechanism families live over
it: `uniformTables`, where every table is `1/2`, and `skewTables`, which differs
only in the child's mechanism. -/

/-- The one-edge graph `0 → 1`.-/
@[expose] public def G2 : Fin 2 → Finset (Fin 2) :=
  fun c ↦ if c = 1 then {0} else ∅

/-- Every mechanism uniform.-/
@[expose] public noncomputable def uniformTables :
    ConditionalTables (Fin 2) (binaryDim (Fin 2)) ℝ G2 where
  table := fun _ _ _ ↦ 1 / 2
  reads_parents := by intro c a v w _; rfl
  nonneg := by intro c a v; norm_num
  sum_one := by intro c v; norm_num

/-- The same root mechanism, a different child mechanism.-/
@[expose] public noncomputable def skewTables :
    ConditionalTables (Fin 2) (binaryDim (Fin 2)) ℝ G2 where
  table := fun c a _ ↦ if c = 1 then (if a = 0 then 1 / 4 else 3 / 4) else 1 / 2
  reads_parents := by intro c a v w _; rfl
  nonneg := by
    intro c a v
    by_cases hc : c = 1 <;> by_cases ha : a = 0 <;> norm_num [hc, ha]
  sum_one := by
    intro c v
    by_cases hc : c = 1 <;> norm_num [hc, Fin.sum_univ_two]

/-- **A family whose members are truncated products, but not all of the same
mechanisms.** The observational member uses `uniformTables`; every interventional
member uses `skewTables`.-/
@[expose] public noncomputable def badFamily :
    InterventionalFamily (Fin 2) (binaryDim (Fin 2)) ℝ :=
  fun targets target v ↦
    if targets = ∅ then uniformTables.family ∅ target v
    else skewTables.family targets target v

end AISafetyAtlas.Examples.Causal.BayesianNetwork
