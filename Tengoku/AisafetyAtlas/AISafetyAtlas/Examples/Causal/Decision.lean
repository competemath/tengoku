module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.Decision
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.BehavioralCollision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A non-vacuous decision example

The behavioral-collision example supplies two models whose transforms agree.
This companion supplies the opposite check required by the decision layer:
the identified-set relation is not universal. A second edgeless model has
`P(X=1) = P(Y=1) = 4/5`, so its no-intervention transform has the opposite
sign from the original model's. At zero regret no common policy can serve
both models.
-/

namespace AISafetyAtlas.Examples.Causal

open AISafetyAtlas.Causal

local notation:max "Model" C:arg =>
  AISafetyAtlas.Causal.Model C (binaryDim C) ℚ
local notation:max "InterventionProfile" C:arg =>
  AISafetyAtlas.Causal.InterventionProfile C (binaryDim C)
local notation:max "Mixture" C:arg =>
  AISafetyAtlas.Causal.Mixture C (binaryDim C) ℚ
local notation:max "ProbMixture" C:arg =>
  AISafetyAtlas.Causal.ProbMixture C (binaryDim C) ℚ

/-! ## Transform equality gives shared optimal behavior -/

/-! ## Fibre-indexing regression

At `C = Fin 2` and `visible = ∅` there is one visible fibre. Summing `Δmask`
over all four assignments would count it four times; the representative image
must stay a singleton.
-/

/-! ## A second margin-class model -/

/-- The edgeless high-corner model, with both marginal probabilities `4/5`.-/
@[expose] public def high : Model (Fin 2) where
  dim_pos := by intro c; simp [binaryDim]
  parents := fun _ => ∅
  acyclic := ⟨fun _ => 0, by intro c p hp; simp at hp⟩
  cpt := fun _ a _ ↦ bernoulli (4/5) a
  cpt_parents := by intro c a v w _; rfl
  cpt_nonneg := by intro c a v; fin_cases a <;> norm_num [bernoulli]
  cpt_sum := by intro c v; rw [Fin.sum_univ_two]; norm_num [bernoulli]

/-! ## A point-mass probability mixture -/

/-- The intervention profile that leaves both variables untouched.-/
@[expose] public def identityProfile : InterventionProfile (Fin 2) :=
  fun _ => LocalIntervention.identity

/-- A probability mixture concentrated on `identityProfile`.-/
@[expose] public def identityMixture : Mixture (Fin 2) :=
  fun σ => if σ = identityProfile then 1 else 0

/-- The point mass on the identity profile is a probability mixture.-/
public theorem identityMixture_isProbability : IsProbabilityMixture identityMixture := by
  classical
  constructor
  · intro σ
    simp only [identityMixture]
    split_ifs <;> norm_num
  · simp only [identityMixture]
    rw [Finset.sum_ite_eq']
    simp

/-- The point-mass mixture packaged for the decision layer.-/
@[expose] public def identityProbMixture : ProbMixture (Fin 2) :=
  ⟨identityMixture, identityMixture_isProbability⟩

/-! ## Opposite signs -/

/-! ## Normalization outside the binary case

`realizable_iff` is a two-point statement and cannot say anything about a task
with three or more decisions. `realizable_iff_general` can, and this is a worked
instance in exactly that region: a three-decision family on the collision's
chart, whose fibrewise spread is `3/4` and which is therefore realized by a
normalized utility. RE24 Appendix A.2 equation (2) normalizes at this arity; the
binary lemma has no statement here at all. -/

/-- A three-decision family on the two-variable chart.-/
@[expose] public def ternaryGap : Fin 3 → Assignment (Fin 2) (binaryDim (Fin 2)) → ℚ :=
  fun d _ ↦ ![0, 1/2, 3/4] d

end AISafetyAtlas.Examples.Causal
