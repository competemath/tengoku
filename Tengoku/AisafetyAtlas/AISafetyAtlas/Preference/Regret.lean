module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Preference
public import Tengoku.Seed.Data.Real.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Half-maximal regret is not ruled out by observation (source §4.1.2)

Armstrong and Mindermann combine their planner/reward unidentifiability theorem
with Everitt et al.'s corrupted-reward no-free-lunch bound.  This module keeps
the two ingredients separate: `RegretModel` records attained maxima, while
`HalfMaximalRegretBound` is an explicit certificate proved by
`AISafetyAtlas.Wireheading.Corruption.ComplementedClass.everitt_theorem_eleven`.

The result is abstract over reward/environment and behaviour types.  It builds
no MDP and asserts nothing about a deployed system.

Survey row: **BY-011**; the certificate belongs to **BY-039**.
-/

namespace AISafetyAtlas.Preference

/-- An abstract regret model with genuine, attained worst-case maxima.-/
public structure RegretModel (Reward Behaviour : Type*) where
  /-- Regret of a behaviour in an environment/reward hypothesis.-/
  regret : Reward → Behaviour → ℝ
  /-- Maximum regret over the environment class.-/
  worstCaseRegret : Behaviour → ℝ
  /-- Every environment's regret is bounded by `worstCaseRegret`.-/
  worstCaseRegret_upper :
    ∀ R : Reward, ∀ π : Behaviour, regret R π ≤ worstCaseRegret π
  /-- The maximum is attained.-/
  worstCaseRegret_attained :
    ∀ π : Behaviour, ∃ R : Reward, worstCaseRegret π = regret R π
  /-- A behaviour with maximal worst-case regret.-/
  worstPolicy : Behaviour
  /-- `worstPolicy` is worst.-/
  worstPolicy_worst :
    ∀ π : Behaviour, worstCaseRegret π ≤ worstCaseRegret worstPolicy

/--
An explicit certificate for the Everitt et al. (IJCAI 2017) Theorem 11
conclusion.  Keeping this separate prevents the BY-011 bridge from silently
assuming BY-039.-/
public structure HalfMaximalRegretBound {Reward Behaviour : Type*}
    (M : RegretModel Reward Behaviour) : Prop where
  bound :
    ∀ π : Behaviour,
      M.worstCaseRegret M.worstPolicy / 2 ≤ M.worstCaseRegret π

namespace RegretModel

variable {Reward Behaviour : Type*} (M : RegretModel Reward Behaviour)

end RegretModel
end AISafetyAtlas.Preference
