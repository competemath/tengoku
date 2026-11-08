module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Causal.StructuralModel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A worked structural causal model, a worked diagram, and a material observation

`AISafetyAtlas.Causal.StructuralModel` renders Definitions 1–5 of Everitt et al.
2021. This module runs them on objects small enough to check by hand, and gives
the clauses that are stated rather than derived their teeth: that evaluation
really is print's recursion, that *"utility nodes have no children"* is a
condition a graph can fail, and that materiality is a condition an observation
can meet — with the deleted information link shown to be what does the work.
-/

namespace AISafetyAtlas.Examples.Causal.StructuralModel

open AISafetyAtlas.Causal

/-! ## A two-variable structural causal model

`A` is a fair bit copied from its own exogenous variable; `B` copies `A`. So `B`
is determined by `A`'s noise alone, through one level of recursion. -/

public abbrev Two := Fin 2

public abbrev bits : Two → ℕ := fun _ ↦ 2

/-- `A = ε_A`, and `B = A`.-/
public noncomputable def copyChain : SCM Two bits bits where
  dom_pos := fun _ ↦ by norm_num
  parents := fun v ↦ if v = 1 then {0} else ∅
  acyclic := acyclic_of_rank (fun v ↦ if v = 1 then 1 else 0) (by
    intro v p hp; fin_cases v <;> simp_all)
  f := fun v a e ↦ if v = 1 then a 0 else e
  f_parents := fun v a b e h ↦ by
    by_cases hv : v = 1
    · simp only [ite_eq_left hv]
      exact h 0 (by simp [hv])
    · simp [hv]
  exoProb := fun _ _ ↦ 1 / 2
  exoProb_nonneg := fun _ _ ↦ by norm_num
  exoProb_sum := fun _ ↦ by rw [Fin.sum_univ_two]; norm_num

/-! ## Intervening

`do(A = 1)` forces the root, and `B` follows it. -/

/-! ## The diagram, and the clause that is stated rather than derived -/

/-- One structure node, one decision, one utility. The decision observes the
structure node; the utility reads the decision.-/
public noncomputable def tinyCID : CID (Fin 3) where
  parents := fun v ↦ if v = 1 then {0} else if v = 2 then {1} else ∅
  acyclic := acyclic_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; fin_cases v <;> simp_all)
  kind := fun v ↦
    if v = 1 then NodeKind.decision
    else if v = 2 then NodeKind.utility
    else NodeKind.structureNode
  utility_childless := by
    intro u hu v hv; fin_cases u <;> fin_cases v <;> simp_all

/-! ## A worked SCIM, and an observation that is material

Print's Figure 2a in miniature: posts `D` influence clicks `U`, and the user's
opinion `O` is what makes the choice of post worth conditioning on. Here `O` is
a fair coin, `D` observes it, and the click happens exactly when the post
matches the opinion.

The point of the example is Definition 5. Copying `O` earns `1`; with the
information link `O → D` removed a policy cannot see the coin and earns `1/2`
whatever it does. So `O` is **material**, and `IsMaterial` is a condition some
observation actually meets rather than a definition nothing satisfies.

`E^D` and `E^U` are one-element here, so the policies are the deterministic
ones. That is an instance of Definition 4, not a restriction of it — print's
`E^D` *"provides randomness to allow the policy to be a stochastic function"*,
and a model may decline to use it. -/

/-- Three binary variables: opinion, post, click.-/
public abbrev figDim : Fin 3 → ℕ := fun _ ↦ 2

/-- Only the opinion is random.-/
public abbrev figExo : Fin 3 → ℕ := fun v ↦ if v = 0 then 2 else 1

/-- `O → D`, and both into `U`.-/
public noncomputable def figCID : CID (Fin 3) where
  parents := fun v ↦ if v = 1 then {0} else if v = 2 then {0, 1} else ∅
  acyclic := acyclic_of_rank (fun v ↦ (v : ℕ)) (by
    intro v p hp; fin_cases v <;> fin_cases p <;> simp_all)
  kind := fun v ↦
    if v = 1 then NodeKind.decision
    else if v = 2 then NodeKind.utility
    else NodeKind.structureNode
  utility_childless := by
    intro u hu v hv; fin_cases u <;> fin_cases v <;> simp_all

public theorem figCID_decisions : figCID.decisions = {1} := by decide

public theorem figCID_parents_decision : figCID.parents 1 = {0} := by
  simp [figCID]

/-- The opinion node copies its own noise; the click fires when post and opinion
agree. The post has no structural function until a policy supplies one, which is
Definition 4's whole asymmetry.-/
@[expose] public def figF (v : Fin 3) (a : Assignment (Fin 3) figDim)
    (e : Fin (figExo v)) : Fin (figDim v) :=
  if v = 0 then ⟨e.val % 2, Nat.mod_lt _ (by norm_num)⟩
  else if a 0 = a 1 then 1 else 0

/-- The SCIM of Figure 2a.-/
@[expose] public noncomputable def figSCIM : SCIM (Fin 3) figDim figExo where
  dom_pos := by decide
  graph := figCID
  utilityValue := fun _ _ i ↦ (i : ℝ)
  utilityValue_injective := by
    intro _ _ i j h
    have hc : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := h
    exact Fin.ext (Nat.cast_injective hc)
  f := fun v _ ↦ figF v
  f_parents := by
    intro v hv a b e hab
    fin_cases v
    · simp [figF]
    · exact absurd (by decide) hv
    · have ha0 : a 0 = b 0 := hab 0 (by simp [figCID])
      have ha1 : a 1 = b 1 := hab 1 (by simp [figCID])
      simp [figF, ha0, ha1]
  exoProb := fun v _ ↦ if v = 0 then 1 / 2 else 1
  exoProb_nonneg := by
    intro v e
    by_cases h : v = 0 <;> simp [h]
  exoProb_sum := by
    intro v
    by_cases h : v = 0 <;> simp [h]

@[simp] public theorem figSCIM_graph : figSCIM.graph = figCID := rfl

@[simp] public theorem figSCIM_utilityValue (u : Fin 3)
    (hu : figSCIM.graph.IsUtility u) (i : Fin (figDim u)) :
    figSCIM.utilityValue u hu i = (i : ℝ) := rfl

/-! ### Evaluating a policy -/

public theorem figSCIM_mem_decisions_one : figCID.IsDecision (1 : Fin 3) := by
  decide

/-! ### The optimum, and what it is worth -/

/-- Copying the opinion.-/
public noncomputable def figCopy : figSCIM.Policy :=
  ⟨fun _ a _ ↦ a 0, by
    intro d a b _ hab
    have hd : (d : Fin 3) = 1 :=
      Finset.mem_singleton.mp (by
        rw [← figCID_decisions]
        exact (figSCIM.graph.mem_decisions_iff d.1).mpr d.2)
    exact hab 0 (by simp [figSCIM_graph, hd, figCID_parents_decision])⟩

/-! ### Removing the information link

`M_{O↛D}`. The graph loses the edge `O → D` and nothing else changes, so a
policy's congruence clause is now over the empty parent set: it must ignore the
opinion. Every such policy earns exactly `1/2`. -/

@[expose] public noncomputable def figCut : SCIM (Fin 3) figDim figExo :=
  figSCIM.removeInfoLink figSCIM_mem_decisions_one 0

public theorem figCut_mem_decisions_one : figCut.graph.IsDecision (1 : Fin 3) :=
  figSCIM_mem_decisions_one

/-- The post the policy settles on, independent of `ε` and of the opinion.-/
@[expose] public noncomputable def figCutChoice (π : figCut.Policy) : Fin 2 :=
  π.1 ⟨1, figCut_mem_decisions_one⟩ (fun _ ↦ 0) 0

@[simp] public theorem figCut_utilityValue (u : Fin 3)
    (hu : figCut.graph.IsUtility u) (i : Fin (figDim u)) :
    figCut.utilityValue u hu i = (i : ℝ) := rfl

end AISafetyAtlas.Examples.Causal.StructuralModel
