module

public import Tengoku.AisafetyAtlas.AISafetyAtlas.Conjectures.MAIS
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.BehavioralCollision
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.OneNodeClass
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Causal.Query
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Conjectures.MAIS.Common
public import Tengoku.AisafetyAtlas.AISafetyAtlas.Examples.Conjectures.MAIS.Rates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# MAIS-O25's antecedent is inhabited

`ExactClassAssumptions` has a witness, so the proposition is not vacuously true.
The witness is the one-node class: at one vertex only the edgeless graph exists,
so several clauses hold for reasons about the vertex set rather than about
identifiability.

Nothing here uses `sorry` or an added axiom.
-/

namespace AISafetyAtlas.Examples.Conjectures.MAIS

open AISafetyAtlas.Causal
open AISafetyAtlas.Conjectures.MAIS
open AISafetyAtlas.Examples.Causal

/-! ## MAIS-O25's antecedent is inhabited

`ExactClassAssumptions` is the antecedent of `maisO25_exactQueryRate`. Before the
theorem below, this tree exhibited no inhabitant, so its own non-vacuity evidence
was missing and the conjecture could have been vacuously true.
`Examples.Causal.OneNodeClass` supplies one: a single binary chance variable, no
observations, a utility gap straddling zero, and the full margin class over it.

**What this settles and what it does not.** It settles that the antecedent is
nonempty, which is the vacuity question. It does not settle that the antecedent
is *selective* — several of the eight clauses hold here for reasons about the
vertex set rather than about the class, since one vertex admits only the edgeless
graph. `conjectures.yaml` records both halves at CONJ-006. -/

/-- **Clause 3 at one vertex.** `def:margin` defines `K` as the maximum of `K(G)`
over the class; every member carries the edgeless graph, so the maximum is `1`
and is attained rather than merely bounded.-/
public theorem oneNode_isClassChartDim :
    IsClassChartDim OneNodeClass.sk OneNodeClass.lam 1 := by
  constructor
  · exact ⟨OneNodeClass.model (1 / 2) (by norm_num) (by norm_num),
      OneNodeClass.model_marginClass (by norm_num) (by norm_num)
        (by norm_num [OneNodeClass.lam]) (by norm_num [OneNodeClass.lam]),
      by rw [OneNodeClass.parents_eq_edgeless, OneNodeClass.chartDim_edgeless]⟩
  · rintro k ⟨M, -, rfl⟩
    rw [OneNodeClass.parents_eq_edgeless, OneNodeClass.chartDim_edgeless]

/-- **MAIS-O25's antecedent has an inhabitant.** All eight clauses, on the
one-node margin class, with `K = 1`, `L = 10`, `ρ = 1 - 2λ` and `δmax = 1`.-/
public theorem oneNode_exactClassAssumptions :
    ExactClassAssumptions OneNodeClass.sk
      {M | OneNodeClass.sk.MarginClass M OneNodeClass.lam}
      OneNodeClass.lam 1 10 (1 - 2 * OneNodeClass.lam) 1 :=
  ⟨OneNodeClass.lam_valid, by norm_num, oneNode_isClassChartDim, fun _ hM ↦ hM,
    OneNodeClass.isCompactSemialgebraicClass,
    fun _ _ _ _ h ↦ OneNodeClass.behaviorEq_injective h,
    ⟨by norm_num, fun _ hδ _ _ _ _ hid ↦ OneNodeClass.modelError_le_ten_mul hδ hid⟩,
    OneNodeClass.containsChartBox⟩

end AISafetyAtlas.Examples.Conjectures.MAIS
