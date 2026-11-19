import Tengoku.Linearhadwiger.HadwigerLean.Inseparability.Stages
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Use the unique region tangencies as the roots of a stage

The stage invariant records a rooted model and a unique tangency for each
branch. Re-rooting each branch at its tangency aligns the two roles without
changing any branch set, core, or region.
-/

namespace HadwigerLean
namespace Inseparability

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {s k m coreBound : ℕ}

noncomputable def StageState.tangentRoot
    (S : StageState G s k m coreBound) (i : Fin s) : V :=
  (S.tangent i).choose

/--
@isnad1 id=mem.0h8v.s6.815e818b4d02 from=translated src=- shape=decaab09 vocab=f7317fc3
-/
theorem StageState.tangentRoot_mem_branch
    (S : StageState G s k m coreBound) (i : Fin s) :
    S.tangentRoot i ∈ S.model.branch i :=
  (S.tangent i).choose_spec.1.1

/--
@isnad1 id=mem.0h8v.s5.cb2b1665188b from=translated src=- shape=bcf41e0a vocab=5f85ed89
-/
theorem StageState.tangentRoot_mem_region
    (S : StageState G s k m coreBound) (i : Fin s) :
    S.tangentRoot i ∈ S.region :=
  (S.tangent i).choose_spec.1.2

/--
@isnad1 id=mem.0h8v.s5.3a48b09e48ce from=translated src=- shape=bcf41e0a vocab=e732c565
-/
theorem StageState.tangentRoot_mem_core
    (S : StageState G s k m coreBound) (i : Fin s) :
    S.tangentRoot i ∈ S.core :=
  S.intersection_in_core
    ⟨Set.mem_iUnion.mpr ⟨i,S.tangentRoot_mem_branch i⟩,
      S.tangentRoot_mem_region i⟩

/--
@isnad1 id=injectiv.0h7v.s5.4f4b621eb1b6 from=translated src=- shape=d12c7664 vocab=7c1e4698
-/
theorem StageState.tangentRoot_injective
    (S : StageState G s k m coreBound) :
    Function.Injective S.tangentRoot := by
  intro i j heq
  by_contra hij
  exact (Set.disjoint_left.mp (S.model.disjoint hij))
    (S.tangentRoot_mem_branch i)
    (heq ▸ S.tangentRoot_mem_branch j)

/-- Re-root a stage model at its actual tangency vertices. The model's
branches and all budgets are unchanged.-/
noncomputable def StageState.normalizeRoots
    (S : StageState G s k m coreBound) :
    StageState G s k m coreBound where
  root := S.tangentRoot
  root_injective := S.tangentRoot_injective
  model := {
    toMinorModel := S.model.toMinorModel
    root_mem := S.tangentRoot_mem_branch
  }
  core := S.core
  region := S.region
  region_connected := S.region_connected
  chromatic_reserve := S.chromatic_reserve
  core_card_le := S.core_card_le
  tangent := S.tangent
  intersection_in_core := S.intersection_in_core
  core_witness := S.core_witness

/--
@isnad1 id=mem.0h8v.s6.1ff6eda8c0ae from=translated src=- shape=0b75190c vocab=daa03833
-/
theorem StageState.normalizeRoots_root_in_core
    (S : StageState G s k m coreBound) (i : Fin s) :
    S.normalizeRoots.root i ∈ S.normalizeRoots.core :=
  S.tangentRoot_mem_core i

/--
@isnad1 id=mem.0h8v.s6.97ad82529525 from=translated src=- shape=0b75190c vocab=c6396b35
-/
theorem StageState.normalizeRoots_root_in_region
    (S : StageState G s k m coreBound) (i : Fin s) :
    S.normalizeRoots.root i ∈ S.normalizeRoots.region :=
  S.tangentRoot_mem_region i

end Inseparability
end HadwigerLean
