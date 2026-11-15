import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @IsGL2RealKTypeModule` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#check @IsGL2RealKTypeSubmodule` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#check @IsIrreducibleGL2RealKTypeModule` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AutomorphicForm.isGL2RealKTypeSubmodule_bot` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AutomorphicForm.isGL2RealKTypeSubmodule_top` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AutomorphicForm.not_isIrreducibleGL2RealKTypeModule_of_subsingleton` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AutomorphicForm.IsGL2RealKTypeModule.refl_comp_lower` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms AutomorphicForm.IsGL2RealKTypeModule.refl_refl` (it only prints; the queue checks the axioms of every declaration). -/

set_option autoImplicit false

namespace AutomorphicForm

variable {M : Type*} [AddCommGroup M] [Module ℂ M]

structure IsGL2RealKTypeModule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) : Prop where
  isInternal : DirectSum.IsInternal wt
  map_raise_le : ∀ n : ℤ, (wt n).map E ≤ wt (n + 2)
  map_lower_le : ∀ n : ℤ, (wt n).map L ≤ wt (n - 2)
  raise_lower_sub : ∀ (n : ℤ) (v : M), v ∈ wt n → E (L v) - L (E v) = (n : ℂ) • v
  map_refl_le : ∀ n : ℤ, (wt n).map ε ≤ wt (-n)
  refl_comp_refl : ε ∘ₗ ε = LinearMap.id
  refl_comp_raise : ε ∘ₗ E = L ∘ₗ ε

def IsGL2RealKTypeSubmodule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M)
    (W : Submodule ℂ M) : Prop :=
  W ≤ (⨆ n : ℤ, W ⊓ wt n) ∧ W.map E ≤ W ∧ W.map L ≤ W ∧ W.map ε ≤ W

def IsIrreducibleGL2RealKTypeModule (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) : Prop :=
  (∃ v : M, v ≠ 0) ∧
    ∀ W : Submodule ℂ M, IsGL2RealKTypeSubmodule wt E L ε W → W = ⊥ ∨ W = ⊤

/--
@isnad1 id=iff.0h6v.s8.9af02e55b1fd from=translated src=- shape=a59e24c9 vocab=19af8e06
-/
theorem isGL2RealKTypeSubmodule_iff (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M)
    (W : Submodule ℂ M) :
    IsGL2RealKTypeSubmodule wt E L ε W ↔
      W ≤ (⨆ n : ℤ, W ⊓ wt n) ∧ W.map E ≤ W ∧ W.map L ≤ W ∧ W.map ε ≤ W :=
  Iff.rfl

/--
@isnad1 id=iff.0h5v.s7.eb6242027c8e from=translated src=- shape=6c9a9338 vocab=0d8399f0
-/
theorem isIrreducibleGL2RealKTypeModule_iff (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) :
    IsIrreducibleGL2RealKTypeModule wt E L ε ↔
      (∃ v : M, v ≠ 0) ∧
        ∀ W : Submodule ℂ M, IsGL2RealKTypeSubmodule wt E L ε W → W = ⊥ ∨ W = ⊤ :=
  Iff.rfl

/--
@isnad1 id=isgl2rea.0h5v.s6.87bcfcd309e3 from=translated src=- shape=e9fc2815 vocab=a2b1e9d4
-/
theorem isGL2RealKTypeSubmodule_bot (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) :
    IsGL2RealKTypeSubmodule wt E L ε ⊥ := by
  refine ⟨bot_le, ?_, ?_, ?_⟩ <;> simp

/--
@isnad1 id=isgl2rea.1h5v.s6.8120db3e3458 from=translated src=- shape=73737aac vocab=ce949603
-/
theorem isGL2RealKTypeSubmodule_top {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) : IsGL2RealKTypeSubmodule wt E L ε ⊤ := by
  refine ⟨?_, le_top, le_top, le_top⟩
  have htop : (⨆ n : ℤ, wt n) = ⊤ := h.isInternal.submodule_iSup_eq_top
  simp only [top_inf_eq]
  rw [htop]

/--
@isnad1 id=not.0h5v.s6.0ffabeb63182 from=translated src=- shape=2d0c7702 vocab=9e67dab1
-/
theorem not_isIrreducibleGL2RealKTypeModule_of_subsingleton [Subsingleton M]
    (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M) :
    ¬ IsIrreducibleGL2RealKTypeModule wt E L ε := fun h => by
  obtain ⟨⟨v, hv⟩, -⟩ := h
  exact hv (Subsingleton.elim v 0)

/--
@isnad1 id=eq.1h5v.s7.2e7ad4e1dcbe from=translated src=- shape=ae91b0f4 vocab=d83d372c
-/
theorem IsGL2RealKTypeModule.refl_comp_lower {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) : ε ∘ₗ L = E ∘ₗ ε := by
  have hεε : ∀ v : M, ε (ε v) = v := fun v => by
    simpa using LinearMap.congr_fun h.refl_comp_refl v
  have hεE : ∀ v : M, ε (E v) = L (ε v) := fun v => by
    simpa using LinearMap.congr_fun h.refl_comp_raise v
  ext v
  simp only [LinearMap.coe_comp, Function.comp_apply]
  have := hεE (ε v)
  rw [hεε] at this
  rw [← this, hεε]

/--
@isnad1 id=eq.1h6v.s7.68a145eb3cb4 from=translated src=- shape=33431af9 vocab=694dd015
-/
theorem IsGL2RealKTypeModule.refl_refl {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) (v : M) : ε (ε v) = v := by
  have := LinearMap.congr_fun h.refl_comp_refl v
  simpa using this

/--
@isnad1 id=mem.2h7v.s7.53f7d712efe1 from=translated src=- shape=f0528f28 vocab=af482992
-/
theorem IsGL2RealKTypeModule.raise_mem {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) {n : ℤ} {v : M} (hv : v ∈ wt n) : E v ∈ wt (n + 2) :=
  h.map_raise_le n (Submodule.mem_map_of_mem hv)

/--
@isnad1 id=mem.2h7v.s7.48433107d3c8 from=translated src=- shape=1a172484 vocab=a73cd997
-/
theorem IsGL2RealKTypeModule.lower_mem {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) {n : ℤ} {v : M} (hv : v ∈ wt n) : L v ∈ wt (n - 2) :=
  h.map_lower_le n (Submodule.mem_map_of_mem hv)

/--
@isnad1 id=mem.2h7v.s7.a3ca2e95d83f from=translated src=- shape=565e0559 vocab=5b8b8d6f
-/
theorem IsGL2RealKTypeModule.refl_mem {wt : ℤ → Submodule ℂ M} {E L ε : M →ₗ[ℂ] M}
    (h : IsGL2RealKTypeModule wt E L ε) {n : ℤ} {v : M} (hv : v ∈ wt n) : ε v ∈ wt (-n) :=
  h.map_refl_le n (Submodule.mem_map_of_mem hv)

end AutomorphicForm

section Battery
open AutomorphicForm
end Battery
