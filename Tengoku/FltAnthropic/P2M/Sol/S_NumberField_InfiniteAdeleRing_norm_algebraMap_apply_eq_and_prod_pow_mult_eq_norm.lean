import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfiniteAdeleRing_norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_InfiniteAdeleRing_norm_algebraMap_apply_eq_and_prod_pow_mult_eq_norm

set_option autoImplicit false

open NumberField

/--
@isnad1 id=and.0h2v.s8.3d4762742027 from=translated src=- shape=47c43b14 vocab=83cce637
-/
theorem solution
    (K : Type) [Field K] [NumberField K] (x : K) :
    (∀ v : InfinitePlace K, ‖algebraMap K (InfiniteAdeleRing K) x v‖ = v x) ∧
    ∏ v : InfinitePlace K, v x ^ v.mult = ‖algebraMap K (InfiniteAdeleRing K) x‖ := by
  have h : ∀ v : InfinitePlace K, ‖algebraMap K (InfiniteAdeleRing K) x v‖ = v x := by
    intro v
    rw [NumberField.InfiniteAdeleRing.algebraMap_apply]
    exact UniformSpace.Completion.norm_coe _
  refine ⟨h, ?_⟩
  rw [NumberField.InfiniteAdeleRing.norm_def]
  exact Finset.prod_congr rfl fun v _ => by rw [h v]
