import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AbsoluteValue_Completion_norm_coe_and_exists_one_lt_norm.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AbsoluteValue_Completion_norm_coe_and_exists_one_lt_norm

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 80000

/--
@isnad1 id=and.0h2v.s8.b2ff7167ad0e from=translated src=- shape=d24e6d3b vocab=8d5eaf80
-/
theorem solution
    {K : Type*} [Field K] (v : AbsoluteValue K ℝ) :
    (∀ x : K, ‖(x : v.Completion)‖ = v x) ∧ (v.IsNontrivial → ∃ x : v.Completion, 1 < ‖x‖) := by
  have h : ∀ x : K, ‖(x : v.Completion)‖ = v x := fun x => by
    rw [UniformSpace.Completion.norm_coe, WithAbs.norm_eq_apply_ofAbs]
  refine ⟨h, fun hnt => ?_⟩
  obtain ⟨x, hx⟩ := hnt.exists_abv_gt_one
  exact ⟨x, by rwa [h]⟩

