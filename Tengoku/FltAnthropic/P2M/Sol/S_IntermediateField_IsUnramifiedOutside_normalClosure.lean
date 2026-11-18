import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GroupCohomology_ContinuousUnramified
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IntermediateField_IsUnramifiedOutside_normalClosure.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IntermediateField_IsUnramifiedOutside_normalClosure

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 1600000

open scoped Pointwise

namespace IntermediateField export _root_.IntermediateField (smul_def mem_fixingSubgroup_iff le_iff_le fixingSubgroup fixingSubgroup_antitone mem_map normalClosure_def'' normal map normalClosure IsUnramifiedOutside) end IntermediateField
open scoped _root_.IntermediateField in

private theorem IntermediateField.le_fixingSubgroup_iSup_of_forall_le_NC {ι : Sort*}
    (E : ι → IntermediateField ℚ (AlgebraicClosure ℚ))
    (H : Subgroup (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (h : ∀ i, H ≤ (E i).fixingSubgroup) : H ≤ (⨆ i, E i).fixingSubgroup := by
  rw [← IntermediateField.le_iff_le, iSup_le_iff]
  exact fun i => (IntermediateField.le_iff_le _ _).2 (h i)

namespace ValuationSubring export _root_.ValuationSubring (mem_nonunits_iff_or mem_pointwise_smul_iff_inv_smul_mem LiesOverPrime inertiaSubgroupIn conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul) end ValuationSubring
open scoped _root_.ValuationSubring in

private theorem ValuationSubring.liesOverPrime_smul_NC {A : ValuationSubring (AlgebraicClosure ℚ)} {q : ℕ}
    (hA : A.LiesOverPrime q) (g : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    (g • A).LiesOverPrime q := by
  rw [ValuationSubring.LiesOverPrime, ValuationSubring.mem_nonunits_iff_or] at hA ⊢
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, map_inv₀, map_natCast]
  exact hA

/--
@isnad1 id=isunrami.1h2v.s8.4ae91bb814a4 from=translated src=- shape=ef26fe78 vocab=0c9ee451
-/
theorem solution
    {S : Finset Nat.Primes} {F : IntermediateField ℚ (AlgebraicClosure ℚ)}
    (hF : F.IsUnramifiedOutside S) :
    (IntermediateField.normalClosure ℚ F (AlgebraicClosure ℚ)).IsUnramifiedOutside S := by
  haveI : Algebra.IsAlgebraic ℚ (AlgebraicClosure ℚ) := AlgebraicClosure.isAlgebraic ℚ
  haveI : IsAlgClosure ℚ (AlgebraicClosure ℚ) := ⟨inferInstance, inferInstance⟩
  haveI : Normal ℚ (AlgebraicClosure ℚ) := IsAlgClosure.normal ℚ (AlgebraicClosure ℚ)
  haveI : FiniteDimensional ℚ F := hF.1

  refine ⟨inferInstance, fun q hq A hA => ?_⟩

  have key : A.inertiaSubgroupIn ℚ ≤
      (⨆ g : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ),
        F.map (g : AlgebraicClosure ℚ →ₐ[ℚ] AlgebraicClosure ℚ)).fixingSubgroup := by
    refine IntermediateField.le_fixingSubgroup_iSup_of_forall_le_NC _ _ fun g => ?_
    intro σ hσ

    have hA' : (g⁻¹ • A).LiesOverPrime q := ValuationSubring.liesOverPrime_smul_NC hA g⁻¹
    have hσ' : σ ∈ (g • (g⁻¹ • A)).inertiaSubgroupIn ℚ := by rwa [smul_inv_smul]
    have hmem := hF.2 q hq (g⁻¹ • A) hA'
      (ValuationSubring.conj_mem_inertiaSubgroupIn_of_mem_inertiaSubgroupIn_smul _ g hσ')
    rw [IntermediateField.mem_fixingSubgroup_iff] at hmem ⊢
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (IntermediateField.mem_map F).1 hy
    have hgx := congrArg g (hmem x hx)
    simp only [AlgEquiv.mul_apply, AlgEquiv.aut_inv, AlgEquiv.apply_symm_apply] at hgx
    simpa using hgx
  exact key.trans (IntermediateField.fixingSubgroup_antitone (IntermediateField.normalClosure_def'' F).le)
