import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicHeight
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_AdelicMaximalCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicHeight_adelicHeight_mul_of_mem_adelicMaximalCompact

set_option autoImplicit false

open NumberField NumberField.AdelicHeight NumberField.AdelicLevel IsDedekindDomain AutomorphicForm

namespace HTKSol

section Local

variable {K : Type*} [NormedField K] [IsUltrametricDist K]

/--
@isnad1 id=le.1h3v.s7.2da5154b0d2f from=translated src=- shape=944067d2 vocab=1b1cab7c
-/
theorem rowMaxNorm_mul_le (M k : Matrix (Fin 2) (Fin 2) K) (hk : ∀ i j, ‖k i j‖ ≤ 1) :
    rowMaxNorm (M * k) ≤ rowMaxNorm M := by
  have h : ∀ j, ‖(M * k) 1 j‖ ≤ rowMaxNorm M := by
    intro j
    rw [Matrix.mul_apply, Fin.sum_univ_two]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 0 j)).trans (le_max_left _ _)
    · rw [norm_mul]
      exact (mul_le_of_le_one_right (norm_nonneg _) (hk 1 j)).trans (le_max_right _ _)
  exact max_le (h 0) (h 1)

omit [IsUltrametricDist K] in
/--
@isnad1 id=eq.0h3v.s9.b78be0e58aef from=translated src=- shape=5a325dd3 vocab=095946d9
-/
theorem coe_mul' (g k : GL (Fin 2) K) :
    ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = (g : Matrix (Fin 2) (Fin 2) K) * (k : Matrix (Fin 2) (Fin 2) K) :=
  rfl

/--
@isnad1 id=eq.2h3v.s9.cee4f5303373 from=translated src=- shape=ee6a763a vocab=2bcb61bd
-/
theorem rowMaxNorm_mul_eq (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    rowMaxNorm ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = rowMaxNorm (g : Matrix (Fin 2) (Fin 2) K) := by
  refine le_antisymm ?_ ?_
  · rw [coe_mul']; exact rowMaxNorm_mul_le _ _ hk
  · have h := rowMaxNorm_mul_le ((g * k : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
      ((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) hk'
    rwa [← coe_mul', mul_inv_cancel_right] at h

/--
@isnad1 id=eq.2h2v.s8.43ac2bd41ef6 from=translated src=- shape=4ac9601d vocab=93ea93ab
-/
theorem norm_det_eq_one (k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
  have hd : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk
  have hd' : ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ ≤ 1 := norm_det_le_one hk'
  have hprod : ‖(k : Matrix (Fin 2) (Fin 2) K).det‖ *
      ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K).det‖ = 1 := by
    rw [← norm_mul, ← Matrix.det_mul, ← coe_mul', mul_inv_cancel, Units.val_one, Matrix.det_one, norm_one]
  refine le_antisymm hd ?_
  by_contra hlt
  push Not at hlt
  have := mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hlt hd'
  rw [hprod] at this
  exact lt_irrefl _ this

/--
@isnad1 id=eq.2h3v.s9.38407645de1a from=translated src=- shape=cb6a5714 vocab=2806211b
-/
theorem finLocalHeight_mul_eq (g k : GL (Fin 2) K)
    (hk : ∀ i j, ‖(k : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1)
    (hk' : ∀ i j, ‖((k⁻¹ : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) i j‖ ≤ 1) :
    finLocalHeight (g * k) = finLocalHeight g := by
  unfold finLocalHeight
  rw [rowMaxNorm_mul_eq g k hk hk', coe_mul', Matrix.det_mul, norm_mul, norm_det_eq_one k hk hk', mul_one]

end Local

/--
@isnad1 id=eq.1h3v.s10.7d106710923e from=translated src=- shape=ca01d2ba vocab=a631130a
-/
theorem finHeight_mul_eq (F : Type) [Field F] [NumberField F]
    (g k : GL (Fin 2) (FiniteAdeleRing (𝓞 F) F)) (hk : k ∈ finiteIntegralGL2 (𝓞 F) F) :
    finHeight F (g * k) = finHeight F g := by
  rw [mem_finiteIntegralGL2_iff] at hk
  unfold finHeight
  refine finprod_congr fun v => ?_
  rw [map_mul]
  refine finLocalHeight_mul_eq _ _ (fun i j => ?_) (fun i j => ?_)
  · rw [finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.1 i j v)
  · rw [← map_inv, finComponent_apply]
    exact norm_le_one_of_mem_adicCompletionIntegers (hk.2 i j v)

end HTKSol

/--
@isnad1 id=eq.1h3v.s9.cfaf5a91c36d from=translated src=- shape=09ded790 vocab=f8409b30
-/
theorem solution
    (F : Type) [Field F] [NumberField F]
    (g : AdelicGL2 (𝓞 F) F) (k : AdelicGL2 (𝓞 F) F) (hk : k ∈ AutomorphicForm.adelicMaximalCompact F) :
    adelicHeight F (g * k) = adelicHeight F g := by
  unfold adelicHeight
  rw [map_mul, map_mul, AutomorphicForm.WindowedSiegel.archHeight_mul_rowIsometry F _ hk.2,
    HTKSol.finHeight_mul_eq F _ _ hk.1]
