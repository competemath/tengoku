import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Tengoku.Seed.Analysis.Normed.Group.Bounded
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Analysis.Complex.Circle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms norm_apply_eq_one_of_isGlobalAddChar_impl` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_compAddChar_eq_of_isGlobalAddChar_impl` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 3 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar

set_option autoImplicit false

open _root_.NumberField open _root_.IsDedekindDomain open _root_.AutomorphicForm open _root_.Filter

noncomputable section

namespace NumberField
export _root_.NumberField (AdeleRing AdelicBox.existsUnique_algebraMap_add_mem_adelicBox AdelicBox.exists_isCompact_adelicBox_subset)
namespace AdelicFourier
open _root_.NumberField

variable (F : Type) [Field F] [NumberField F]

local notation "𝔸" => AdeleRing (𝓞 F) F
local notation "ι" => algebraMap F (AdeleRing (𝓞 F) F)

theorem exists_norm_apply_le_of_isGlobalAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ M : ℝ, ∀ x : 𝔸, ‖ψ x‖ ≤ M := by
  obtain ⟨C, hC, hsub⟩ := AdelicBox.exists_isCompact_adelicBox_subset F
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hψ.continuous.continuousOn
  refine ⟨M, fun x => ?_⟩
  obtain ⟨k, hk⟩ := (AdelicBox.existsUnique_algebraMap_add_mem_adelicBox F x).exists
  have hkx : ψ (ι k + x) = ψ x := by
    rw [AddChar.map_add_eq_mul, hψ.principalInvariant k, one_mul]
  rw [← hkx]
  exact hM _ (hsub hk)

theorem norm_apply_le_one_of_bounded {ψ : AddChar 𝔸 ℂ} {M : ℝ} (hM : ∀ x : 𝔸, ‖ψ x‖ ≤ M)
    (x : 𝔸) : ‖ψ x‖ ≤ 1 := by
  by_contra h
  have h1 : 1 < ‖ψ x‖ := lt_of_not_ge h
  have hpow : ∀ n : ℕ, ‖ψ x‖ ^ n ≤ M := fun n => by
    rw [← norm_pow, ← AddChar.map_nsmul_eq_pow]
    exact hM _
  obtain ⟨n, hn⟩ := ((tendsto_pow_atTop_atTop_of_one_lt h1).eventually (eventually_gt_atTop M)).exists
  exact absurd (hpow n) (not_le.mpr hn)

theorem norm_apply_eq_one_of_isGlobalAddChar_impl {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) (x : 𝔸) :
    ‖ψ x‖ = 1 := by
  obtain ⟨M, hM⟩ := exists_norm_apply_le_of_isGlobalAddChar F hψ
  refine le_antisymm (norm_apply_le_one_of_bounded F hM x) ?_
  have hneg : ‖ψ (-x)‖ ≤ 1 := norm_apply_le_one_of_bounded F hM (-x)
  have hprod : ‖ψ (-x)‖ * ‖ψ x‖ = 1 := by
    rw [← norm_mul, ← AddChar.map_add_eq_mul, neg_add_cancel, AddChar.map_zero_eq_one, norm_one]
  calc (1 : ℝ) = ‖ψ (-x)‖ * ‖ψ x‖ := hprod.symm
    _ ≤ 1 * ‖ψ x‖ := mul_le_mul_of_nonneg_right hneg (norm_nonneg _)
    _ = ‖ψ x‖ := one_mul _

def toCircleAddChar {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) : AddChar 𝔸 Circle where
  toFun x := ⟨ψ x, mem_sphere_zero_iff_norm.2 (norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x)⟩
  map_zero_eq_one' := by
    ext
    simp only [AddChar.map_zero_eq_one]
    rfl
  map_add_eq_mul' a b := by
    ext
    simp only [AddChar.map_add_eq_mul]
    rfl

theorem exists_compAddChar_eq_of_isGlobalAddChar_impl {ψ : AddChar 𝔸 ℂ} (hψ : IsGlobalAddChar F ψ) :
    ∃ e : AddChar 𝔸 Circle, Circle.coeHom.compAddChar e = ψ :=
  ⟨toCircleAddChar F hψ, by ext x; rfl⟩

end NumberField.AdelicFourier

end

open _root_.NumberField open _root_.P2MW.S_NumberField_AdelicFourier_norm_apply_eq_one_of_isGlobalAddChar.NumberField open _root_.AutomorphicForm

theorem solution (F : Type) [Field F] [NumberField F]
    {ψ : AddChar (AdeleRing (𝓞 F) F) ℂ} (hψ : IsGlobalAddChar F ψ) (x : AdeleRing (𝓞 F) F) :
    ‖ψ x‖ = 1 := by
  exact NumberField.AdelicFourier.norm_apply_eq_one_of_isGlobalAddChar_impl F hψ x
