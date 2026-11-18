import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_CharPReduction
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_CoeffSemilinearAut
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_pow_char_eq_map_frobenius_qExpand

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#check @ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#check @ModularCurve.coeffRed_coeffMap_pow_char_eq_qExpand` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ModularCurve.coeffRed_coeffMap_pow_char_eq_qExpand` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#check @ModularCurve.coeffRed_coeffMap_eq_of_inertial` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius

set_option autoImplicit false

noncomputable section

namespace ModularCurve
export _root_.ModularCurve (CharPReduction.integralCoeffs CharPReduction.coeffRed CharPReduction.coeffRed_coeff coeffMap coeffMap_coeff coeffMap_coeffMap coeffMap_congr qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd coeffSemilinearAut pow_char_eq_map_frobenius_qExpand)
open _root_.ModularCurve

open _root_.ModularCurve.coeffSemilinearAut

section CoeffGrain

variable {A k : Type*} [CommRing A] [CommRing k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
variable (red : A →+* k) (τ : A →+* A)

private theorem coeffMap_pow_char_eq_qExpand_of_frobenius (hτ : ∀ a : A, red (τ a) ^ ℓ = red a) (x : LaurentSeries A) :
    coeffMap red (coeffMap τ x) ^ ℓ = qExpand k ℓ (coeffMap red x) := by
  rw [pow_char_eq_map_frobenius_qExpand ℓ (coeffMap red (coeffMap τ x)),
    show (qExpand k ℓ (coeffMap red (coeffMap τ x))).map (frobenius k ℓ)
        = coeffMap (frobenius k ℓ) (qExpand k ℓ (coeffMap red (coeffMap τ x))) from rfl,
    coeffMap_qExpand, coeffMap_coeffMap, coeffMap_coeffMap]
  congr 1
  refine coeffMap_congr (RingHom.ext fun a => ?_) x
  rw [RingHom.comp_apply, RingHom.comp_apply, frobenius_def]
  exact hτ a

end CoeffGrain

section ApparatusGrain

variable {L k : Type*} [CommRing L] [Field k] (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ]
variable (A : Subring L) (red : A →+* k) (τL : L →+* L)

private theorem coeffMap_mem_integralCoeffs (hτA : ∀ a ∈ A, τL a ∈ A) {x : LaurentSeries L}
    (hx : x ∈ CharPReduction.integralCoeffs A) : coeffMap τL x ∈ CharPReduction.integralCoeffs A := fun n => by
  rw [coeffMap_coeff]
  exact hτA _ (hx n)

private def restrictEndo (hτA : ∀ a ∈ A, τL a ∈ A) : A →+* A := τL.restrict A A hτA

private theorem coeffRed_coeffMap_coeff (hτA : ∀ a ∈ A, τL a ∈ A) (x : CharPReduction.integralCoeffs A) (n : ℤ) :
    (CharPReduction.coeffRed A red ⟨coeffMap τL (x : LaurentSeries L), coeffMap_mem_integralCoeffs A τL hτA x.2⟩).coeff n
      = red (restrictEndo A τL hτA ⟨(x : LaurentSeries L).coeff n, x.2 n⟩) := by
  rw [CharPReduction.coeffRed_coeff]
  rfl

private theorem coeffRed_coeffMap_pow_char_eq_qExpand (hτA : ∀ a ∈ A, τL a ∈ A)
    (hF : ∀ a : A, red (restrictEndo A τL hτA a) ^ ℓ = red a) (x : CharPReduction.integralCoeffs A) :
    CharPReduction.coeffRed A red ⟨coeffMap τL (x : LaurentSeries L), coeffMap_mem_integralCoeffs A τL hτA x.2⟩ ^ ℓ
      = qExpand k ℓ (CharPReduction.coeffRed A red x) := by
  rw [pow_char_eq_map_frobenius_qExpand ℓ]
  ext n
  rw [HahnSeries.map_coeff]
  by_cases h : (ℓ : ℤ) ∣ n
  · obtain ⟨m, rfl⟩ := h
    rw [qExpand_coeff_mul, qExpand_coeff_mul, coeffRed_coeffMap_coeff A red τL hτA, frobenius_def, hF,
      CharPReduction.coeffRed_coeff]
  · rw [qExpand_coeff_of_not_dvd _ _ h, qExpand_coeff_of_not_dvd _ _ h, map_zero]

private theorem coeffRed_coeffMap_eq_of_inertial (hτA : ∀ a ∈ A, τL a ∈ A)
    (hI : ∀ a : A, red (restrictEndo A τL hτA a) = red a) (x : CharPReduction.integralCoeffs A) :
    CharPReduction.coeffRed A red ⟨coeffMap τL (x : LaurentSeries L), coeffMap_mem_integralCoeffs A τL hτA x.2⟩
      = CharPReduction.coeffRed A red x := by
  ext n
  rw [coeffRed_coeffMap_coeff A red τL hτA, hI, CharPReduction.coeffRed_coeff]

end ApparatusGrain

end ModularCurve
open scoped _root_.P2MW.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius.ModularCurve

end
open scoped _root_.P2MW.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius.ModularCurve

open _root_.ModularCurve _root_.P2MW.S_ModularCurve_coeffMap_pow_char_eq_qExpand_of_frobenius.ModularCurve in
theorem solution {A k : Type*} [CommRing A] [CommRing k] (ℓ : ℕ) [Fact ℓ.Prime]
    [CharP k ℓ] (red : A →+* k) (τ : A →+* A) (hτ : ∀ a : A, red (τ a) ^ ℓ = red a)
    (x : LaurentSeries A) :
    ModularCurve.coeffMap red (ModularCurve.coeffMap τ x) ^ ℓ
      = ModularCurve.qExpand k ℓ (ModularCurve.coeffMap red x) :=
  ModularCurve.coeffMap_pow_char_eq_qExpand_of_frobenius ℓ red τ hτ x
