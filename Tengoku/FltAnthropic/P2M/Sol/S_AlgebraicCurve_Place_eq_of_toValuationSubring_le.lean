import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorPushPull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_eq_of_toValuationSubring_le.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Place_eq_of_toValuationSubring_le.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Place_eq_of_toValuationSubring_le

set_option autoImplicit false

namespace R1M3B
namespace PlaceAux

open AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

theorem coe_unit_inv_eq_inv (O : ValuationSubring F) (u : (↥O)ˣ) :
    (((u⁻¹ : (↥O)ˣ) : O) : F) = (((u : O) : F))⁻¹ := by
  have h1 : ((u : O) : F) * (((u⁻¹ : (↥O)ˣ) : O) : F) = 1 := by
    rw [← MulMemClass.coe_mul, Units.mul_inv, OneMemClass.coe_one]
  exact (eq_inv_of_mul_eq_one_right h1)

theorem eq_inv_mul_inv_pow (O : ValuationSubring F) {f : F} (hf : f ≠ 0) (hfinv : f⁻¹ ∈ O)
    {ϖ : O} (u : (↥O)ˣ) (m : ℕ) (hu : (⟨f⁻¹, hfinv⟩ : O) = u * ϖ ^ m) :
    f = (((u⁻¹ : (↥O)ˣ) : O) : F) * (((ϖ : F))⁻¹) ^ m := by
  have hval : f⁻¹ = ((u : O) : F) * ((ϖ : F)) ^ m := by
    have := congrArg Subtype.val hu
    simpa using this
  rw [coe_unit_inv_eq_inv, inv_pow, ← mul_inv, ← hval, inv_inv]

theorem eq_of_le {v w : Place K F} (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w := by
  apply Place.ext
  apply le_antisymm h
  by_contra hwv
  obtain ⟨x, hxw, hxv⟩ := SetLike.not_le_iff_exists.mp hwv
  set O := v.toValuationSubring with hO
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hxv (zero_mem O)
  have hxinv : x⁻¹ ∈ O := (O.mem_or_inv_mem x).resolve_left hxv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  have hϖ0 : ((ϖ : O) : F) ≠ 0 := by
    intro h0
    apply hϖ.ne_zero
    exact Subtype.ext h0
  have hϖw : ((ϖ : O) : F) ∈ w.toValuationSubring := h ϖ.2

  have hy0 : (⟨x⁻¹, hxinv⟩ : O) ≠ 0 := by
    intro h0
    have := congrArg Subtype.val h0
    simp only [ZeroMemClass.coe_zero, inv_eq_zero] at this
    exact hx0 this
  obtain ⟨m, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hϖ
  have hxeq := eq_inv_mul_inv_pow O hx0 hxinv u m hu

  have hm : m ≠ 0 := by
    rintro rfl
    apply hxv
    rw [hxeq, pow_zero, mul_one]
    exact ((u⁻¹ : (↥O)ˣ) : O).2
  obtain ⟨m', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm

  have hinvw : ((ϖ : O) : F)⁻¹ ∈ w.toValuationSubring := by
    have hval : x⁻¹ = ((u : O) : F) * ((ϖ : O) : F) ^ (m' + 1) := by
      have := congrArg Subtype.val hu
      simpa using this
    have hkey : ((ϖ : O) : F)⁻¹ = x * ((u : O) : F) * ((ϖ : O) : F) ^ m' := by
      symm
      apply eq_inv_of_mul_eq_one_left
      rw [mul_assoc, mul_assoc, ← pow_succ, ← hval, mul_inv_cancel₀ hx0]
    rw [hkey]
    exact mul_mem (mul_mem hxw (h (u : O).2)) (pow_mem hϖw m')

  apply w.ne_top'
  rw [eq_top_iff]
  intro f _
  by_cases hfO : f ∈ O
  · exact h hfO
  · have hf0 : f ≠ 0 := by
      rintro rfl
      exact hfO (zero_mem O)
    have hfinv : f⁻¹ ∈ O := (O.mem_or_inv_mem f).resolve_left hfO
    have hz0 : (⟨f⁻¹, hfinv⟩ : O) ≠ 0 := by
      intro h0
      have := congrArg Subtype.val h0
      simp only [ZeroMemClass.coe_zero, inv_eq_zero] at this
      exact hf0 this
    obtain ⟨n, u', hu'⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hz0 hϖ
    rw [eq_inv_mul_inv_pow O hf0 hfinv u' n hu']
    exact mul_mem (h ((u'⁻¹ : (↥O)ˣ) : O).2) (pow_mem hinvw n)

end R1M3B.PlaceAux

theorem solution
    {K F : Type*} [Field K] [Field F] [Algebra K F] {v w : AlgebraicCurve.Place K F}
    (h : v.toValuationSubring ≤ w.toValuationSubring) : v = w :=
  R1M3B.PlaceAux.eq_of_le h
