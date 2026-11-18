import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_SupersingularModuli

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_eq_zero_of_mem_ssJSet_two.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_eq_zero_of_mem_ssJSet_two

set_option autoImplicit false

open ModularCurve WeierstrassCurve

namespace GaussPencil
namespace SS

/--
@isnad1 id=eq.0h1v.s5.f0b797f9faac from=translated src=- shape=9306f47f vocab=e8bc6838
-/
theorem two_eq_zero (k : Type*) [Ring k] [CharP k 2] : (2 : k) = 0 := by
  simpa using CharP.cast_eq_zero k 2

/--
@isnad1 id=eq.0h1v.s5.8c5431ff9bf2 from=translated src=- shape=9306f47f vocab=e8bc6838
-/
theorem cast1728_eq_zero_of_two (k : Type*) [Ring k] [CharP k 2] : (1728 : k) = 0 := by
  rw [show (1728 : k) = 2 * 864 by norm_num, two_eq_zero k, zero_mul]

/--
@isnad1 id=ex.2h2v.s8.a01b99126318 from=translated src=- shape=e85d412b vocab=cee4edb6
-/
theorem exists_two_torsion_char_two {k : Type*} [Field k] [CharP k 2] [DecidableEq k]
    (a : k) (h0 : a ≠ 0) (ha4 : a ^ 4 = a) :
    ∃ P : (ofJNe0Or1728 a).toAffine.Point, P ≠ 0 ∧ 2 • P = 0 := by
  have h1728 : (1728 : k) = 0 := cast1728_eq_zero_of_two k
  have ha3 : a ^ 3 = 1 := by
    have : a * (a ^ 3 - 1) = 0 := by rw [mul_sub, mul_one, ← pow_succ', ha4, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h h0
    · exact sub_eq_zero.mp h
  have hneg : ∀ x : k, -x = x := fun x => CharTwo.neg_eq x

  have heq : (ofJNe0Or1728 a).toAffine.Equation 0 a := by
    rw [WeierstrassCurve.Affine.equation_iff]
    simp only [ofJNe0Or1728, h1728, sub_zero]
    have : a ^ 5 = a ^ 2 := by rw [show (5 : ℕ) = 3 + 2 by norm_num, pow_add, ha3, one_mul]
    rw [this]
    linear_combination a ^ 2 * two_eq_zero k
  haveI : Fact (IsUnit a) := ⟨isUnit_iff_ne_zero.mpr h0⟩
  haveI : Fact (IsUnit (a - 1728)) := ⟨by rw [h1728, sub_zero]; exact isUnit_iff_ne_zero.mpr h0⟩
  have hns : (ofJNe0Or1728 a).toAffine.Nonsingular 0 a :=
    (WeierstrassCurve.Affine.equation_iff_nonsingular (W := ofJNe0Or1728 a)).mp heq
  refine ⟨WeierstrassCurve.Affine.Point.some _ _ hns, WeierstrassCurve.Affine.Point.some_ne_zero hns, ?_⟩
  have hy : a = (ofJNe0Or1728 a).toAffine.negY 0 a := by
    simp only [WeierstrassCurve.Affine.negY, ofJNe0Or1728, mul_zero, sub_zero]
    exact (hneg a).symm
  rw [two_nsmul]
  exact WeierstrassCurve.Affine.Point.add_self_of_Y_eq hy

end GaussPencil.SS

/--
@isnad1 id=eq.2h2v.s6.b9d452265c76 from=translated src=- shape=b163faee vocab=30713750
-/
theorem solution
    {k : Type*} [Field k] [CharP k 2] [DecidableEq k]
    (a : k) (ha : a ∈ ssJSet 2 k) (ha2 : a ^ (2 ^ 2) = a) : a = 0 := by
  by_contra h0
  haveI : Fact (IsUnit a) := ⟨isUnit_iff_ne_zero.mpr h0⟩
  haveI : Fact (IsUnit (a - 1728)) :=
    ⟨by rw [GaussPencil.SS.cast1728_eq_zero_of_two k, sub_zero]; exact isUnit_iff_ne_zero.mpr h0⟩
  obtain ⟨P, hP0, hP2⟩ := GaussPencil.SS.exists_two_torsion_char_two a h0 (by simpa using ha2)
  exact hP0 (ha (ofJNe0Or1728 a) (ofJNe0Or1728_j a) P hP2)
