import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_isFractionRing_ratLocalizedAt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_isFractionRing_ratLocalizedAt

namespace SolB0C

open GaloisRep

private lemma mem_ratLocalizedAt_iff {p : ℕ} {q : ℚ} :
    q ∈ ratLocalizedAt p ↔ q.den.Coprime p := Iff.rfl

private def ratLocalizedAtMonoid (p : ℕ) : Submonoid ℤ where
  carrier := {z : ℤ | z ≠ 0 ∧ ((z : ℚ)⁻¹ ∈ ratLocalizedAt p)}
  one_mem' := by
    refine ⟨one_ne_zero, ?_⟩
    rw [Int.cast_one, inv_one, mem_ratLocalizedAt_iff]
    simp
  mul_mem' := by
    rintro a b ⟨ha0, ha⟩ ⟨hb0, hb⟩
    refine ⟨mul_ne_zero ha0 hb0, ?_⟩
    rw [Int.cast_mul, mul_inv]
    exact mul_mem ha hb

private lemma natCast_den_mem_ratLocalizedAtMonoid {p : ℕ} {q : ℚ} (hq : q ∈ ratLocalizedAt p) :
    ((q.den : ℤ)) ∈ ratLocalizedAtMonoid p := by
  refine ⟨Int.natCast_ne_zero.mpr q.den_nz, ?_⟩
  rw [mem_ratLocalizedAt_iff, Int.cast_natCast, Rat.inv_natCast_den_of_pos q.pos]
  exact hq

private scoped instance isLocalization (p : ℕ) :
    IsLocalization (ratLocalizedAtMonoid p) (ratLocalizedAt p) :=
  (isLocalization_iff (ratLocalizedAtMonoid p) (ratLocalizedAt p)).mpr
    ⟨by
      rintro ⟨z, hz0, hzi⟩
      refine isUnit_iff_exists_inv.mpr ⟨⟨(z : ℚ)⁻¹, hzi⟩, Subtype.ext ?_⟩
      push_cast
      exact mul_inv_cancel₀ (Int.cast_ne_zero.mpr hz0),
    by
      rintro ⟨x, hx⟩
      refine ⟨⟨x.num, ⟨(x.den : ℤ), natCast_den_mem_ratLocalizedAtMonoid hx⟩⟩, Subtype.ext ?_⟩
      push_cast
      exact (eq_div_iff (by exact_mod_cast x.den_nz)).mp (Rat.num_div_den x).symm,
    by
      intro a b h
      obtain rfl : a = b := Int.cast_injective (show ((a : ℚ)) = (b : ℚ) by
        exact_mod_cast congrArg Subtype.val h)
      exact ⟨1, rfl⟩⟩

end SolB0C
open scoped _root_.P2MW.S_GaloisRep_isFractionRing_ratLocalizedAt.SolB0C

/--
@isnad1 id=isfracti.0h1v.s6.210398e3bdf8 from=translated src=- shape=68508a85 vocab=c3810cec
-/
theorem solution (p : ℕ) :
    IsFractionRing (GaloisRep.ratLocalizedAt p) ℚ :=
  IsFractionRing.isFractionRing_of_isDomain_of_isLocalization (SolB0C.ratLocalizedAtMonoid p)
    (GaloisRep.ratLocalizedAt p) ℚ

