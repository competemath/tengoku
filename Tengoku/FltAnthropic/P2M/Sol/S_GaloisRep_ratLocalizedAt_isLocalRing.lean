import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_GaloisRep_ratLocalizedAt_isLocalRing.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_GaloisRep_ratLocalizedAt_isLocalRing

namespace GaloisRep
export _root_.GaloisRep (ratLocalizedAt)
namespace FlatSol
open _root_.GaloisRep

/--
@isnad1 id=iff.0h2v.s5.dac7271e7e36 from=translated src=- shape=c7a4012e vocab=9256c41c
-/
theorem mem_ratLocalizedAt_iff_coprime {p : ℕ} (q : ℚ) :
    q ∈ ratLocalizedAt p ↔ q.den.Coprime p :=
  Iff.rfl

/--
@isnad1 id=iff.1h2v.s5.0bdd73cb1a52 from=translated src=- shape=c36e0ae1 vocab=665e5dc6
-/
theorem mem_ratLocalizedAt_iff {p : ℕ} (hp : p.Prime) (q : ℚ) :
    q ∈ ratLocalizedAt p ↔ ¬ p ∣ q.den := by
  rw [mem_ratLocalizedAt_iff_coprime, Nat.coprime_comm, hp.coprime_iff_not_dvd]

/--
@isnad1 id=iff.1h2v.s7.8de4831a5e5f from=translated src=- shape=edf58b6b vocab=ad4f134a
-/
theorem ratLocalizedAt.isUnit_iff {p : ℕ} (hp : p.Prime) (x : ratLocalizedAt p) :
    IsUnit x ↔ ¬ p ∣ (x : ℚ).num.natAbs := by
  constructor
  · intro hx
    obtain ⟨y, hy⟩ := hx.exists_right_inv
    have hxy : (x : ℚ) * y = 1 := by
      rw [← Subring.coe_mul, hy, Subring.coe_one]
    have hx0 : (x : ℚ) ≠ 0 := left_ne_zero_of_mul_eq_one hxy
    have hyden : ¬ p ∣ (y : ℚ).den := (mem_ratLocalizedAt_iff hp _).mp y.2
    rwa [eq_inv_of_mul_eq_one_right hxy, Rat.den_inv_of_ne_zero hx0] at hyden
  · intro hx
    have hx0 : (x : ℚ) ≠ 0 := by
      intro h0
      apply hx
      rw [h0, Rat.zero_num, Int.natAbs_zero]
      exact dvd_zero p
    have hmem : (x : ℚ)⁻¹ ∈ ratLocalizedAt p := by
      rw [mem_ratLocalizedAt_iff hp, Rat.den_inv_of_ne_zero hx0]
      exact hx
    exact IsUnit.of_mul_eq_one ⟨(x : ℚ)⁻¹, hmem⟩ (Subtype.ext (mul_inv_cancel₀ hx0))

/--
@isnad1 id=islocalr.1h1v.s6.3fad730b80cf from=translated src=- shape=6cdec8b9 vocab=f8d952d1
-/
theorem ratLocalizedAt.isLocalRing {p : ℕ} (hp : p.Prime) : IsLocalRing (ratLocalizedAt p) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun a => ?_
  by_cases ha : p ∣ (a : ℚ).num.natAbs
  · refine Or.inr ((ratLocalizedAt.isUnit_iff hp (1 - a)).mpr fun h1 =>
      (mem_ratLocalizedAt_iff hp _).mp a.2 ?_)

    have hcoe : ((1 - a : ratLocalizedAt p) : ℚ) = 1 - (a : ℚ) := rfl
    have hden : (1 - (a : ℚ)).den = (a : ℚ).den := by
      simpa only [Int.cast_one] using Rat.intCast_sub_den 1 (a : ℚ)
    have hnum : (1 - (a : ℚ)).num = (a : ℚ).den - (a : ℚ).num := by
      have h : ((1 - (a : ℚ)).num : ℚ) = (((a : ℚ).den : ℤ) - (a : ℚ).num : ℤ) := by
        rw [← Rat.mul_den_eq_num, hden, sub_mul, one_mul, Rat.mul_den_eq_num]
        push_cast
        rfl
      exact_mod_cast h
    rw [hcoe, ← Int.natCast_dvd, hnum] at h1
    rw [← Int.natCast_dvd] at ha
    have hsum := dvd_add h1 ha
    rw [sub_add_cancel] at hsum
    exact Int.natCast_dvd_natCast.mp hsum
  · exact Or.inl ((ratLocalizedAt.isUnit_iff hp a).mpr ha)

end GaloisRep.FlatSol

/--
@isnad1 id=islocalr.1h1v.s6.3fad730b80cf from=translated src=- shape=6cdec8b9 vocab=f8d952d1
-/
theorem solution
    {p : ℕ} (hp : p.Prime) : IsLocalRing (GaloisRep.ratLocalizedAt p) :=
  GaloisRep.FlatSol.ratLocalizedAt.isLocalRing hp
