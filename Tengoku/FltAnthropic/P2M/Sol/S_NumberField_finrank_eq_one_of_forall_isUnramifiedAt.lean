import Tengoku.Seed.NumberTheory.NumberField.Discriminant.Different
import Tengoku.Seed.RingTheory.DedekindDomain.Different
import Tengoku.Seed.RingTheory.Localization.Integral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 1 `p2m_open_scoped`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt

set_option autoImplicit false

open Module
attribute [local instance] FractionRing.liftAlgebra

namespace NumberField
export _root_.NumberField (abs_discr_gt_two discr absNorm_differentIdeal)
open _root_.NumberField

variable (K : Type*) [Field K] [NumberField K]

open scoped _root_.NumberField _root_.P2MW.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt.NumberField

/--
@isnad1 id=eq.1h1v.s8.1241e38f3d45 from=translated src=- shape=d8b98f9b vocab=5d1d531d
-/
theorem differentIdeal_eq_top_of_forall_not_dvd'
    (h : ∀ P : Ideal (𝓞 K), P.IsMaximal → ¬ P ∣ differentIdeal ℤ (𝓞 K)) :
    differentIdeal ℤ (𝓞 K) = ⊤ := by
  by_contra hne
  obtain ⟨P, hPmax, hle⟩ := Ideal.exists_le_maximal _ hne
  exact h P hPmax (Ideal.dvd_iff_le.mpr hle)

/--
@isnad1 id=eq.1h1v.s7.ca68d7990d92 from=translated src=- shape=76f26584 vocab=ba84a5b9
-/
theorem natAbs_discr_eq_one_of_forall_not_dvd'
    (h : ∀ P : Ideal (𝓞 K), P.IsMaximal → ¬ P ∣ differentIdeal ℤ (𝓞 K)) :
    (discr K).natAbs = 1 := by
  have h1 : (differentIdeal ℤ (𝓞 K)).absNorm = (discr K).natAbs :=
    absNorm_differentIdeal (K := K) (𝒪 := 𝓞 K)
  rw [← h1, differentIdeal_eq_top_of_forall_not_dvd' K h, Ideal.absNorm_top]

/--
@isnad1 id=eq.1h1v.s7.ff7237999227 from=translated src=- shape=0eb44c4a vocab=156993b9
-/
theorem finrank_eq_one_of_forall_not_dvd'
    (h : ∀ P : Ideal (𝓞 K), P.IsMaximal → ¬ P ∣ differentIdeal ℤ (𝓞 K)) :
    finrank ℚ K = 1 := by
  by_contra hne
  have hpos : 0 < finrank ℚ K := finrank_pos
  have h1 : 1 < finrank ℚ K := by omega
  have h2 : 2 < |discr K| := abs_discr_gt_two h1
  rw [← Int.natCast_natAbs, natAbs_discr_eq_one_of_forall_not_dvd' K h] at h2
  norm_num at h2

/--
@isnad1 id=not.2h2v.s7.a05dbb8b5a96 from=translated src=- shape=a8d22161 vocab=bbc0238c
-/
theorem forall_not_dvd_differentIdeal_of_forall_isUnramifiedAt'
    (H : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], Algebra.IsUnramifiedAt ℤ P) :
    ∀ P : Ideal (𝓞 K), P.IsMaximal → ¬ P ∣ differentIdeal ℤ (𝓞 K) := by
  haveI : Algebra.IsAlgebraic (FractionRing ℤ) (FractionRing (𝓞 K)) :=
    isAlgebraic_of_isFractionRing (R := ℤ) (S := 𝓞 K) (FractionRing ℤ) (FractionRing (𝓞 K))
  haveI : Algebra.IsIntegral (FractionRing ℤ) (FractionRing (𝓞 K)) :=
    Algebra.isAlgebraic_iff_isIntegral.mp inferInstance
  intro P hP
  haveI := hP
  exact not_dvd_differentIdeal_iff.mpr (H P)

end NumberField

open scoped _root_.NumberField _root_.P2MW.S_NumberField_finrank_eq_one_of_forall_isUnramifiedAt.NumberField in

/--
@isnad1 id=eq.1h1v.s6.8e2fb4a2c1f5 from=translated src=- shape=f718b45f vocab=828f25e9
-/
theorem solution
    (K : Type*) [Field K] [NumberField K]
    (H : ∀ (P : Ideal (𝓞 K)) [P.IsMaximal], Algebra.IsUnramifiedAt ℤ P) :
    Module.finrank ℚ K = 1 :=
  NumberField.finrank_eq_one_of_forall_not_dvd' K
    (NumberField.forall_not_dvd_differentIdeal_of_forall_isUnramifiedAt' K H)
