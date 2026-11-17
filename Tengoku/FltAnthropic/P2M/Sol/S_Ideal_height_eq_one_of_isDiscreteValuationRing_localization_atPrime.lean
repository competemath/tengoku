import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Ideal_height_eq_one_of_isDiscreteValuationRing_localization_atPrime

set_option autoImplicit false

/--
@isnad1 id=eq.1h2v.s6.b8fb73b208a8 from=translated src=- shape=b8b5a730 vocab=28e489a0
-/
theorem solution {R : Type*} [CommRing R] [IsDomain R] (p : Ideal R) [p.IsPrime]
    (h : IsDiscreteValuationRing (Localization.AtPrime p)) : p.height = 1 := by
  haveI := h
  have hnf : ¬ IsField (Localization.AtPrime p) := fun hF =>
    IsDiscreteValuationRing.not_a_field (R := Localization.AtPrime p)
      ((IsLocalRing.isField_iff_maximalIdeal_eq).mp hF)
  have hd1 : ringKrullDim (Localization.AtPrime p) = 1 :=
    IsPrincipalIdealRing.ringKrullDim_eq_one (Localization.AtPrime p) hnf
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p (Localization.AtPrime p)] at hd1
  exact_mod_cast hd1
