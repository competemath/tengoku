import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_ker_counit_eq_sq_of_pow_eq_one_of_isUnit
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_formallyUnramified_of_ker_counit_eq_sq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_etale_of_pow_eq_one_of_isUnit_of_finite.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_etale_of_pow_eq_one_of_isUnit_of_finite

universe u v

set_option autoImplicit false

theorem solution
    {R : Type u} [CommRing R] {H : Type v} [CommRing H] [HopfAlgebra R H]
    [IsNoetherianRing R] [Module.Finite R H] [Module.Flat R H]
    (n : ℕ) (hn : IsUnit (n : R))
    (hH : ∀ (T : Type v) [CommRing T] [Algebra R T] (f : WithConv (H →ₐ[R] T)), f ^ n = 1) :
    Algebra.Etale R H := by
  haveI : Algebra.FinitePresentation R H := (Algebra.FinitePresentation.of_finiteType).mp inferInstance
  haveI := HopfAlgebra.formallyUnramified_of_ker_counit_eq_sq
    (HopfAlgebra.ker_counit_eq_sq_of_pow_eq_one_of_isUnit (R := R) (H := H) n hn hH)
  exact Algebra.Etale.of_formallyUnramified_of_flat
