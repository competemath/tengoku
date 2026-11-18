import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LinearMap_finrank_ker_dualMap_eq_finrank_ker.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LinearMap_finrank_ker_dualMap_eq_finrank_ker

set_option autoImplicit false
open Module

/--
@isnad1 id=eq.0h3v.s10.7c28d4a4fbf9 from=translated src=- shape=1923beb9 vocab=e5683093
-/
theorem solution
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) :
    finrank K (LinearMap.ker f.dualMap) = finrank K (LinearMap.ker f) := by
  have h1 := Subspace.finrank_add_finrank_dualAnnihilator_eq (LinearMap.range f)
  have h2 := f.finrank_range_add_finrank_ker
  rw [LinearMap.ker_dualMap_eq_dualAnnihilator_range]
  omega
