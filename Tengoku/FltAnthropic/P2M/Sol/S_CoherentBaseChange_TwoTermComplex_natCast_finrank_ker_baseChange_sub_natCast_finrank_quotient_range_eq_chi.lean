import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_CoherentBaseChange

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CoherentBaseChange_TwoTermComplex_natCast_finrank_ker_baseChange_sub_natCast_finrank_quotient_range_eq_chi

set_option autoImplicit false

universe u v w

open scoped TensorProduct
open _root_.CoherentBaseChange

namespace CoherentBaseChange
export _root_.CoherentBaseChange (TwoTermComplex)
namespace TwoTermComplex
export _root_.CoherentBaseChange.TwoTermComplex (chi C0 d C1)
namespace ChiFieldAux
open _root_.CoherentBaseChange.TwoTermComplex open _root_.CoherentBaseChange

variable {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
  (K : Type w) [Field K] [Algebra R K]

noncomputable def rk : ℕ := Module.finrank K (LinearMap.range (G.d.baseChange K))

/--
@isnad1 id=eq.0h3v.s11.523b47cb9d0f from=translated src=- shape=c6a3ebe7 vocab=7a1f53cc
-/
theorem h0_add_rk :
    Module.finrank K (LinearMap.ker (G.d.baseChange K)) + rk G K =
      Module.finrank K (K ⊗[R] G.C0) := by
  have h := LinearMap.finrank_range_add_finrank_ker (G.d.baseChange K)
  unfold rk; omega

/--
@isnad1 id=eq.0h3v.s11.d0787791c35f from=translated src=- shape=57571614 vocab=5cd10710
-/
theorem rk_add_h1 :
    rk G K + Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) =
      Module.finrank K (K ⊗[R] G.C1) := by
  have h := Submodule.finrank_quotient_add_finrank (LinearMap.range (G.d.baseChange K))
  unfold rk; omega

/--
@isnad1 id=eq.0h3v.s12.8032d0a32de4 from=translated src=- shape=f6e2675f vocab=bc460bf3
-/
theorem main :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  haveI : Nontrivial R := (algebraMap R K).domain_nontrivial
  have h0 := h0_add_rk G K
  have h1 := rk_add_h1 G K
  rw [Module.finrank_baseChange] at h0 h1
  show _ = (Module.finrank R G.C0 : ℤ) - (Module.finrank R G.C1 : ℤ)
  have h0' : (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) + (rk G K : ℤ) =
      (Module.finrank R G.C0 : ℤ) := by exact_mod_cast h0
  have h1' : (rk G K : ℤ) + (Module.finrank K ((K ⊗[R] G.C1) ⧸
      LinearMap.range (G.d.baseChange K)) : ℤ) = (Module.finrank R G.C1 : ℤ) := by exact_mod_cast h1
  omega

end CoherentBaseChange.TwoTermComplex.ChiFieldAux

/--
@isnad1 id=eq.0h3v.s12.8032d0a32de4 from=translated src=- shape=f6e2675f vocab=bc460bf3
-/
theorem solution
    {R : Type u} [CommRing R] (G : CoherentBaseChange.TwoTermComplex.{u, v} R)
    (K : Type w) [Field K] [Algebra R K] :
    (Module.finrank K (LinearMap.ker (G.d.baseChange K)) : ℤ) -
      Module.finrank K ((K ⊗[R] G.C1) ⧸ LinearMap.range (G.d.baseChange K)) = G.chi := by
  exact CoherentBaseChange.TwoTermComplex.ChiFieldAux.main G K
