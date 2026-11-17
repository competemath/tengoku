import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_inf_of_not_isAffine.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicGeometry_Scheme_TwoAffineOpenCover_nonempty_inf_of_not_isAffine

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

/--
@isnad1 id=nonempty.1h2v.s6.abbf38dfa912 from=translated src=- shape=116deb7f vocab=4a23cb4a
-/
theorem solution
    {X : Scheme.{u}} [IrreducibleSpace X] (𝒱 : X.TwoAffineOpenCover) (hX : ¬ IsAffine X) :
    ((𝒱.U0 ⊓ 𝒱.U1 : X.Opens) : Set X).Nonempty := by

  have hne : ∀ {U V : X.Opens}, IsAffineOpen U → U ⊔ V = ⊤ → ((V : X.Opens) : Set X).Nonempty := by
    intro U V hU hUV
    rw [← TopologicalSpace.Opens.ne_bot_iff_nonempty]
    rintro rfl
    rw [sup_bot_eq] at hUV
    subst hUV
    exact hX (@IsAffine.of_isIso _ _ X.topIso.inv inferInstance hU)
  have h1 : ((𝒱.U1 : X.Opens) : Set X).Nonempty := hne 𝒱.isAffineOpen_U0 𝒱.sup_eq_top
  have h0 : ((𝒱.U0 : X.Opens) : Set X).Nonempty := hne 𝒱.isAffineOpen_U1 (by rw [sup_comm]; exact 𝒱.sup_eq_top)
  exact nonempty_preirreducible_inter 𝒱.U0.isOpen 𝒱.U1.isOpen h0 h1
