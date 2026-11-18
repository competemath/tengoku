import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Deformations_TameDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_TaylorWiles_tameDescentChar_comp_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_TaylorWiles_tameDescentChar_comp_eq

set_option autoImplicit false

universe u v w

open Function

/--
@isnad1 id=eq.2h6v.s9.7f4dc6db4760 from=translated src=- shape=47879318 vocab=7ccbcbbf
-/
theorem solution {G : Type u} {Δ : Type v} {A : Type w} [Group G] [Group Δ] [CommRing A]
    (π : G →* Δ) (hπ : Function.Surjective π) (χ : G →* Aˣ)
    (hχ : ∀ g ∈ π.ker, χ g = 1) (g : G) :
    TaylorWiles.tameDescentChar π hπ χ hχ (π g) = χ g := by
  have h : (QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g) =
      QuotientGroup.mk g := by
    apply (QuotientGroup.quotientKerEquivOfSurjective π hπ).injective
    rw [MulEquiv.apply_symm_apply]
    exact (QuotientGroup.kerLift_mk (φ := π) g).symm
  show (QuotientGroup.lift π.ker χ hχ)
      ((QuotientGroup.quotientKerEquivOfSurjective π hπ).symm (π g)) = χ g
  rw [h]
  rfl
