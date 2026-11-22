import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_NumberField_InfinitePlaceTransport
import Tengoku.FltAnthropic.Definitions.Def_NumberField_ArchimedeanIdeleModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_InfinitePlaceTransport_transport_eq_actRingEquiv

set_option autoImplicit false

/--
@isnad1 id=eq.1h4v.s10.8280e1f35dff from=translated src=- shape=41afa053 vocab=a72f9d1c
-/
theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (σ : NumberField.InfPlaceDecomp.decomp E K w) (h : (σ : K ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (σ : K ≃ₐ[E] K) h = NumberField.InfPlaceDecomp.actRingEquiv σ :=
  rfl
