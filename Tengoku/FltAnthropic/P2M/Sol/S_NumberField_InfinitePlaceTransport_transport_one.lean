import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_NumberField_InfinitePlaceTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfinitePlaceTransport_transport_one.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_InfinitePlaceTransport_transport_one

set_option autoImplicit false

/--
@isnad1 id=eq.1h3v.s9.184c0ea934be from=translated src=- shape=4456c27e vocab=dd31fc61
-/
theorem solution (E K : Type*) [Field E] [Field K] [Algebra E K]
    (w : NumberField.InfinitePlace K) (h : (1 : K ≃ₐ[E] K) • w = w) :
    NumberField.InfinitePlaceTransport.transport (1 : K ≃ₐ[E] K) h = RingEquiv.refl w.Completion := by
  apply RingEquiv.ext
  intro x
  rw [RingEquiv.refl_apply]
  refine NumberField.InfinitePlace.Completion.induction_on _ x
    (isClosed_eq (NumberField.InfinitePlaceTransport.continuous_transport (1 : K ≃ₐ[E] K) h) continuous_id)
    fun a => ?_
  change NumberField.InfinitePlaceTransport.transport (1 : K ≃ₐ[E] K) h (a : w.Completion) = (a : w.Completion)
  rw [NumberField.InfinitePlaceTransport.transport_coe]
  rfl
