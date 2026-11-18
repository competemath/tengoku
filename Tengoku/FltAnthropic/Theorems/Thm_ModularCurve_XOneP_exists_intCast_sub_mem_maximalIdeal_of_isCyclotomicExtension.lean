import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ModularCurve_XOneP_exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ModularCurve_XOneP_exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

/--
@isnad1 id=ex.3h5v.s8.3a752880c8ba from=translated src=- shape=275802b5 vocab=4ae2b72a
-/
theorem ModularCurve.XOneP.exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension
    (p : ℕ) [Fact p.Prime]
    (L : Type) [Field L] [CharZero L] [IsCyclotomicExtension {p} ℚ L]
    (ζ : L) (hζ : IsPrimitiveRoot ζ p)
    (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] [Algebra A L] [IsFractionRing A L]
    (hAp : (p : A) ∈ IsLocalRing.maximalIdeal A) (hζA : ∃ z : A, algebraMap A L z = ζ) :
    ∀ a : A, ∃ n : ℤ, a - (n : A) ∈ IsLocalRing.maximalIdeal A := by exact @_root_.P2MW.S_ModularCurve_XOneP_exists_intCast_sub_mem_maximalIdeal_of_isCyclotomicExtension.solution p _ L _ _ _ ζ hζ A _ _ _ _ _ hAp hζA
