import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Mathlib_Algebra_IsDirectLimit
import Tengoku.FltAnthropic.P2M.Sol.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open scoped TensorProduct

universe u v w w'

/--
@isnad1 id=ex.1h5v.s9.0fe3b94adc24 from=translated src=- shape=0129ccba vocab=fcbbf89f
-/
theorem Algebra.exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit
    {ι : Type u} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    (G : ι → Type v) [∀ i, CommRing (G i)] (f : ∀ i j : ι, i ≤ j → G i →+* G j)
    [DirectedSystem G fun i j h => ⇑(f i j h)]
    (R : Type w) [CommRing R] [∀ i, Algebra (G i) R]
    (hR : IsDirectLimit (fun i j h => ⇑(f i j h)) fun i => ⇑(algebraMap (G i) R))
    (A : Type w') [CommRing A] [Algebra R A] [Algebra.FinitePresentation R A] :
    ∃ (i : ι) (A₀ : Type v) (_ : CommRing A₀) (_ : Algebra (G i) A₀)
      (_ : Algebra.FinitePresentation (G i) A₀), Nonempty ((R ⊗[G i] A₀) ≃ₐ[R] A) := by exact @_root_.P2MW.S_Algebra_exists_finitePresentation_tensorProduct_algEquiv_of_isDirectLimit.solution ι _ _ _ G _ f _ R _ _ hR A _ _ _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
