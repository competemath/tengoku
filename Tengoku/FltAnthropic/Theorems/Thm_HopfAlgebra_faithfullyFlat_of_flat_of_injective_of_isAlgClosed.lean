import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open scoped TensorProduct

universe u v w

/--
@isnad1 id=faithful.3h3v.s12.594e27669aa6 from=translated src=- shape=10a41b73 vocab=738d6164
-/
theorem HopfAlgebra.faithfullyFlat_of_flat_of_injective_of_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k]
    (K : Type v) [CommRing K] [HopfAlgebra k K] [Algebra.FiniteType k K]
    (H : Type w) [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]
    [Algebra K H] [IsScalarTower k K H] (hinj : Function.Injective (algebraMap K H))
    (hcomul : ∀ x : K, Coalgebra.comul (R := k) (algebraMap K H x) =
      TensorProduct.map (IsScalarTower.toAlgHom k K H).toLinearMap (IsScalarTower.toAlgHom k K H).toLinearMap
        (Coalgebra.comul (R := k) x))
    (hcounit : ∀ x : K, Coalgebra.counit (R := k) (algebraMap K H x) = Coalgebra.counit (R := k) x)
    [Module.Flat K H] :
    Module.FaithfullyFlat K H := by exact @_root_.P2MW.S_HopfAlgebra_faithfullyFlat_of_flat_of_injective_of_isAlgClosed.solution k _ _ K _ _ _ H _ _ _ _ _ hinj hcomul hcounit _
