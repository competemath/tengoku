import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false
universe u v
open scoped TensorProduct
theorem HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal
    {F : Type u} [Field F] {A : Type v} [CommRing A] [HopfAlgebra F A] (I : Ideal A)
    (hcomul : ∀ a ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ F I) (Ideal.Quotient.mkₐ F I)
      (Coalgebra.comul (R := F) a) = 0)
    (hcounit : ∀ a ∈ I, Coalgebra.counit (R := F) a = 0)
    (hanti : ∀ a ∈ I, HopfAlgebraStruct.antipode (R := F) a ∈ I) :
    ∃ (A' : Type v) (_ : CommRing A') (_ : HopfAlgebra F A') (π : A →ₐc[F] A'),
      Function.Surjective π ∧
      RingHom.ker (π : A →+* A') = I ∧
      (Coalgebra.IsCocomm F A → Coalgebra.IsCocomm F A') ∧
      (Module.Finite F A → Module.Finite F A') ∧
      (∀ (T : Type v) [CommRing T] [Algebra F T] (φ : A →ₐ[F] T),
        I ≤ RingHom.ker (φ : A →+* T) → ∃! φ' : A' →ₐ[F] T, φ'.comp (π : A →ₐ[F] A') = φ) := by exact @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal.solution F _ A _ _ I hcomul hcounit hanti
