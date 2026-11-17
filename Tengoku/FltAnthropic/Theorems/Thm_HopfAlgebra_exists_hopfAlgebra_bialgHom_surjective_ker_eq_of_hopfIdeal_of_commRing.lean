import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false
universe u v
open scoped TensorProduct

/--
@isnad1 id=ex.3h3v.s13.dba2f0321c20 from=translated src=- shape=3ca47613 vocab=b50c73b2
-/
theorem HopfAlgebra.exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing
    {R : Type u} [CommRing R] {A : Type v} [CommRing A] [HopfAlgebra R A] (I : Ideal A)
    (hcomul : ∀ a ∈ I, Algebra.TensorProduct.map (Ideal.Quotient.mkₐ R I) (Ideal.Quotient.mkₐ R I)
      (Coalgebra.comul (R := R) a) = 0)
    (hcounit : ∀ a ∈ I, Coalgebra.counit (R := R) a = 0)
    (hanti : ∀ a ∈ I, HopfAlgebraStruct.antipode (R := R) a ∈ I) :
    ∃ (A' : Type v) (_ : CommRing A') (_ : HopfAlgebra R A') (π : A →ₐc[R] A'),
      Function.Surjective π ∧
      RingHom.ker (π : A →+* A') = I ∧
      (Coalgebra.IsCocomm R A → Coalgebra.IsCocomm R A') ∧
      (Module.Finite R A → Module.Finite R A') ∧
      (∀ (T : Type v) [CommRing T] [Algebra R T] (φ : A →ₐ[R] T),
        I ≤ RingHom.ker (φ : A →+* T) → ∃! φ' : A' →ₐ[R] T, φ'.comp (π : A →ₐ[R] A') = φ) := by exact @_root_.P2MW.S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal_of_commRing.solution R _ A _ _ I hcomul hcounit hanti
