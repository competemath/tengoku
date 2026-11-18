import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfOrderData
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_FVectStructure
import Tengoku.FltAnthropic.P2M.Sol.S_HopfOrder_exists_isGreatest

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfOrder_exists_isGreatest.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

universe u v w

open scoped TensorProduct

theorem HopfOrder.exists_isGreatest
    {R : Type*} [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [IsNoetherianRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A] [Algebra.Etale K A]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S) (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range) :
    ∃ Smax : Subalgebra R A, (Module.Finite R ↥Smax ∧ Submodule.span K (Smax : Set A) = ⊤ ∧
        (∀ x ∈ Smax, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp Smax.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp Smax.val)).range) ∧
        (∀ x ∈ Smax, HopfAlgebra.antipode K (A := A) x ∈ Smax) ∧
        (∀ x ∈ Smax, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) ∧
      ∀ T : Subalgebra R A, (Module.Finite R ↥T ∧ Submodule.span K (T : Set A) = ⊤ ∧
        (∀ x ∈ T, Coalgebra.comul (R := K) x ∈
          (Algebra.TensorProduct.productMap
            (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)
            (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp T.val)).range) ∧
        (∀ x ∈ T, HopfAlgebra.antipode K (A := A) x ∈ T) ∧
        (∀ x ∈ T, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)) → T ≤ Smax := by exact @_root_.P2MW.S_HopfOrder_exists_isGreatest.solution R _ _ _ _ K _ _ _ A _ _ _ _ _ S hfin hspan hcomul hanti hcounit
