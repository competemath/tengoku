import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfOrder_isHopfOrder_map

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfOrder_isHopfOrder_map.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct
theorem HopfOrder.isHopfOrder_map
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    (S : Subalgebra R A)
    (hfin : Module.Finite R ↥S)
    (hspan : Submodule.span K (S : Set A) = ⊤)
    (hcomul : ∀ x ∈ S, Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp S.val)).range)
    (hanti : ∀ x ∈ S, HopfAlgebra.antipode K (A := A) x ∈ S)
    (hcounit : ∀ x ∈ S, Coalgebra.counit (R := K) (A := A) x ∈ (algebraMap R K).range)
    (π : A →ₐc[K] Ā) (hπ : Function.Surjective π) :
    Module.Finite R ↥((S.map ((π : A →ₐ[K] Ā).restrictScalars R))) ∧
    Submodule.span K (((S.map ((π : A →ₐ[K] Ā).restrictScalars R)) : Subalgebra R Ā) : Set Ā) = ⊤ ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), Coalgebra.comul (R := K) x ∈
        (Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : Ā →ₐ[K] Ā ⊗[K] Ā).restrictScalars R).comp ((S.map ((π : A →ₐ[K] Ā).restrictScalars R))).val)
          (((Algebra.TensorProduct.includeRight : Ā →ₐ[K] Ā ⊗[K] Ā).restrictScalars R).comp ((S.map ((π : A →ₐ[K] Ā).restrictScalars R))).val)).range) ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), HopfAlgebra.antipode K (A := Ā) x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R))) ∧
    (∀ x ∈ (S.map ((π : A →ₐ[K] Ā).restrictScalars R)), Coalgebra.counit (R := K) (A := Ā) x ∈ (algebraMap R K).range) := by exact @_root_.P2MW.S_HopfOrder_isHopfOrder_map.solution R _ _ _ K _ _ _ A _ _ _ _ Ā _ _ _ _ S hfin hspan hcomul hanti hcounit π hπ
