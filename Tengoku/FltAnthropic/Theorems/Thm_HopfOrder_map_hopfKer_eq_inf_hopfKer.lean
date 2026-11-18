import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKer
import Tengoku.FltAnthropic.P2M.Sol.S_HopfOrder_map_hopfKer_eq_inf_hopfKer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfOrder_map_hopfKer_eq_inf_hopfKer.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct
theorem HopfOrder.map_hopfKer_eq_inf_hopfKer
    {R : Type*} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
    {A : Type*} [CommRing A] [HopfAlgebra K A] [Algebra R A] [IsScalarTower R K A]
    {Ā : Type*} [CommRing Ā] [HopfAlgebra K Ā] [Algebra R Ā] [IsScalarTower R K Ā]
    (S : Subalgebra R A)
    {H : Type*} [CommRing H] [HopfAlgebra R H] [Module.Free R H]
    (e : H →ₐ[R] A) (he : Function.Injective e) (heS : e.range = S)
    (he_comul : ∀ h : H, Coalgebra.comul (R := K) (e h) =
        Algebra.TensorProduct.productMap
          (((Algebra.TensorProduct.includeLeft : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
          (((Algebra.TensorProduct.includeRight : A →ₐ[K] A ⊗[K] A).restrictScalars R).comp e)
          (Coalgebra.comul (R := R) h))
    (π : A →ₐc[K] Ā)
    {Hbar : Type*} [CommRing Hbar] [HopfAlgebra R Hbar] [Module.Free R Hbar]
    (q : H →ₐc[R] Hbar) (ebar : Hbar →ₐ[R] Ā) (hebar : Function.Injective ebar)
    (hsq : ∀ h : H, ebar (q h) = π (e h)) :
    (HopfAlgebra.hopfKer q).map e = S ⊓ (HopfAlgebra.hopfKer π).restrictScalars R := by exact @_root_.P2MW.S_HopfOrder_map_hopfKer_eq_inf_hopfKer.solution R _ _ _ K _ _ _ A _ _ _ _ Ā _ _ _ _ S H _ _ _ e he heS he_comul π Hbar _ _ _ q ebar hebar hsq
