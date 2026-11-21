import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_signTwist_antipode_mul_comul_padicInt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_signTwist_antipode_mul_comul_padicInt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct
open scoped TensorProduct in
/--
@isnad1 id=other.3h3v.s14.ef6623a59725 from=translated src=- shape=4216be81 vocab=95fd3684
-/
theorem HopfAlgebra.signTwist_antipode_mul_comul_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    let Δ' : H →ₗ[ℤ_[p]] (H ⊗[ℤ_[p]] H) :=
      Coalgebra.comul + (Ring.inverse d₀ - 1) • ((TensorProduct.map Pm Pm).comp Coalgebra.comul)
    let μ'ₗ : (H ⊗[ℤ_[p]] H) →ₗ[ℤ_[p]] H :=
      LinearMap.mul' ℤ_[p] H + (d₀ - 1) • ((LinearMap.mul' ℤ_[p] H).comp (TensorProduct.map Pm Pm))
    (μ'ₗ ∘ₗ LinearMap.rTensor H (HopfAlgebra.antipode ℤ_[p]) ∘ₗ Δ'
        = (Algebra.linearMap ℤ_[p] H) ∘ₗ Coalgebra.counit)
    ∧ (μ'ₗ ∘ₗ LinearMap.lTensor H (HopfAlgebra.antipode ℤ_[p]) ∘ₗ Δ'
        = (Algebra.linearMap ℤ_[p] H) ∘ₗ Coalgebra.counit) := by exact @_root_.P2MW.S_HopfAlgebra_signTwist_antipode_mul_comul_padicInt.solution p _ hp2 d₀ hd₀ H _ _ hcocomm
