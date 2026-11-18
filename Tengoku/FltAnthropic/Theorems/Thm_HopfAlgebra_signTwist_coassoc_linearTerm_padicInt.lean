import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct
open scoped TensorProduct in
theorem HopfAlgebra.signTwist_coassoc_linearTerm_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d₀ : ℤ_[p]) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H) :
    let Pm : H →ₗ[ℤ_[p]] H :=
      Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
    let Q := TensorProduct.map Pm Pm
    let Δ : H →ₗ[ℤ_[p]] H ⊗[ℤ_[p]] H := Coalgebra.comul
    let A := (TensorProduct.assoc ℤ_[p] H H H).toLinearMap
    ∀ a : H,
      A ((LinearMap.rTensor H (Q.comp Δ)) (Δ a)) + A ((LinearMap.rTensor H Δ) (Q (Δ a)))
      = (LinearMap.lTensor H (Q.comp Δ)) (Δ a) + (LinearMap.lTensor H Δ) (Q (Δ a)) := by exact @_root_.P2MW.S_HopfAlgebra_signTwist_coassoc_linearTerm_padicInt.solution p _ hp2 d₀ hd₀ H _ _ hcocomm
