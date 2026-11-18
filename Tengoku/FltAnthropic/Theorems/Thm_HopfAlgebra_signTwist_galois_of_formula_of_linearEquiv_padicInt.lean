import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_signTwist_galois_of_formula_of_linearEquiv_padicInt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_signTwist_galois_of_formula_of_linearEquiv_padicInt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped NNReal
open scoped TensorProduct in
theorem HopfAlgebra.signTwist_galois_of_formula_of_linearEquiv_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (s : AlgebraicClosure ℚ_[p]) (hs0 : s ≠ 0)
    (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    (H' : Type) [CommRing H'] [HopfAlgebra ℤ_[p] H']
    (e : H' ≃ₗ[ℤ_[p]] H)
    (β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
         WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
    (hβ : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ (φ' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])) (h : H),
        (β φ') h = φ' (e.symm (h - Pm h)) + s⁻¹ * φ' (e.symm (Pm h))) :
    ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
      (f' g' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
      (g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
      (∀ h' : H', g' h' = σ (f' h')) →
      (∀ h : H, g h = σ ((β f') h)) →
        (σ s = s → β g' = g) ∧ (σ s ≠ s → β g' * g = 1) := by exact @_root_.P2MW.S_HopfAlgebra_signTwist_galois_of_formula_of_linearEquiv_padicInt.solution p _ hp2 d s hs0 hs H _ _ hcocomm H' _ _ e β hβ
