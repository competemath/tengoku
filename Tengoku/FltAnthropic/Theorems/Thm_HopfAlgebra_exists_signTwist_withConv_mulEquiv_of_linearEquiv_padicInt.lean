import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped NNReal
open scoped TensorProduct in
/--
@isnad1 id=ex.15h9v.s15.89cc0302cc4d from=translated src=- shape=de9393e9 vocab=e7d11a05
-/
theorem HopfAlgebra.exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (d : ℚ_[p]) (hd : ‖d‖₊ = 1) (hd_nsq : ¬ IsSquare d)
    (s : AlgebraicClosure ℚ_[p]) (hs : s ^ 2 = algebraMap ℚ_[p] (AlgebraicClosure ℚ_[p]) d)
    (d₀ : ℤ_[p]) (hd₀d : (d₀ : ℚ_[p]) = d) (hd₀ : IsUnit d₀)
    (H : Type) [CommRing H] [HopfAlgebra ℤ_[p] H]
    (hfin : Module.Finite ℤ_[p] H) (hflat : Module.Flat ℤ_[p] H)
    (hcocomm : Coalgebra.IsCocomm ℤ_[p] H)
    (H' : Type) [CommRing H'] [HopfAlgebra ℤ_[p] H']
    (hfin' : Module.Finite ℤ_[p] H') (hflat' : Module.Flat ℤ_[p] H')
    (hcocomm' : Coalgebra.IsCocomm ℤ_[p] H')
    (e : H' ≃ₗ[ℤ_[p]] H)
    (he1 : e 1 = 1)
    (hemul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a b : H', e (a * b) = e a * e b + (d₀ - 1) • (Pm (e a) * Pm (e b)))
    (hecounit : ∀ a : H', (Coalgebra.counit (e a) : ℤ_[p]) = Coalgebra.counit a)
    (heant : ∀ a : H', e (HopfAlgebra.antipode ℤ_[p] a) = HopfAlgebra.antipode ℤ_[p] (e a))
    (hecomul : let Pm : H →ₗ[ℤ_[p]] H :=
        Ring.inverse (2:ℤ_[p]) • (LinearMap.id - HopfAlgebra.antipode ℤ_[p])
      ∀ a : H', (TensorProduct.map (e : H' →ₗ[ℤ_[p]] H) (e : H' →ₗ[ℤ_[p]] H))
                  (Coalgebra.comul a)
            = Coalgebra.comul (e a)
              + (Ring.inverse d₀ - 1) •
                  (TensorProduct.map Pm Pm) (Coalgebra.comul (e a))) :
    ∃ β : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]) ≃
          WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]),
      (∀ f' g', β (f' * g') = β f' * β g') ∧
      ∀ (σ : AlgebraicClosure ℚ_[p] ≃ₐ[ℚ_[p]] AlgebraicClosure ℚ_[p])
        (f' g' : WithConv (H' →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p]))
        (g : WithConv (H →ₐ[ℤ_[p]] AlgebraicClosure ℚ_[p])),
        (∀ h' : H', g' h' = σ (f' h')) →
        (∀ h : H, g h = σ ((β f') h)) →
          (σ s = s → β g' = g) ∧ (σ s ≠ s → β g' * g = 1) := by exact @_root_.P2MW.S_HopfAlgebra_exists_signTwist_withConv_mulEquiv_of_linearEquiv_padicInt.solution p _ hp2 d hd hd_nsq s hs d₀ hd₀d hd₀ H _ _ hfin hflat hcocomm H' _ _ hfin' hflat' hcocomm' e he1 hemul hecounit heant hecomul
