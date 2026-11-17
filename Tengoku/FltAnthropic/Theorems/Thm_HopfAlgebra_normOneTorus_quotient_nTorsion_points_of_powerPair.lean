import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_Flat
import Tengoku.FltAnthropic.P2M.Sol.S_HopfAlgebra_normOneTorus_quotient_nTorsion_points_of_powerPair

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_HopfAlgebra_normOneTorus_quotient_nTorsion_points_of_powerPair.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open scoped TensorProduct in
theorem HopfAlgebra.normOneTorus_quotient_nTorsion_points_of_powerPair
    (K : Type) [Field K] [CharZero K] (c : K) (hc : c ≠ 0)
    (n : ℕ) [Fact n.Prime]
    (δ : AlgebraicClosure K) (hδ : δ * δ = algebraMap K (AlgebraicClosure K) c)
    (B₀ : Type) [CommRing B₀] [Algebra K B₀]
    (u₀ v₀ P Q : B₀)
    (hlift₀ : ∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      ∃! g : B₀ →ₐ[K] AlgebraicClosure K, g u₀ = w ∧ g v₀ = z)
    (hpow : ∀ f : B₀ →ₐ[K] AlgebraicClosure K,
      f P + f Q * δ = (f u₀ + f v₀ * δ) ^ n ∧
      f P - f Q * δ = (f u₀ - f v₀ * δ) ^ n)
    (A : Type) [CommRing A] [Algebra K A]
    (u' v' : A) (π : B₀ →ₐ[K] A)
    (hπu : π u₀ = u') (hπv : π v₀ = v') (hπP : π P = 1) (hπQ : π Q = 0)
    (hfact : ∀ g : B₀ →ₐ[K] AlgebraicClosure K, g P = 1 → g Q = 0 →
      ∃ f : A →ₐ[K] AlgebraicClosure K, f.comp π = g)
    (hgen' : Algebra.adjoin K {u', v'} = ⊤) :
    (∀ f : A →ₐ[K] AlgebraicClosure K, (f u' + f v' * δ) ^ n = 1) ∧
    (∀ (w z : AlgebraicClosure K),
      w ^ 2 - algebraMap K (AlgebraicClosure K) c * z ^ 2 = 1 →
      (w + z * δ) ^ n = 1 →
      ∃! f : A →ₐ[K] AlgebraicClosure K, f u' = w ∧ f v' = z) := by exact @_root_.P2MW.S_HopfAlgebra_normOneTorus_quotient_nTorsion_points_of_powerPair.solution K _ _ c hc n _ δ hδ B₀ _ _ u₀ v₀ P Q hlift₀ hpow A _ _ u' v' π hπu hπv hπP hπQ hfact hgen'
