import Tengoku.Seed.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Tengoku.Seed.NumberTheory.ModularForms.EisensteinSeries.Basic
import Tengoku.Seed.NumberTheory.ModularForms.Discriminant
import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups
import Tengoku.Seed.FieldTheory.IntermediateField.Basic
import Tengoku.FltAnthropic.P2M.Sol.S_WLight_qExpansion_sigmaTransport_package

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WLight_qExpansion_sigmaTransport_package.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false
open Complex Real UpperHalfPlane
open scoped Manifold MatrixGroups ModularForm

theorem WLight.qExpansion_sigmaTransport_package (N : ℕ) [NeZero N]
    (K : IntermediateField ℚ ℂ) (φ : ↥K →+* ℂ) (hφK : ∀ z : ↥K, φ z ∈ K)
    (T : (ℍ → ℂ) → (ℍ → ℂ) → Prop)
    (hT : ∀ g g' : ℍ → ℂ, T g g' ↔
        (MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g ∧ MDifferentiable 𝓘(ℂ) 𝓘(ℂ) g' ∧
          ∃ m : ℕ,
            (Function.Periodic ((g * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
              IsBoundedAtImInfty (g * ModularForm.discriminant ^ m) ∧
              ∀ n : ℕ,
                (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
            (Function.Periodic ((g' * ModularForm.discriminant ^ m) ∘ UpperHalfPlane.ofComplex) N ∧
              IsBoundedAtImInfty (g' * ModularForm.discriminant ^ m) ∧
              ∀ n : ℕ,
                (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n ∈ K) ∧
            ∀ (n : ℕ) (z : ↥K),
              (z : ℂ) = (UpperHalfPlane.qExpansion N (g * ModularForm.discriminant ^ m)).coeff n →
              (UpperHalfPlane.qExpansion N (g' * ModularForm.discriminant ^ m)).coeff n = φ z)) :
    (∀ {ι : Type} (g g' : ι → ℍ → ℂ), (∀ i : ι, T (g i) (g' i)) → ∀ R : MvPolynomial ι ↥K,
        T (MvPolynomial.aeval g (MvPolynomial.map (algebraMap ↥K ℂ) R))
          (MvPolynomial.aeval g' (MvPolynomial.map φ R))) ∧
    (∀ g g' : ℍ → ℂ, T g g' → (g = 0 ↔ g' = 0)) ∧
    ∀ jf : ℍ → ℂ, (∀ τ : ℍ, jf τ = ModularForm.E₄ τ ^ 3 / ModularForm.discriminant τ) → T jf jf := by exact @_root_.P2MW.S_WLight_qExpansion_sigmaTransport_package.solution N _ K φ hφK T hT
