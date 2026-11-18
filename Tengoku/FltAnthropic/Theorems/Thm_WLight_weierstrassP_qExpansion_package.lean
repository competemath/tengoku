import Tengoku.Seed.Analysis.SpecialFunctions.Elliptic.Weierstrass
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Manifold
import Tengoku.Seed.Analysis.Complex.IntegerCompl
import Tengoku.Seed.Geometry.Manifold.Notation
import Tengoku.FltAnthropic.P2M.Sol.S_WLight_weierstrassP_qExpansion_package

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_WLight_weierstrassP_qExpansion_package.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Complex Real
open scoped UpperHalfPlane Manifold

/--
@isnad1 id=and.0h0v.s11.dad55f79aa7a from=translated src=- shape=ff423620 vocab=dfc2be99
-/
theorem WLight.weierstrassP_qExpansion_package :

    (∀ w : ℂ, 0 < w.im →
      ∑' n : ℤ, 1 / (w + n) ^ 2 =
        (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (2 * π * I * w) ^ m) ∧

    (∀ w : ℂ, w.im < 0 →
      ∑' n : ℤ, 1 / (w + n) ^ 2 =
        (2 * π * I) ^ 2 * ∑' m : ℕ, (m : ℂ) * cexp (-(2 * π * I * w)) ^ m) ∧

    (∀ z τ : ℂ, -τ.im < z.im → z.im < τ.im → z ∈ Complex.integerComplement →
      ∑' c : ℤ, ((∑' d : ℤ, 1 / ((z - c * τ) + d) ^ 2) - ∑' d : ℤ, 1 / (c * τ + d) ^ 2) =
        (2 * π * I) ^ 2 *
          (cexp (2 * π * I * z) / (1 - cexp (2 * π * I * z)) ^ 2 + 1 / 12 +
            ∑' c : ℕ+, ∑' m : ℕ, (m : ℂ) *
              (cexp (2 * π * I * z) ^ m + (cexp (2 * π * I * z))⁻¹ ^ m - 2) *
                cexp (2 * π * I * τ) ^ ((c : ℕ) * m))) ∧

    (∀ L : ℍ → PeriodPair, (∀ τ : ℍ, (L τ).ω₁ = (τ : ℂ) ∧ (L τ).ω₂ = 1) →
      ∀ N a₁ a₂ : ℕ, a₁ < N → a₂ < N → (a₁ ≠ 0 ∨ a₂ ≠ 0) →
        (∀ τ : ℍ, PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * τ + a₂) / N) =
          (2 * π * I) ^ 2 *
            (cexp (2 * π * I / N) ^ a₂ * cexp (2 * π * I * (τ : ℂ) / N) ^ a₁ /
                (1 - cexp (2 * π * I / N) ^ a₂ * cexp (2 * π * I * (τ : ℂ) / N) ^ a₁) ^ 2 +
              1 / 12 +
              ∑' p : ℕ+ × ℕ+, ((p.2 : ℕ) : ℂ) *
                (cexp (2 * π * I / N) ^ (a₂ * (p.2 : ℕ)) *
                    cexp (2 * π * I * (τ : ℂ) / N) ^ (((p.1 : ℕ) * N + a₁) * (p.2 : ℕ)) +
                  (cexp (2 * π * I / N))⁻¹ ^ (a₂ * (p.2 : ℕ)) *
                    cexp (2 * π * I * (τ : ℂ) / N) ^ (((p.1 : ℕ) * N - a₁) * (p.2 : ℕ)) -
                  2 * cexp (2 * π * I * (τ : ℂ) / N) ^ ((p.1 : ℕ) * N * (p.2 : ℕ))))) ∧
        MDifferentiable 𝓘(ℂ) 𝓘(ℂ)
          (fun τ : ℍ => PeriodPair.weierstrassP (L τ) (((a₁ : ℂ) * τ + a₂) / N))) ∧

    (∀ L L' : PeriodPair, ∀ c : ℂ, L'.ω₁ = c * L.ω₁ → L'.ω₂ = c * L.ω₂ →
      ∀ z : ℂ, PeriodPair.weierstrassP L' (c * z) =
        c⁻¹ ^ 2 * PeriodPair.weierstrassP L z) := by exact @_root_.P2MW.S_WLight_weierstrassP_qExpansion_package.solution
