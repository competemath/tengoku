import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open Complex in

/--
@isnad1 id=eq.11h7v.s11.3bde7f075542 from=translated src=- shape=12bda2ff vocab=4fbfeff0
-/
theorem Complex.integral_radial_loop_eq_two_mul_I_mul_setIntegral
    (c : ℂ) (r : ℝ → ℝ) (hcont : Continuous r) (hper : Function.Periodic r (2 * Real.pi))
    (hpos : ∀ φ, 0 < r φ)
    (N : ℕ) (φs : Fin (N + 1) → ℝ) (hφ0 : φs 0 = 0) (hφN : φs (Fin.last N) = 2 * Real.pi)
    (hmono : StrictMono φs)
    (hC2 : ∀ i : Fin N, ContDiffOn ℝ 2 r (Set.Icc (φs i.castSucc) (φs i.succ)))
    (P Q : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hKU : ∀ z : ℂ, ‖z - c‖ ≤ r (arg (z - c)) → z ∈ U)
    (hP : ContDiffOn ℝ 1 P U) (hQ : ContDiffOn ℝ 1 Q U) :
    ∫ φ in (0 : ℝ)..(2 * Real.pi),
        (P (c + r φ * exp (φ * I)) * ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I)) +
          Q (c + r φ * exp (φ * I)) *
            (starRingEnd ℂ) ((((deriv r φ : ℝ) : ℂ) + r φ * I) * exp (φ * I))) =
      2 * I * ∫ z in {z : ℂ | ‖z - c‖ ≤ r (arg (z - c))},
        ((fderiv ℝ P z 1 + I * fderiv ℝ P z I) / 2 - (fderiv ℝ Q z 1 - I * fderiv ℝ Q z I) / 2) := by exact @_root_.P2MW.S_Complex_integral_radial_loop_eq_two_mul_I_mul_setIntegral.solution c r hcont hper hpos N φs hφ0 hφN hmono hC2 P Q U hU hKU hP hQ
