import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

theorem AutomorphicForm.LocalFunctionSpace.eq_of_forall_exists_forall_sum_char_mul_eq_zero
    (p : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ))
    (f : p.adicCompletion ℚ → ℂ)
    (hf : ∃ δ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x y : p.adicCompletion ℚ, Valued.v (x - y) < (δ : WithZero (Multiplicative ℤ)) → f x = f y)
    (χ : p.adicCompletion ℚ → ℂ)
    (hχ : ∀ x y : p.adicCompletion ℚ, χ (x + y) = χ x * χ y)
    (hχ₁ : ∃ γ₀ : (WithZero (Multiplicative ℤ))ˣ,
      ∀ x : p.adicCompletion ℚ, Valued.v x < (γ₀ : WithZero (Multiplicative ℤ)) → χ x = 1)
    (hχ₂ : ∃ x₀ : p.adicCompletion ℚ, χ x₀ ≠ 1)
    (hsum : ∀ a : p.adicCompletion ℚ, a ≠ 0 →
      ∃ β₀ : (WithZero (Multiplicative ℤ))ˣ, ∀ β : (WithZero (Multiplicative ℤ))ˣ, β₀ ≤ β →
      ∃ δ : (WithZero (Multiplicative ℤ))ˣ, ∀ T : Finset (p.adicCompletion ℚ),
        (∀ t ∈ T, Valued.v t < (β : WithZero (Multiplicative ℤ))) →
        (∀ x : p.adicCompletion ℚ, Valued.v x < (β : WithZero (Multiplicative ℤ)) →
          ∃! t, t ∈ T ∧ Valued.v (x - t) < (δ : WithZero (Multiplicative ℤ))) →
        ∑ t ∈ T, χ (-(a * t)) * f t = 0) :
    ∀ x y : p.adicCompletion ℚ, f x = f y := by exact @_root_.P2MW.S_AutomorphicForm_LocalFunctionSpace_eq_of_forall_exists_forall_sum_char_mul_eq_zero.solution p f hf χ hχ hχ₁ hχ₂ hsum
