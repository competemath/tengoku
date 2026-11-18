import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open IsDedekindDomain NumberField

/--
@isnad1 id=and.10h4v.s14.0a8512fb031d from=translated src=- shape=790cd922 vocab=e3570b86
-/
theorem Matrix.exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori
    (p : ℕ) (hp : p.Prime) (v : HeightOneSpectrum (𝓞 ℚ)) (hpv : (p : 𝓞 ℚ) ∈ v.asIdeal)
    (Y Yi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ)) (h1 : Y * Yi = 1) (h2 : Yi * Y = 1)
    (hY : ∀ i j, Y i j ∈ v.adicCompletionIntegers ℚ) (hY10 : (p : v.adicCompletion ℚ)⁻¹ * Y 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hpYi : ∀ i j, ((p : v.adicCompletion ℚ) • Yi) i j ∈ v.adicCompletionIntegers ℚ) (hpYi10 : (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ) • Yi) 1 0 ∈ v.adicCompletionIntegers ℚ)
    (hYi : ¬ ((∀ i j, Yi i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * Yi 1 0 ∈ v.adicCompletionIntegers ℚ))
    (hpY : ¬ ((∀ i j, ((p : v.adicCompletion ℚ)⁻¹ • Y) i j ∈ v.adicCompletionIntegers ℚ) ∧ (p : v.adicCompletion ℚ)⁻¹ * ((p : v.adicCompletion ℚ)⁻¹ • Y) 1 0 ∈ v.adicCompletionIntegers ℚ)) :
    Valued.v Y.det = Valued.v (p : v.adicCompletion ℚ) ∧
    ((∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, ι i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ιi i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι' i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι'i i j ∈ v.adicCompletionIntegers ℚ) ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * ι 1 0 ∈ v.adicCompletionIntegers ℚ ∧ (p : v.adicCompletion ℚ)⁻¹ * ι' 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      Y = ι * !![(p : v.adicCompletion ℚ), 0; 0, 1] * ι') ∨
     (∃ ι ιi ι' ι'i : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, ι i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ιi i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι' i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, ι'i i j ∈ v.adicCompletionIntegers ℚ) ∧
      ι * ιi = 1 ∧ ιi * ι = 1 ∧ ι' * ι'i = 1 ∧ ι'i * ι' = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * ι 1 0 ∈ v.adicCompletionIntegers ℚ ∧ (p : v.adicCompletion ℚ)⁻¹ * ι' 1 0 ∈ v.adicCompletionIntegers ℚ ∧
      Y = ι * !![1, 0; 0, (p : v.adicCompletion ℚ)] * ι') ∨
     (∃ κ κi : Matrix (Fin 2) (Fin 2) (v.adicCompletion ℚ),
      (∀ i j, κ i j ∈ v.adicCompletionIntegers ℚ) ∧ (∀ i j, κi i j ∈ v.adicCompletionIntegers ℚ) ∧ κ * κi = 1 ∧ κi * κ = 1 ∧
      (p : v.adicCompletion ℚ)⁻¹ * κ 1 0 ∈ v.adicCompletionIntegers ℚ ∧ Y = !![0, 1; (p : v.adicCompletion ℚ), 0] * κ)) := by exact @_root_.P2MW.S_Matrix_exists_eq_iwahori_mul_diagonal_mul_iwahori_or_eq_atkinLehner_mul_of_mem_iwahori.solution p hp v hpv Y Yi h1 h2 hY hY10 hpYi hpYi10 hYi hpY
