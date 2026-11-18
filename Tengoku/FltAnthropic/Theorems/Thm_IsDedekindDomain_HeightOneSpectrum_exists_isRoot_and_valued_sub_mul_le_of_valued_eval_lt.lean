import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
set_option autoImplicit false
open NumberField IsDedekindDomain

theorem IsDedekindDomain.HeightOneSpectrum.exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (f : Polynomial ↥(v.adicCompletionIntegers K)) (a₀ : ↥(v.adicCompletionIntegers K))
    (h : Valued.v ((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) <
      Valued.v ((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) ^ 2) :
    ∃ a : ↥(v.adicCompletionIntegers K), f.IsRoot a ∧
      Valued.v ((a : v.adicCompletion K) - (a₀ : v.adicCompletion K)) *
          Valued.v ((f.derivative.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) ≤
        Valued.v ((f.eval a₀ : ↥(v.adicCompletionIntegers K)) : v.adicCompletion K) := by exact @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_exists_isRoot_and_valued_sub_mul_le_of_valued_eval_lt.solution K _ _ v f a₀ h
