import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quotient_span_singleton_mul_norm_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quotient_span_singleton_mul_norm_eq_one.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
attribute [-instance] NumberField.AdelicHaar.locallyCompactSpace_adeleRing NumberField.AdelicHaar.finite_residueField_adicCompletionIntegers NumberField.AdelicHaar.locallyCompactSpace_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_finiteAdeleRing NumberField.AdelicHaar.compactSpace_adicCompletionIntegers NumberField.AdelicHaar.t2Space_finiteAdeleRing NumberField.AdelicHaar.t2Space_matrix_adeleRing NumberField.AdelicHaar.t2Space_adeleRing NumberField.AdelicHaar.fact_isOpen_adicCompletionIntegers NumberField.AdelicHaar.t2Space_gl_adeleRing NumberField.AdelicHaar.locallyCompactSpace_matrix_adeleRing NumberField.AdelicHaar.t2Space_infiniteAdeleRing NumberField.AdelicHaar.properSpace_adicCompletion

set_option autoImplicit false

open NumberField IsDedekindDomain

/--
@isnad1 id=eq.1h3v.s11.e0c5d337fb9c from=translated src=- shape=65f53973 vocab=a437a11e
-/
theorem IsDedekindDomain.HeightOneSpectrum.natCard_adicCompletionIntegers_quotient_span_singleton_mul_norm_eq_one
    (K : Type) [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K))
    (a : v.adicCompletionIntegers K) (ha : a ≠ 0) :
    (Nat.card (v.adicCompletionIntegers K ⧸ Ideal.span ({a} : Set (v.adicCompletionIntegers K))) : ℝ) *
      ‖(a : v.adicCompletion K)‖ = 1 := by exact @_root_.P2MW.S_IsDedekindDomain_HeightOneSpectrum_natCard_adicCompletionIntegers_quotient_span_singleton_mul_norm_eq_one.solution K _ _ v a ha
