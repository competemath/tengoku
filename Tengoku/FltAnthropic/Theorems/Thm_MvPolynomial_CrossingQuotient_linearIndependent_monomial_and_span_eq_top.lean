import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvPolynomial_CrossingQuotient
import Tengoku.FltAnthropic.P2M.Sol.S_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open MvPolynomial MvPolynomial.CrossingQuotient
theorem MvPolynomial.CrossingQuotient.linearIndependent_monomial_and_span_eq_top
    {W : Type*} [CommRing W] (t : W) :
    LinearIndependent W (MvPolynomial.CrossingQuotient.monomial t) ∧
      Submodule.span W (Set.range (MvPolynomial.CrossingQuotient.monomial t)) = ⊤ := by exact @_root_.P2MW.S_MvPolynomial_CrossingQuotient_linearIndependent_monomial_and_span_eq_top.solution W _ t
