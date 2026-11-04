import Tengoku.Seed.Analysis.Polynomial.Basic
import Tengoku.Seed.Order.Filter.AtTopBot.Basic
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A direct proof of the one-variable, quantifier-free part of Standard input
`std:sa`. Projection/quantifier elimination is deliberately not assumed. -/

open Filter
open scoped Topology

namespace DuistermaatVanDerKallen

/-- A predicate has constant truth value on some tail of the real line.-/
def EventuallyConstant (p : ℝ → Prop) : Prop :=
  (∀ᶠ x in atTop, p x) ∨ (∀ᶠ x in atTop, ¬ p x)

/-- Every polynomial inequality has constant truth value on a tail.
@isnad1 id=eventual.0h1v.s4.0163dc4e73f8 from=translated src=- shape=939ee034 vocab=c49fcf31
-/
theorem polynomial_nonneg_eventuallyConstant (p : Polynomial ℝ) :
    EventuallyConstant (fun x => 0 ≤ p.eval x) := by
  by_cases hd : 0 < p.degree
  · by_cases hc : 0 ≤ p.leadingCoeff
    · exact Or.inl ((p.tendsto_atTop_of_leadingCoeff_nonneg hd hc).eventually
        (eventually_ge_atTop 0))
    · exact Or.inr (((p.tendsto_atBot_of_leadingCoeff_nonpos hd (le_of_not_ge hc)).eventually
        (eventually_lt_atBot 0)).mono fun _ hx => not_le.mpr hx)
  · have heq := Polynomial.eq_C_of_degree_le_zero (le_of_not_gt hd)
    rw [heq]
    by_cases hc : 0 ≤ p.coeff 0
    · exact Or.inl (Eventually.of_forall fun _ => by simpa using hc)
    · exact Or.inr (Eventually.of_forall fun _ => by simpa using hc)

/-- Boolean combination of univariate polynomial weak inequalities.
Equality and strict inequality are expressible using conjunction and negation.-/
inductive PolynomialSignFormula where
  | nonneg (p : Polynomial ℝ)
  | not (p : PolynomialSignFormula)
  | and (p q : PolynomialSignFormula)

namespace PolynomialSignFormula

def Holds : PolynomialSignFormula → ℝ → Prop
  | .nonneg p, x => 0 ≤ p.eval x
  | .not p, x => ¬ p.Holds x
  | .and p q, x => p.Holds x ∧ q.Holds x

/--
@isnad1 id=eventual.0h1v.s2.f14b3b1d9eea from=translated src=- shape=76a08d12 vocab=832e05ae
-/
theorem eventuallyConstant (p : PolynomialSignFormula) : EventuallyConstant p.Holds := by
  induction p with
  | nonneg p => exact polynomial_nonneg_eventuallyConstant p
  | not p ih =>
    rcases ih with h | h
    · exact Or.inr (h.mono fun _ hx => not_not.mpr hx)
    · exact Or.inl h
  | and p q ihp ihq =>
    rcases ihp with hp | hp
    · rcases ihq with hq | hq
      · exact Or.inl (hp.and hq)
      · exact Or.inr (hq.mono fun _ hx h => hx h.2)
    · exact Or.inr (hp.mono fun _ hx h => hx h.1)

/-- The precise tail property needed for the common-radius proof, once the
existentially defined radius set has a quantifier-free polynomial description.
@isnad1 id=ex.1h1v.s5.c01181bd19b3 from=translated src=- shape=97c43d31 vocab=0f8e7f6f
-/
theorem contains_tail_of_unbounded (p : PolynomialSignFormula)
    (hunbounded : ∀ B : ℝ, ∃ x, B ≤ x ∧ p.Holds x) :
    ∃ B : ℝ, ∀ x, B ≤ x → p.Holds x := by
  rcases p.eventuallyConstant with h | h
  · exact eventually_atTop.mp h
  · obtain ⟨B, hB⟩ := eventually_atTop.mp h
    obtain ⟨x, hx, hp⟩ := hunbounded B
    exact False.elim (hB x hx hp)

end PolynomialSignFormula
end DuistermaatVanDerKallen
