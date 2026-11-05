import Tengoku.NsP23.P23.Artin.TraceToCentre
import Tengoku.NsP23.P23.Artin.PureTraceObstructions
import Tengoku.NsP23.P23.OneTie.DominantReduction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Direct-model H-L5

This file assembles the frozen Run-09 trace-to-geometry bridge, the frozen
Run-10 exact-family coefficient obstructions, and the Run-11 arbitrary
dominant reductions.  Every statement is internal to the finite
standard-monomial model; no polynomial-quotient or external nearly-Gorenstein
bridge is asserted.
-/

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

/-- A mixed dominant four-border configuration cannot have all three variable
basis vectors in the ordinary trace.  The coefficient calculations are the
frozen Run-10 exact-family theorems.
@isnad1 id=not.8h6v.s6.a7d78cde0979 from=translated src=- shape=e613d892 vocab=4155800b
-/
theorem mixed_dominant_four_border_not_variablesInTrace
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) {C : Normal a b c}
    (hdom : IsDominantRoot S C) (hborder : (borderFinset S).card = 4) :
    ¬VariablesInTrace k S hlive := by
  intro htrace
  rcases mixed_dominant_four_border_survivor S ha hb hc hcard hlive hanti
      hdom hborder with
    ⟨hr, hr0, hb1, hc1, hu, hv, hroots⟩ |
    ⟨hr, hc1, hu, hv, hroots⟩ |
    ⟨hr, hb1, hu, hv, hroots⟩ |
    ⟨hr, hrlast, hu, hv, huv, hroots⟩
  · subst_vars
    exact mixedYZ_y_not_mem_trace (k := k) ha hu hv htrace.2.1
  · subst_vars
    exact mixedYQ_y_not_mem_trace (k := k) ha hb hu hv hr htrace.2.1
  · subst_vars
    exact mixedZP_z_not_mem_trace (k := k) ha hc hu hv hr htrace.2.2
  · subst_vars
    exact mixedPQ_not_variablesInTrace (k := k) ha hb hc hu hv huv hlive htrace

/-- Mixed direct finite-model H-L5.
@isnad1 id=ne.7h5v.s6.34785fa0b167 from=translated src=- shape=15263f1f vocab=d4c7c949
-/
theorem mixed_directModel_HL5
    (S : Finset (Normal a b c)) (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (htrace : VariablesInTrace k S hlive) :
    (borderFinset S).card ≠ 4 := by
  intro hborder
  obtain ⟨C, _, hdom⟩ := mixed_four_border_trace_has_dominant
    (k := k) S ha hb hc hcard hlive hanti htrace hborder
  exact mixed_dominant_four_border_not_variablesInTrace
    (k := k) S ha hb hc hcard hlive hanti hdom hborder htrace

/-- Pure direct finite-model H-L5.  Dominant configurations are eliminated by
the Run-11 three-branch reduction; residual P4Z/P5Z configurations use the
frozen Run-10 obstruction API.
@isnad1 id=ne.6h4v.s6.5572d209b4de from=translated src=- shape=6931eaf4 vocab=d4c7c949
-/
theorem pure_directModel_HL5
    (S : Finset (Normal a b 0)) (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hcard : S.card = 3) (hlive : IsLiveTie S)
    (hanti : IsRootAntichain S) (htrace : VariablesInTrace k S hlive) :
    (borderFinset S).card ≠ 4 := by
  intro hborder
  rcases pure_four_border_trace_dominant_or_residual
      (k := k) S ha hb hcard hlive hanti htrace hborder with
    hdom | hresidual
  · obtain ⟨C, _, hCdom⟩ := hdom
    exact pure_dominant_border_card_ne_four_general
      S ha hb hcard hlive hanti hCdom hborder
  · rcases hresidual with
      ⟨V, ha', hb', hV, hroots⟩ | ⟨v, ha', hb', hv, hroots⟩
    · subst S
      exact p4Z_not_variablesInTrace (k := k) ha' hb' hV hlive htrace
    · subst S
      exact p5Z_not_variablesInTrace (k := k) ha' hb' hv hlive htrace

/-- Stable Run-11 summary API.-/
structure DirectModelHL5 : Prop where
  mixed : ∀ (a b c : ℕ) [NeZero a] (S : Finset (Normal a b c)),
    2 ≤ a → 1 ≤ b → 1 ≤ c → S.card = 3 →
    ∀ (hlive : IsLiveTie S), IsRootAntichain S →
      VariablesInTrace k S hlive → (borderFinset S).card ≠ 4
  pure : ∀ (a b : ℕ) [NeZero a] (S : Finset (Normal a b 0)),
    2 ≤ a → 2 ≤ b → S.card = 3 →
    ∀ (hlive : IsLiveTie S), IsRootAntichain S →
      VariablesInTrace k S hlive → (borderFinset S).card ≠ 4

/-- The direct finite standard-monomial model satisfies the mixed and pure
H-L5 conclusions.
@isnad1 id=directmo.0h1v.s3.d666badf29b8 from=translated src=- shape=c6850a32 vocab=0eed906f
-/
theorem directModel_HL5 : DirectModelHL5 (k := k) where
  mixed := by
    intro a b c _ S ha hb hc hcard hlive hanti htrace
    exact mixed_directModel_HL5 (k := k) S ha hb hc hcard hlive hanti htrace
  pure := by
    intro a b _ S ha hb hcard hlive hanti htrace
    exact pure_directModel_HL5 (k := k) S ha hb hcard hlive hanti htrace

end

end P23.Artin
