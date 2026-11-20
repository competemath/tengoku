import Tengoku.Hellingerrepolean4.Hellinger.AllBent
import Tengoku.Hellingerrepolean4.Hellinger.AllQuadratic
import Tengoku.Hellingerrepolean4.Hellinger.EntropyTransfer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The complete information bounds for flat Boolean spectra and quadratic
phases, with strictness and equality. Probability-model identification is
kept separate from this finite entropy calculation. -/

set_option autoImplicit false
noncomputable section

namespace Hellinger.ClassInformation

/--
@isnad1 id=isboolea.1h2v.s3.cc812963b972 from=translated src=- shape=08c32349 vocab=43e87195
-/
theorem quadratic_isBoolean {n : ℕ} {f : PaperSpecs.Cube n → ℝ}
    (hf : PaperSpecs.IsQuadratic f) : PaperSpecs.IsBoolean f := by
  obtain ⟨a, b, q, h⟩ := hf
  intro x
  rw [h x]
  split_ifs <;> simp

/--
@isnad1 id=bentinfo.0h0v.s0.df139794b555 from=translated src=- shape=45709ebd vocab=df139794
-/
theorem bent_information : PaperSpecs.BentInformation := by
  intro n hn f hf hb ρ hρ
  obtain ⟨hH, hs⟩ := AllBent.paper_bent_hellinger n hn f hf hb ρ hρ
  exact ⟨EntropyTransfer.hellinger_implies_ck f hf ρ hρ hH,
    fun hp => EntropyTransfer.strict_hellinger_implies_strict_ck f hf ρ hρ (hs hp)⟩

/--
@isnad1 id=quadrati.0h0v.s0.9252165d413f from=translated src=- shape=45709ebd vocab=9252165d
-/
theorem quadratic_information : PaperSpecs.QuadraticInformation := by
  intro n hn f hq ρ hρ
  have hf := quadratic_isBoolean hq
  obtain ⟨hH, heq⟩ := AllQuadratic.paper_quadratic_hellinger n hn f hq ρ hρ
  refine ⟨EntropyTransfer.hellinger_implies_ck f hf ρ hρ hH, ?_⟩
  intro hp hl
  constructor
  · intro hI
    exact (heq hp hl).mp
      (EntropyTransfer.ck_equality_implies_hellinger_equality f hf ρ hρ hH hI)
  · rintro ⟨i, _, negative, hform⟩
    rw [hform]
    exact EntropyTransfer.signed_dictator_information n i negative ρ hρ

end Hellinger.ClassInformation
