import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicSets
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.PolynomialTail

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! The univariate tail property for the finite Boolean semialgebraic definition.
Polynomial curves are handled directly; no projection theorem is used. -/

namespace DuistermaatVanDerKallen
open Filter
noncomputable section

/--
@isnad1 id=eq.0h4v.s6.30336403aa45 from=translated src=- shape=cff23680 vocab=8880e25e
-/
theorem polynomial_curve_eval {ι : Type*} (p : MvPolynomial ι ℝ)
    (g : ι → Polynomial ℝ) (t : ℝ) :
    (MvPolynomial.eval₂ Polynomial.C g p).eval t =
      MvPolynomial.eval (fun i => (g i).eval t) p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [MvPolynomial.eval₂_add, hp, hq]
  | mul_X p i hp => simp [MvPolynomial.eval₂_mul, hp]

/--
@isnad1 id=eventual.1h3v.s5.bff0d4fb3cf8 from=translated src=- shape=4befacb5 vocab=bfb7c7a5
-/
theorem IsSemialgebraic.eventuallyConstant_polynomial_curve {ι : Type*}
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) (g : ι → Polynomial ℝ) :
    EventuallyConstant (fun t => (fun i => (g i).eval t) ∈ S) := by
  induction hS with
  | nonneg p =>
    simpa only [polynomial_curve_eval, Set.mem_ofPred_eq] using
      polynomial_nonneg_eventuallyConstant (MvPolynomial.eval₂ Polynomial.C g p)
  | inter _ _ ih₁ ih₂ =>
    rcases ih₁ with h₁ | h₁
    · rcases ih₂ with h₂ | h₂
      · exact Or.inl (h₁.and h₂)
      · exact Or.inr (h₂.mono fun t ht h => ht h.2)
    · exact Or.inr (h₁.mono fun t ht h => ht h.1)
  | union _ _ ih₁ ih₂ =>
    rcases ih₁ with h₁ | h₁
    · exact Or.inl (h₁.mono fun t ht => Or.inl ht)
    · rcases ih₂ with h₂ | h₂
      · exact Or.inl (h₂.mono fun t ht => Or.inr ht)
      · exact Or.inr ((h₁.and h₂).mono fun t ht h => h.elim ht.1 ht.2)
  | compl _ ih =>
    rcases ih with h | h
    · exact Or.inr (h.mono fun t ht hnot => hnot ht)
    · exact Or.inl h

/--
@isnad1 id=ex.2h1v.s6.38bf1df634e0 from=translated src=- shape=3750c27d vocab=72e7d624
-/
theorem IsSemialgebraic.contains_tail_of_unbounded {S : Set (Fin 1 → ℝ)}
    (hS : IsSemialgebraic (Fin 1) S)
    (hU : ∀ B : ℝ, ∃ t, B ≤ t ∧ (fun _ : Fin 1 => t) ∈ S) :
    ∃ B : ℝ, ∀ t, B ≤ t → (fun _ : Fin 1 => t) ∈ S := by
  have h := hS.eventuallyConstant_polynomial_curve (fun _ => Polynomial.X)
  simp only [Polynomial.eval_X] at h
  rcases h with h | h
  · exact eventually_atTop.mp h
  · obtain ⟨B, hB⟩ := eventually_atTop.mp h
    obtain ⟨t, ht, htS⟩ := hU B
    exact False.elim (hB t ht htS)

end
end DuistermaatVanDerKallen
