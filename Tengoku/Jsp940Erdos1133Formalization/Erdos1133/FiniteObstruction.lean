import Tengoku.Jsp940Erdos1133Formalization.Erdos1133.PolynomialPullback

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section
open Set
namespace Erdos1133

/-- The sole analytic input to the grouping reduction. All indexed nodes,
including repetitions, and all entire interpolants are quantified here.-/
def FiniteBernsteinObstruction (H : ℝ) (k : ℕ) : Prop :=
  ∀ (t : Fin k → ℝ) (a : ℝ),
    (∀ i, t i ∈ Icc a (a + (k : ℝ) + 1)) →
    ∃ y : Fin k → Icc (-1 : ℝ) 1,
      ∀ f : ℂ → ℂ, IsBernsteinFunction Real.pi H f →
        ∃ i, f (t i) ≠ ((y i : ℝ) : ℂ)

theorem finiteObstruction_group {H : ℝ} {k : ℕ}
    (h : FiniteBernsteinObstruction H k)
    {α : Type*} [DecidableEq α] (g : Finset α) (hg : g.card = k)
    (t : α → ℝ) (a : ℝ) (ht : ∀ i ∈ g, t i ∈ Icc a (a + (k : ℝ) + 1)) :
    ∃ y : α → ℝ, (∀ i, |y i| ≤ 1) ∧
      ∀ f : ℂ → ℂ, IsBernsteinFunction Real.pi H f →
        ∃ i ∈ g, f (t i) ≠ (y i : ℂ) := by
  classical
  let e : Fin k ≃ g := (Fintype.equivFinOfCardEq (by simpa using hg)).symm
  obtain ⟨v, hv⟩ := h (fun j => t (e j)) a (fun j => ht _ (e j).property)
  let y : α → ℝ := fun i => if hi : i ∈ g then (v (e.symm ⟨i, hi⟩) : ℝ) else 0
  refine ⟨y, ?_, ?_⟩
  · intro i
    by_cases hi : i ∈ g
    · dsimp [y]
      rw [dite_eq_left hi, abs_le]
      exact (v (e.symm ⟨i, hi⟩)).property
    · simp [y, hi]
  · intro f hf
    obtain ⟨j, hj⟩ := hv f hf
    refine ⟨e j, (e j).property, ?_⟩
    simpa [y] using hj

end Erdos1133
