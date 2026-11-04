import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.CountableSemialgebraic
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.RegularJacobian
import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicMeasurable

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Uniform Euclidean Jacobian integration for C¹ semialgebraic families.
Coordinate projection remains an explicit open premise. All injective pieces
and almost-everywhere finite-fiber facts are derived. This does not identify
manifold-stratum integrals with the manuscript's complex-form densities. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set MeasureTheory MeasureTheory.Measure
open scoped ENNReal

theorem semialgebraic_domain_of_graph
    (hproj : SemialgebraicProjectionObligation)
    {ι κ ν : Type} [Finite ι] [Fintype κ] [Finite ν]
    (E : (ι → ℝ) → Set (κ → ℝ))
    (f : (ι → ℝ) → (κ → ℝ) → (ν → ℝ))
    (hgraph : IsSemialgebraic ((ι ⊕ ν) ⊕ κ) {q |
      (fun j => q (.inr j)) ∈ E (fun j => q (.inl (.inl j))) ∧
      f (fun j => q (.inl (.inl j))) (fun j => q (.inr j)) =
        (fun j => q (.inl (.inr j)))}) (a : ι → ℝ) :
    IsSemialgebraic κ (E a) := by
  let g : ((ι ⊕ ν) ⊕ κ) → MvPolynomial (κ ⊕ ν) ℝ :=
    Sum.elim (Sum.elim (fun i => MvPolynomial.C (a i))
      (fun i => MvPolynomial.X (.inr i))) (fun i => MvPolynomial.X (.inl i))
  have he (q : (κ ⊕ ν) → ℝ) : (fun j => MvPolynomial.eval q (g j)) =
      Sum.elim (Sum.elim a (fun i => q (.inr i))) (fun i => q (.inl i)) := by
    funext j
    rcases j with (i | i) | i <;> simp [g]
  have h := hgraph.polynomial_preimage g
  have hh : IsSemialgebraic (κ ⊕ ν) {q |
      (fun i => q (.inl i)) ∈ E a ∧ f a (fun i => q (.inl i)) =
        (fun i => q (.inr i))} := by
    convert h using 1
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, he]
    rfl
  have hp := hproj κ ν _ hh
  convert hp using 1
  ext x
  simp only [Set.mem_ofPred_eq, Sum.elim_inl, Sum.elim_inr]
  exact ⟨fun hx => ⟨f a x, hx, rfl⟩, fun ⟨_, hx, _⟩ => hx⟩

theorem ae_finite_semialgebraic_fibers_of_contDiffAt
    (hproj : SemialgebraicProjectionObligation)
    {ι κ : Type} [Finite ι] [Fintype κ]
    (μ : Measure (κ → ℝ)) [IsAddHaarMeasure μ]
    (E : (ι → ℝ) → Set (κ → ℝ))
    (f : (ι → ℝ) → (κ → ℝ) → (κ → ℝ))
    (D : (ι → ℝ) → (κ → ℝ) → (κ → ℝ) →L[ℝ] (κ → ℝ))
    (hgraph : IsSemialgebraic ((ι ⊕ κ) ⊕ κ) {q |
      (fun j => q (.inr j)) ∈ E (fun j => q (.inl (.inl j))) ∧
      f (fun j => q (.inl (.inl j))) (fun j => q (.inr j)) =
        (fun j => q (.inl (.inr j)))})
    (hf : ∀ a, ∀ x ∈ E a, ContDiffAt ℝ 1 (f a) x)
    (hD : ∀ a, ∀ x ∈ E a, HasFDerivAt (f a) (D a x) x) :
    ∀ a, ∀ᵐ y ∂μ, ({x | x ∈ E a ∧ f a x = y}).Finite := by
  intro a
  filter_upwards [ae_countable_fibers_of_contDiffAt μ (E a) (f a) (D a) (hf a) (hD a)]
    with y hy
  exact hgraph.finite_fiber_of_countable_of_projection hproj (Sum.elim a y) hy

end
end DuistermaatVanDerKallen
