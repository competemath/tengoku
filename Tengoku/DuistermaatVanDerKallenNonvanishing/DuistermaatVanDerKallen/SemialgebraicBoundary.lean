import Tengoku.DuistermaatVanDerKallenNonvanishing.DuistermaatVanDerKallen.SemialgebraicSets
import Tengoku.Seed.Topology.Algebra.MvPolynomial
import Tengoku.Seed.Topology.Order.Basic
import Tengoku.Seed.Topology.Instances.Real.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A nonzero polynomial contains the frontier of every finite Boolean
combination of polynomial inequalities. Scalar graphs have empty interior,
so semialgebraic scalar graphs satisfy a nonzero polynomial relation.
No projection, continuity, or Hardt theorem is a premise. -/

namespace DuistermaatVanDerKallen
noncomputable section
open Set

/--
@isnad1 id=ex.1h2v.s7.4a2847e3326f from=translated src=- shape=26a2ab85 vocab=dab0bff5
-/
theorem IsSemialgebraic.frontier_polynomial {ι : Type*} {S : Set (ι → ℝ)}
    (hS : IsSemialgebraic ι S) :
    ∃ p : MvPolynomial ι ℝ, p ≠ 0 ∧ frontier S ⊆ {x | MvPolynomial.eval x p = 0} := by
  induction hS with
  | nonneg p =>
    by_cases hp : p = 0
    · refine ⟨1, one_ne_zero, ?_⟩
      simp [hp]
    · exact ⟨p, hp, fun x hx =>
        (frontier_le_subset_eq continuous_const p.continuous_eval hx).symm⟩
  | inter h₁ h₂ ih₁ ih₂ =>
    obtain ⟨p, hp, hSp⟩ := ih₁
    obtain ⟨q, hq, hSq⟩ := ih₂
    refine ⟨p * q, mul_ne_zero hp hq, ?_⟩
    intro x hx
    rcases frontier_inter_subset _ _ hx with h | h
    · change MvPolynomial.eval x (p * q) = 0
      rw [map_mul, hSp h.1, zero_mul]
    · change MvPolynomial.eval x (p * q) = 0
      rw [map_mul, hSq h.2, mul_zero]
  | union h₁ h₂ ih₁ ih₂ =>
    obtain ⟨p, hp, hSp⟩ := ih₁
    obtain ⟨q, hq, hSq⟩ := ih₂
    refine ⟨p * q, mul_ne_zero hp hq, ?_⟩
    intro x hx
    rcases frontier_union_subset _ _ hx with h | h
    · change MvPolynomial.eval x (p * q) = 0
      rw [map_mul, hSp h.1, zero_mul]
    · change MvPolynomial.eval x (p * q) = 0
      rw [map_mul, hSq h.2, mul_zero]
  | compl h ih => simpa only [frontier_compl] using ih

/--
@isnad1 id=ex.2h2v.s7.6b277b8a6c5d from=translated src=- shape=daf6e554 vocab=c3c60271
-/
theorem IsSemialgebraic.polynomial_vanishing_of_empty_interior {ι : Type*}
    {S : Set (ι → ℝ)} (hS : IsSemialgebraic ι S) (hI : interior S = ∅) :
    ∃ p : MvPolynomial ι ℝ, p ≠ 0 ∧ ∀ x ∈ S, MvPolynomial.eval x p = 0 := by
  obtain ⟨p, hp, hfront⟩ := hS.frontier_polynomial
  refine ⟨p, hp, fun x hx => hfront ?_⟩
  rw [frontier, hI, sdiff_empty]
  exact subset_closure hx

/--
@isnad1 id=eq.0h3v.s6.151843d0f634 from=translated src=- shape=675a0a4f vocab=f687569e
-/
theorem scalar_graph_empty_interior {ι : Type*} (f : (ι → ℝ) → ℝ) (S : Set (ι → ℝ)) :
    interior {q : (ι ⊕ Unit) → ℝ | (fun i => q (.inl i)) ∈ S ∧
      f (fun i => q (.inl i)) = q (.inr ())} = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro q hq
  let g : ℝ → (ι ⊕ Unit) → ℝ := fun t => Sum.elim (fun i => q (.inl i)) (fun _ => t)
  have hg : Continuous g := by
    apply continuous_pi
    intro i
    cases i with
    | inl i => exact continuous_const
    | inr i => exact continuous_id
  have hsub : g ⁻¹' interior {q : (ι ⊕ Unit) → ℝ | (fun i => q (.inl i)) ∈ S ∧
      f (fun i => q (.inl i)) = q (.inr ())} ⊆ {f (fun i => q (.inl i))} := by
    intro t ht
    exact (interior_subset ht).2.symm
  have hI := (hg.isOpen_preimage _ isOpen_interior).subset_interior_iff.mpr hsub
  have hmem : q (.inr ()) ∈ g ⁻¹' interior {q : (ι ⊕ Unit) → ℝ |
      (fun i => q (.inl i)) ∈ S ∧ f (fun i => q (.inl i)) = q (.inr ())} := by
    have he : g (q (.inr ())) = q := by
      funext i
      cases i with
      | inl i => rfl
      | inr i => cases i; rfl
    simpa only [mem_preimage, he] using hq
  simpa only [interior_singleton, mem_empty_iff_false] using hI hmem

/--
@isnad1 id=ex.1h3v.s8.d5309ccccd79 from=translated src=- shape=4b019f31 vocab=d2561960
-/
theorem semialgebraic_scalar_graph_polynomial {ι : Type*}
    (f : (ι → ℝ) → ℝ) (S : Set (ι → ℝ))
    (hf : IsSemialgebraic (ι ⊕ Unit) {q | (fun i => q (.inl i)) ∈ S ∧
      f (fun i => q (.inl i)) = q (.inr ())}) :
    ∃ p : MvPolynomial (ι ⊕ Unit) ℝ, p ≠ 0 ∧
      ∀ x ∈ S, MvPolynomial.eval (Sum.elim x (fun _ => f x)) p = 0 := by
  obtain ⟨p, hp, hv⟩ := hf.polynomial_vanishing_of_empty_interior
    (scalar_graph_empty_interior f S)
  exact ⟨p, hp, fun x hx => hv _ ⟨hx, rfl⟩⟩

end
end DuistermaatVanDerKallen
