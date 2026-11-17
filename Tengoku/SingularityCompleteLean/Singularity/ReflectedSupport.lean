import Tengoku.SingularityCompleteLean.Singularity.GreenPositive
import Tengoku.SingularityCompleteLean.Singularity.GreenAdjoint

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Semigroup generation and reflection of the finite support

The reflected walk inherits positivity, normalization, and semigroup generation.
Finite generation also supplies countability of the group via its finite words.
-/

noncomputable section

namespace Singularity

variable {Γ : Type*} [Group Γ]

/-- Reflection carries a positive finite jump law to a positive finite jump law.
@isnad1 id=lt.2h4v.s6.a222dd790d97 from=translated src=- shape=42e56dc1 vocab=858f44e1
-/
theorem reflected_jump_pos (s : Finset Γ) (μ : Γ → ℝ) (hpos : ∀ g ∈ s, 0 < μ g) :
    ∀ g ∈ s.map ⟨Inv.inv, inv_injective⟩, 0 < μ g⁻¹ := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
  simpa only [Function.Embedding.coeFn_mk, inv_inv] using hpos a ha

/-- Reflection preserves total jump mass.
@isnad1 id=eq.0h3v.s5.d97107f82be7 from=translated src=- shape=a75637ae vocab=778d944b
-/
theorem reflected_jump_mass (s : Finset Γ) (μ : Γ → ℝ) :
    ∑ g ∈ s.map ⟨Inv.inv, inv_injective⟩, μ g⁻¹ = ∑ g ∈ s, μ g := by
  simp only [Finset.sum_map, Function.Embedding.coeFn_mk, inv_inv]

/-- Reflecting a semigroup-generating support still generates as a semigroup.
@isnad1 id=eq.1h2v.s6.1fa96cd39e72 from=translated src=- shape=10f13480 vocab=24a5ce71
-/
theorem reflected_support_generates (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    Submonoid.closure (s.map ⟨Inv.inv, inv_injective⟩ : Set Γ) = ⊤ := by
  have hinv : ∀ g ∈ Submonoid.closure (s : Set Γ),
      g⁻¹ ∈ Submonoid.closure (s.map ⟨Inv.inv, inv_injective⟩ : Set Γ) := by
    intro g hg
    induction hg using Submonoid.closure_induction_left with
    | one => simpa only [inv_one] using Submonoid.one_mem _
    | mul_left a ha b _ ih =>
      rw [mul_inv_rev]
      apply Submonoid.mul_mem _ ih
      exact Submonoid.subset_closure (Finset.mem_map.mpr ⟨a, ha, rfl⟩)
  apply top_unique
  intro g _
  have hg : g⁻¹ ∈ Submonoid.closure (s : Set Γ) := by rw [hgen]; trivial
  simpa only [inv_inv] using hinv g⁻¹ hg

/-- Finite semigroup generation implies countability via the finite jump words.
@isnad1 id=countabl.1h2v.s5.2a53c5836340 from=translated src=- shape=d85bca3a vocab=fe481f9b
-/
theorem countable_of_finite_jump_generation (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) : Countable Γ := by
  let f : (Σ n : ℕ, WalkWord s n) → Γ := fun p => walkEndpoint s p.1 1 p.2
  have hf : Function.Surjective f := by
    intro g
    obtain ⟨n, w, hw⟩ := exists_walkWord_between s hgen 1 g
    exact ⟨⟨n, w⟩, hw⟩
  exact hf.countable

end Singularity
