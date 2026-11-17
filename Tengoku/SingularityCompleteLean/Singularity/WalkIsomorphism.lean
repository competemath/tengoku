import Tengoku.SingularityCompleteLean.Singularity.WalkTransport
import Tengoku.SingularityCompleteLean.Singularity.InvariantMeanTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transporting the hypotheses of a finite-support walk

A group isomorphism preserves positive jump weights, total mass, semigroup
generation, and nonamenability. The transported walk therefore has the required
spectral gap without an additional spectral assumption.
-/

noncomputable section
open Set
open scoped Classical

namespace Singularity

variable {Γ Λ : Type*} [Group Γ] [Group Λ]

/-- Positive jump weights remain positive on the transported finite support.
@isnad1 id=lt.2h6v.s7.f2e56f29c784 from=translated src=- shape=2d8b5df7 vocab=f7c22df5
-/
theorem mappedSupport_positive (e : Γ ≃* Λ) (s : Finset Γ) (μ : Γ → ℝ)
    (hμ : ∀ g ∈ s, 0 < μ g) :
    ∀ g ∈ s.map e.toEmbedding, 0 < (μ ∘ e.symm) g := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Finset.mem_map.mp hg
  simpa using hμ a ha

/-- Relabeling the support preserves the total jump mass.
@isnad1 id=eq.1h5v.s7.ef9031478bf0 from=translated src=- shape=db285654 vocab=17b75d9b
-/
theorem mappedSupport_mass (e : Γ ≃* Λ) (s : Finset Γ) (μ : Γ → ℝ)
    (hm : ∑ g ∈ s, μ g = 1) :
    ∑ g ∈ s.map e.toEmbedding, (μ ∘ e.symm) g = 1 := by
  simpa using hm

/-- Semigroup generation is preserved by a group isomorphism.
@isnad1 id=eq.1h4v.s7.57a6a219908b from=translated src=- shape=1059a357 vocab=9effea64
-/
theorem mappedSupport_generates (e : Γ ≃* Λ) (s : Finset Γ)
    (hgen : Submonoid.closure (s : Set Γ) = ⊤) :
    Submonoid.closure (s.map e.toEmbedding : Set Λ) = ⊤ := by
  apply top_unique
  intro y hy
  clear hy
  obtain ⟨x, rfl⟩ := e.surjective y
  have hx : x ∈ Submonoid.closure (s : Set Γ) := by rw [hgen]; trivial
  induction hx using Submonoid.closure_induction with
  | mem x hx => exact Submonoid.subset_closure (Finset.mem_map.mpr ⟨x, hx, rfl⟩)
  | one => simp
  | mul x y hx hy ihx ihy => simpa using Submonoid.mul_mem _ ihx ihy

/-- Nonamenability is unchanged by relabeling the group.
@isnad1 id=not.1h3v.s5.78a399b7bd2b from=translated src=- shape=e957f4bb vocab=63d67510
-/
theorem noInvariantMean_of_mulEquiv (e : Γ ≃* Λ) (hNA : ¬HasInvariantMean Γ) :
    ¬HasInvariantMean Λ := fun h => hNA (hasInvariantMean_of_injective e.toMonoidHom e.injective h)

end Singularity
