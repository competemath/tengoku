import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Graded.FiniteVectorGrading
import Tengoku.Seed.Data.Finset.Max
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Rigidity of shifts of finite-dimensional graded spaces -/

set_option autoImplicit false
noncomputable section
attribute [local instance] Classical.propDecidable

namespace MagnitudeConjecture.Graded.VectorGrading

variable {k M : Type*} [Field k] [AddCommGroup M] [Module k M]
variable [FiniteDimensional k M] (G : VectorGrading k M)

/-- The exact finite support of the grading.-/
def support : Finset ℤ := G.degreeSupport.filter fun i ↦ G.component i ≠ ⊥

/--
@isnad1 id=iff.0h4v.s6.daaf12aa703b from=translated src=- shape=bb1cc582 vocab=f6777347
-/
theorem mem_support_iff (i : ℤ) : i ∈ G.support ↔ G.component i ≠ ⊥ := by
  simp only [support, Finset.mem_filter]
  exact ⟨And.right, fun hi ↦ ⟨by
    by_contra hout
    exact hi (G.component_eq_bot_outside hout), hi⟩⟩

/--
@isnad1 id=nonempty.0h3v.s5.8fa3b5818c04 from=translated src=- shape=f0ddaacf vocab=9296ad0d
-/
theorem support_nonempty [Nontrivial M] : G.support.Nonempty := by
  obtain ⟨x, hx⟩ := exists_ne (0 : M)
  by_contra hn
  have hall : ∀ i, G.component i = ⊥ := by
    intro i
    by_contra hi
    exact hn ⟨i, (G.mem_support_iff i).mpr hi⟩
  have hz : ∀ i, G.projection i x = 0 := by
    intro i
    have hm := G.projection_mem i x
    rw [hall i] at hm
    exact hm
  have hs := G.sum_projection x
  simp only [hz, Finset.sum_const_zero] at hs
  exact hx hs.symm

/-- An injective homogeneous endomorphism cannot change the degree of a
nonzero finite-dimensional graded vector space.
@isnad1 id=eq.2h5v.s8.ce4f39abb834 from=translated src=- shape=f366e866 vocab=e61a6fec
-/
theorem degree_eq_zero_of_injective [Nontrivial M] (d : ℤ) (f : M →ₗ[k] M)
    (hf : Function.Injective f)
    (hdegree : ∀ i x, x ∈ G.component i → f x ∈ G.component (i + d)) : d = 0 := by
  have hshift : ∀ i ∈ G.support, i + d ∈ G.support := by
    intro i hi
    rw [G.mem_support_iff] at hi ⊢
    obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hi
    intro hz
    have hm := hdegree i x hx
    rw [hz] at hm
    exact hx0 (hf (by simpa using hm))
  have hn := G.support_nonempty
  have hlo := Finset.min'_le G.support _ (hshift _ (Finset.min'_mem G.support hn))
  have hhi := Finset.le_max' G.support _ (hshift _ (Finset.max'_mem G.support hn))
  omega

end MagnitudeConjecture.Graded.VectorGrading
