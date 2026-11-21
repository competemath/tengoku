import Tengoku.RainichKaluzaReconstruction.RainichKaluza.RankOneEndomorphism
import Tengoku.Seed.LinearAlgebra.LinearIndependent.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Protected eigendirections under a rank-one perturbation

Let `S` be an endomorphism and let `V = x ⊗ f` have rank at most one.  If an
eigenspace of `S` contains two linearly independent vectors, then the
restriction of `f` to that eigenspace has a nontrivial kernel.  Consequently
`S + V` retains a nonzero eigenvector with the same eigenvalue.

For a four-dimensional non-null Maxwell stress endomorphism, the `+q` and
`-q` principal eigenspaces are both two-dimensional.  Applying the theorem to
both planes explains, without choosing a basis, why adding the scalar
rank-one Ricci contribution protects an opposite eigenvalue pair.  The
Maxwell principal-plane multiplicity statement is a separate exterior-algebra
input and is not proved in this file.
-/

namespace RainichKaluza

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

/-- A linear combination of two vectors which is always annihilated by `f`.
It may vanish; linear independence supplies a nonzero alternative in the
theorem below.-/
def kernelCombination (f : E →ₗ[ℝ] ℝ) (y₁ y₂ : E) : E :=
  f y₂ • y₁ - f y₁ • y₂

@[simp]
theorem kernelCombination_mem_ker
    (f : E →ₗ[ℝ] ℝ) (y₁ y₂ : E) :
    f (kernelCombination f y₁ y₂) = 0 := by
  simp [kernelCombination]
  ring

/-- Every two-dimensional vector plane contains a nonzero vector annihilated
by a given covector.  This is the elementary dimension mechanism behind the
protected-eigenvalue result.-/
theorem exists_nonzero_kernelVector_of_pair
    (f : E →ₗ[ℝ] ℝ) (y₁ y₂ : E)
    (hlin : LinearIndependent ℝ ![y₁, y₂]) :
    ∃ y : E, y ≠ 0 ∧ f y = 0 := by
  by_cases h₁ : f y₁ = 0
  · exact ⟨y₁, hlin.ne_zero 0, h₁⟩
  · refine ⟨kernelCombination f y₁ y₂, ?_, kernelCombination_mem_ker f y₁ y₂⟩
    intro hzero
    have hcoeff := (LinearIndependent.pair_iff.mp hlin)
      (f y₂) (-f y₁) (by
        simpa [kernelCombination, sub_eq_add_neg] using hzero)
    exact h₁ (neg_eq_zero.mp hcoeff.2)

/-- **Protected eigendirection theorem.** A rank-one perturbation cannot remove
an eigenvalue whose eigenspace contains two linearly independent vectors.-/
theorem exists_protected_eigenvector_of_pair
    (S : Module.End ℝ E) (f : E →ₗ[ℝ] ℝ) (x : E)
    (lambda : ℝ) (y₁ y₂ : E)
    (hlin : LinearIndependent ℝ ![y₁, y₂])
    (hy₁ : S y₁ = lambda • y₁)
    (hy₂ : S y₂ = lambda • y₂) :
    ∃ y : E, y ≠ 0 ∧
      (S + rankOneEndomorphism f x) y = lambda • y := by
  by_cases h₁ : f y₁ = 0
  · refine ⟨y₁, hlin.ne_zero 0, ?_⟩
    simp [hy₁, h₁]
  · let y := kernelCombination f y₁ y₂
    have hfy : f y = 0 := kernelCombination_mem_ker f y₁ y₂
    have hy_ne : y ≠ 0 := by
      intro hzero
      have hcoeff := (LinearIndependent.pair_iff.mp hlin)
        (f y₂) (-f y₁) (by
          simpa [y, kernelCombination, sub_eq_add_neg] using hzero)
      exact h₁ (neg_eq_zero.mp hcoeff.2)
    refine ⟨y, hy_ne, ?_⟩
    calc
      (S + rankOneEndomorphism f x) y = S y := by simp [hfy]
      _ = lambda • y := by
        simp [y, kernelCombination, hy₁, hy₂, smul_sub, smul_smul, mul_comm]

/-- **Protected opposite-pair theorem.** If `S` has two-dimensional principal
eigenplanes with eigenvalues `+q` and `-q`, then adding any rank-one
endomorphism retains a nonzero eigenvector in each plane.-/
theorem exists_protected_opposite_eigenvectors
    (S : Module.End ℝ E) (f : E →ₗ[ℝ] ℝ) (x : E) (q : ℝ)
    (p₁ p₂ m₁ m₂ : E)
    (hp : LinearIndependent ℝ ![p₁, p₂])
    (hm : LinearIndependent ℝ ![m₁, m₂])
    (hp₁ : S p₁ = q • p₁) (hp₂ : S p₂ = q • p₂)
    (hm₁ : S m₁ = (-q) • m₁) (hm₂ : S m₂ = (-q) • m₂) :
    (∃ p : E, p ≠ 0 ∧
      (S + rankOneEndomorphism f x) p = q • p) ∧
    (∃ m : E, m ≠ 0 ∧
      (S + rankOneEndomorphism f x) m = (-q) • m) := by
  constructor
  · exact exists_protected_eigenvector_of_pair S f x q p₁ p₂ hp hp₁ hp₂
  · exact exists_protected_eigenvector_of_pair S f x (-q) m₁ m₂ hm hm₁ hm₂

end RainichKaluza
