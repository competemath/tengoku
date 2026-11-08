module

public import Tengoku.Seed.LinearAlgebra.Matrix.SchurComplement
public import Tengoku.Seed.LinearAlgebra.Matrix.NonsingularInverse
public import Tengoku.Seed.Data.Real.Basic
public import Tengoku.AisafetyAtlas.AISafetyAtlas.SingularLearning.ReducedRank

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The saddle Hessian block

MAIS-O77(b) computes the two-sided local pair at a nonterminal critical point by
splitting the loss along a discarded singular mode.  The quadratic part of that
splitting is the `2H`-dimensional block

    `K = [[BᵀB, -s I], [-s I, A Aᵀ]]`,

and the argument needs it to be nonsingular.  That is the step this module
settles, and only that step: no Morse lemma, no volume statement, no claim about
`O77AllSaddlesHavePairOne`.

**Why this is not a direct Schur complement.**  At a rung point both diagonal
blocks are singular — `A` and `B` have rank `k < H` there — so neither of
Mathlib's two Schur-complement determinant lemmas applies as written.  What *is*
invertible is the off-diagonal block `-s I`, for `s ≠ 0`.  Exchanging the two
block rows moves it into the corner the Schur complement wants, at the cost of a
sign that is a unit and therefore invisible to the nonsingularity question.

The identity obtained is

    `det [[-s I, R], [P, -s I]] = (-1)^H det (P R - s² I)`,

which is the printed `det K = (-1)^H det (s² I - P R)` up to the sign
`det (s² I - X) = (-1)^H det (X - s² I)`.  Only the vanishing matters below, so
the sign is carried rather than fought.
-/

namespace AISafetyAtlas.SingularLearning

open Matrix

/-! ## The quadratic form

Nonsingularity is a statement about the matrix; the Morse splitting consumes the
*form*.  This is the bridge between them, and it is where the shape
`xᵀ P x + yᵀ R y - 2 s ⟨x, y⟩` — the sum of the two block energies minus the
coupling through the discarded mode — becomes visible.
-/

/-! ## The germ as a block form with varying coupling

The exact loss expansion produces

    `G = ½[xᵀPx + yᵀRy - 2s⟨x,y⟩] + ½⟨x,y⟩²`,

and the quartic can be absorbed: `G` is the *same* block quadratic form with the
coupling `s` replaced by `s - ½⟨x,y⟩`.  At the origin the coupling is `s`, so the
Hessian is the block already studied above, and away from it the coupling varies
polynomially.

This is the shape a Morse argument consumes — `G(z) = ½ zᵀ H(z) z` with `H`
analytic and `H(0)` the nondegenerate Hessian — obtained here without any
Hadamard-type lemma, because the loss expansion terminated.
-/

/-! ## Reducing the coordinate change to a matrix equation

The Morse step asks for analytic `A(z)` with `A(0) = I` and `A(z)ᵀ K A(z) = H(z)`,
where `K = H(0)` is the nondegenerate Hessian.  Writing `A = I + K⁻¹X` with `X`
symmetric turns that into a single matrix equation whose linear part is
invertible, which is what puts it inside the reach of an inverse function
theorem rather than needing a bespoke construction.

The two lemmas here are the algebra of that reduction.  They are unconditional
and carry no analysis; the analytic solvability of the resulting equation is the
part still to be done.
-/

/-! ## Indefiniteness at a general rung, and where the kernel vector comes from

`hessianBlock_indefinite_at_zero` settles the rank-zero rung, where both diagonal
blocks vanish outright.  At a general rung the diagonal blocks are the Gram
matrices `BᵀB` and `AAᵀ`, which are positive semidefinite but not zero.  The two
results below close that gap in the only way the argument needs: a *shared*
kernel direction is not required, one block having a kernel vector is enough, and
at a nonterminal rung one of them always does.

The two statements are deliberately independent of the `fromBlocks` packaging on
the one side and of the coupling `s` on the other, so that a caller already
holding the form in the shape `xᵀPx + yᵀRy - 2s⟨x,y⟩` — which is what
`hessianBlock_quadForm` produces — can consume the first directly.
-/

/-- Scaling a vector scales the quadratic form quadratically.-/
private theorem quadForm_smul {H : ℕ} (M : Matrix (Fin H) (Fin H) ℝ) (t : ℝ)
    (z : Fin H → ℝ) :
    (t • z) ⬝ᵥ (M *ᵥ (t • z)) = t ^ 2 * (z ⬝ᵥ (M *ᵥ z)) := by
  rw [Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  ring

/-- A matrix of rank below its width has a nonzero kernel vector.  This is
rank–nullity in the only direction used here, phrased so that the caller never
has to see `Module.finrank`.-/
private theorem exists_ker_of_rank_lt {K H : ℕ} (B : Matrix (Fin K) (Fin H) ℝ)
    (h : B.rank < H) :
    ∃ z : Fin H → ℝ, z ≠ 0 ∧ B *ᵥ z = 0 := by
  have hrn := LinearMap.finrank_range_add_finrank_ker B.mulVecLin
  rw [show Module.finrank ℝ (Fin H → ℝ) = H by simp] at hrn
  rw [show Module.finrank ℝ (LinearMap.range B.mulVecLin) = B.rank from rfl] at hrn
  have hker : Module.finrank ℝ (LinearMap.ker B.mulVecLin) ≠ 0 := by omega
  have hne : LinearMap.ker B.mulVecLin ≠ ⊥ := fun hb => hker (by rw [hb]; simp)
  obtain ⟨z, hz, hz0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  exact ⟨z, hz0, hz⟩

end AISafetyAtlas.SingularLearning
