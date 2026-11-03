import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Graded.IdempotentProjective
import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Graded.FiniteProjectionCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Homogeneous idempotent projections -/
set_option autoImplicit false
noncomputable section
namespace MagnitudeConjecture.Graded.ModuleGrading
variable {k A M : Type*} [Field k] [Ring A] [Algebra k A]
variable [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]
variable {R : VectorGrading k A} (G : ModuleGrading (M := M) R)

/-- First take the homogeneous component, then apply the idempotent.-/
def idempotentProjection (e : A) (d : ℤ) : M →ₗ[k] M where
  toFun x := e • G.projection d x
  map_add' x y := by rw [map_add, smul_add]
  map_smul' c x := by rw [map_smul, smul_comm]; rfl

/--
@isnad1 id=mem.2h8v.s8.22d7a70b40a9 from=translated src=- shape=adcefd25 vocab=abbfc581
-/
theorem idempotentProjection_mem (e : A) (he : e * e = e)
    (he0 : e ∈ R.component 0) (d : ℤ) (x : M) :
    G.idempotentProjection e d x ∈ idempotentComponent R G e d := by
  refine ⟨?_, ?_⟩
  · change e • G.projection d x ∈ G.component d
    simpa only [zero_add] using G.smul_mem he0 (G.projection_mem d x)
  · change e • (e • G.projection d x) = e • G.projection d x
    rw [← mul_smul, he]

/--
@isnad1 id=eq.1h8v.s8.bc94739f291d from=translated src=- shape=ea26ca79 vocab=b746d1a7
-/
theorem idempotentProjection_of_mem (e : A) (d : ℤ) (x : M)
    (hx : x ∈ idempotentComponent R G e d) : G.idempotentProjection e d x = x := by
  change e • G.projection d x = x
  rw [G.toVectorGrading.projection_of_mem hx.1, hx.2]

/--
@isnad1 id=eq.2h9v.s8.afdfb632149b from=translated src=- shape=3dd006d4 vocab=a8a15631
-/
theorem idempotentProjection_of_degree_ne (e : A) {d d' : ℤ} (h : d' ≠ d)
    (x : M) (hx : x ∈ G.component d') : G.idempotentProjection e d x = 0 := by
  change e • G.projection d x = 0
  rw [G.toVectorGrading.projection_of_mem_ne hx h, smul_zero]

/--
@isnad1 id=eq.2h9v.s8.e06fd2f2ce4a from=translated src=- shape=f17f850a vocab=425a9714
-/
theorem idempotentProjection_of_orthogonal {e f : A} (hef : e * f = 0)
    (d : ℤ) (x : M) (hx : x ∈ idempotentComponent R G f d) :
    G.idempotentProjection e d x = 0 := by
  change e • G.projection d x = 0
  rw [G.toVectorGrading.projection_of_mem hx.1]
  calc
    e • x = e • (f • x) := congrArg (fun y ↦ e • y) hx.2.symm
    _ = 0 := by rw [← mul_smul, hef, zero_smul]

variable {ι ν : Type*} [Fintype ι] [Fintype ν]
variable (e : ι → A) (hsum : ∑ i, e i = 1)
variable (δ : ν → ℤ) (hδ : Function.Injective δ)
variable (hcover : ∀ d, G.component d ≠ ⊥ → ∃ q, δ q = d)

include hsum hδ hcover in
/-- The homogeneous idempotent coordinates sum back to the original vector.
@isnad1 id=eq.3h10v.s8.82430c7b822b from=translated src=- shape=a1ed8783 vocab=66032800
-/
theorem sum_idempotentProjection (x : M) :
    ∑ p : ι × ν, G.idempotentProjection (e p.1) (δ p.2) x = x := by
  classical
  change ∑ p : ι × ν, e p.1 • G.projection (δ p.2) x = x
  rw [Fintype.sum_prod_type]
  simp only [← Finset.smul_sum, G.toVectorGrading.sum_projection_of_cover δ hδ hcover]
  rw [← Finset.sum_smul, hsum, one_smul]

end MagnitudeConjecture.Graded.ModuleGrading
