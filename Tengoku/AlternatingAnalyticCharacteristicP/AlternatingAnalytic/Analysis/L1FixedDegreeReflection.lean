import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.DenseMultilinearExtension
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1AnalyticFactorization
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Analysis.L1PolynomialLift
import Tengoku.Seed.Analysis.Analytic.CPolynomial
import Tengoku.Seed.Analysis.Analytic.Composition
import Tengoku.Seed.Analysis.Analytic.Within

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Fixed-degree reflection along ℓ¹ families

Theorem 4.5(2): if `a : H → W` has a bounded homogeneous polynomial representative of
fixed degree `d` with values in a Banach space `Z ⊇ W` (closed), then `a ∘ γ` is analytic
for every analytic `γ` on an open subset of ℓ¹(I, K). The proof extends the multilinear
map to the completion of `H`, lifts it after a bounded linear map from ℓ¹, and uses the
local factorization of `γ` through ℓ¹ words. Neither `K` nor `H` need be complete.
-/

open scoped lp
open Filter Topology
open L1Coordinates (L1)

noncomputable section

namespace AlternatingAnalytic

variable {K I J H Z : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup H] [NormedSpace K H]
  [NormedAddCommGroup Z] [NormedSpace K Z] [CompleteSpace Z]

/-- The norm-nonincreasing extension of a multilinear map to the completion of `H`.-/
def completionMultilinear (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z) :
    ContinuousMultilinearMap K (fun _ : Fin d => UniformSpace.Completion H) Z :=
  denseMultilinearExtension
    (UniformSpace.Completion.toComplₗᵢ : H →ₗᵢ[K] UniformSpace.Completion H)
    UniformSpace.Completion.denseRange_coe d B

@[simp]
theorem completionMultilinear_apply (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z) (v : Fin d → H) :
    completionMultilinear d B (fun i => (v i : UniformSpace.Completion H)) = B v :=
  denseMultilinearExtension_apply
    (UniformSpace.Completion.toComplₗᵢ : H →ₗᵢ[K] UniformSpace.Completion H)
    UniformSpace.Completion.denseRange_coe d B v

theorem norm_completionMultilinear_le (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z) :
    ‖completionMultilinear d B‖ ≤ ‖B‖ :=
  norm_denseMultilinearExtension_le
    (UniformSpace.Completion.toComplₗᵢ : H →ₗᵢ[K] UniformSpace.Completion H)
    UniformSpace.Completion.denseRange_coe d B

/-- The completed diagonal stays in the closed submodule `W`.-/
theorem completionMultilinear_diagonal_mem
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h))
    (z : UniformSpace.Completion H) : completionMultilinear d B (fun _ => z) ∈ W := by
  refine UniformSpace.Completion.induction_on z
    (hW.preimage ((completionMultilinear d B).cont.comp
      (continuous_pi fun _ => continuous_id))) ?_
  intro h
  rw [completionMultilinear_apply, ← hP]
  exact (P h).property

/-- The diagonal of the completed multilinear map, as a map into `W`.-/
def completionDiagonal
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h)) :
    UniformSpace.Completion H → W :=
  fun z => ⟨completionMultilinear d B (fun _ => z),
    completionMultilinear_diagonal_mem W hW d B P hP z⟩

@[simp]
theorem coe_completionDiagonal
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h))
    (z : UniformSpace.Completion H) :
    (completionDiagonal W hW d B P hP z : Z) =
      completionMultilinear d B (fun _ => z) := rfl

@[simp]
theorem completionDiagonal_coe
    (W : Submodule K Z) (hW : IsClosed (W : Set Z)) (d : ℕ)
    (B : ContinuousMultilinearMap K (fun _ : Fin d => H) Z)
    (P : H → W) (hP : ∀ h, (P h : Z) = B (fun _ => h)) (h : H) :
    completionDiagonal W hW d B P hP (h : UniformSpace.Completion H) = P h := by
  apply Subtype.ext
  exact (completionMultilinear_apply d B (fun _ => h)).trans (hP h).symm

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace K V]

end AlternatingAnalytic
