import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.KernelEnergy
import Tengoku

namespace OAI

/-! Coordinate maps and the invariant-kernel obstruction.
The Hilbert space is the lp space with finite Euclidean fibres. -/
noncomputable section
namespace Dixmier
namespace KernelObstruction
open scoped ComplexConjugate
open Finset
variable {G K : Type*} [Fintype K]
local instance : DecidableEq G := Classical.decEq G
local instance : DecidableEq K := Classical.decEq K

abbrev Fibre (K : Type*) [Fintype K] := EuclideanSpace ℂ K
abbrev Space (G K : Type*) [Fintype K] := lp (fun _ : G => Fibre K) 2
abbrev Op (G K : Type*) [Fintype K] := Space G K →L[ℂ] Space G K

def inclusion (x : G) : Fibre K →L[ℂ] Space G K :=
  lp.singleContinuousLinearMap ℂ (fun _ : G => Fibre K) 2 x

def evaluation (x : G) : Space G K →L[ℂ] Fibre K :=
  lp.evalCLM ℂ (fun _ : G => Fibre K) 2 x

@[simp] theorem inclusion_apply (x : G) (v : Fibre K) :
    inclusion x v = lp.single 2 x v := rfl
@[simp] theorem evaluation_apply (x : G) (ξ : Space G K) :
    evaluation x ξ = ξ x := rfl

@[simp] theorem inclusion_norm (x : G) (v : Fibre K) : ‖inclusion x v‖ = ‖v‖ :=
  lp.norm_single (p := 2) (E := fun _ : G => Fibre K) (by norm_num) x v

@[simp] theorem inclusion_adjoint (x : G) :
    (inclusion (K := K) x).adjoint = evaluation x := by
  apply ContinuousLinearMap.ext
  intro ξ
  apply ext_inner_left ℂ
  intro v
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (lp.single 2 x v) ξ = inner ℂ v (ξ x)
  exact lp.inner_single_left (𝕜 := ℂ) (G := fun _ : G => Fibre K) x v ξ

@[simp] theorem evaluation_inclusion (x : G) :
    (evaluation (K := K) x).comp (inclusion x) = ContinuousLinearMap.id ℂ (Fibre K) := by
  ext v a
  simp

def block (F : Op G K) (x y : G) : Fibre K →L[ℂ] Fibre K :=
  (evaluation x).comp (F.comp (inclusion y))

def row (F : Op G K) (x : G) : Space G K →L[ℂ] Fibre K :=
  (evaluation x).comp F

def col (F : Op G K) (y : G) : Fibre K →L[ℂ] Space G K :=
  F.comp (inclusion y)

def coefficients (B : Fibre K →L[ℂ] Fibre K) : EuclideanSpace ℂ (K × K) :=
  WithLp.toLp 2 (fun ab => (B (EuclideanSpace.basisFun K ℂ ab.2)) ab.1)

@[simp] theorem coefficients_apply (B : Fibre K →L[ℂ] Fibre K) (a b : K) :
    coefficients B (a,b) = (B (EuclideanSpace.basisFun K ℂ b)) a := rfl

theorem coefficients_norm_sq (B : Fibre K →L[ℂ] Fibre K) :
    ‖coefficients B‖^2 = ∑ b : K, ‖B (EuclideanSpace.basisFun K ℂ b)‖^2 := by
  simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type, coefficients_apply]
  exact Finset.sum_comm

theorem space_norm_sq (ξ : Space G K) : ‖ξ‖^2 = ∑' x, ‖ξ x‖^2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ξ

theorem space_summable (ξ : Space G K) : Summable (fun x => ‖ξ x‖^2) := by
  simpa using (lp.memℓp ξ).summable (by norm_num : (0 : ℝ) < (2 : ENNReal).toReal)

theorem column_energy (L : Fibre K →L[ℂ] Space G K) :
    ∑' x, ‖coefficients ((evaluation x).comp L)‖^2 =
      ∑ b : K, ‖L (EuclideanSpace.basisFun K ℂ b)‖^2 := by
  simp_rw [coefficients_norm_sq]
  rw [Summable.tsum_finsetSum]
  · apply Finset.sum_congr rfl
    intro b hb
    exact (space_norm_sq _).symm
  · intro b hb
    exact space_summable _

theorem column_energy_le (L : Fibre K →L[ℂ] Space G K) :
    ∑' x, ‖coefficients ((evaluation x).comp L)‖^2 ≤
      (Fintype.card K : ℝ) * ‖L‖^2 := by
  rw [column_energy]
  calc
    _ ≤ ∑ b : K, ‖L‖^2 := by
      apply Finset.sum_le_sum
      intro b hb
      have h := L.le_opNorm (EuclideanSpace.basisFun K ℂ b)
      simp only [(EuclideanSpace.basisFun K ℂ).norm_eq_one, mul_one] at h
      exact pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = _ := by simp [nsmul_eq_mul]

theorem coefficients_adjoint_apply (B : Fibre K →L[ℂ] Fibre K) (a b : K) :
    coefficients B.adjoint (a,b) = conj (coefficients B (b,a)) := by
  simp only [coefficients_apply]
  rw [← EuclideanSpace.basisFun_inner, ← EuclideanSpace.basisFun_inner]
  rw [ContinuousLinearMap.adjoint_inner_right, inner_conj_symm]

theorem coefficients_adjoint_norm (B : Fibre K →L[ℂ] Fibre K) :
    ‖coefficients B.adjoint‖ = ‖coefficients B‖ := by
  have h : ‖coefficients B.adjoint‖^2 = ‖coefficients B‖^2 := by
    simp only [EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type,
      coefficients_adjoint_apply, RCLike.norm_conj]
    exact Finset.sum_comm
  nlinarith [norm_nonneg (coefficients B.adjoint), norm_nonneg (coefficients B)]

theorem row_block_norm (R : Space G K →L[ℂ] Fibre K) (x : G) :
    ‖coefficients (R.comp (inclusion x))‖ =
      ‖coefficients ((evaluation x).comp R.adjoint)‖ := by
  rw [← coefficients_adjoint_norm (R.comp (inclusion x)),
    ContinuousLinearMap.adjoint_comp, inclusion_adjoint]

theorem row_energy_le (R : Space G K →L[ℂ] Fibre K) :
    ∑' x, ‖coefficients (R.comp (inclusion x))‖^2 ≤
      (Fintype.card K : ℝ) * ‖R‖^2 := by
  simp_rw [row_block_norm]
  simpa only [ContinuousLinearMap.adjoint.norm_map] using column_energy_le R.adjoint

variable [Group G]

def reindex (e : G ≃ G) (ξ : Space G K) : Space G K :=
  ⟨fun x => ξ (e x), memℓp_gen (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩

omit [Group G] in
theorem reindex_norm (e : G ≃ G) (ξ : Space G K) : ‖reindex e ξ‖ = ‖ξ‖ := by
  have h : ‖reindex e ξ‖^2 = ‖ξ‖^2 := by
    rw [space_norm_sq, space_norm_sq]
    exact e.tsum_eq (fun x => ‖ξ x‖^2)
  nlinarith [norm_nonneg (reindex e ξ), norm_nonneg ξ]

def reindexIsometry (e : G ≃ G) : Space G K →ₗᵢ[ℂ] Space G K where
  toFun := reindex e
  map_add' ξ η := by ext x a; rfl
  map_smul' z ξ := by ext x a; rfl
  norm_map' := reindex_norm e

/-- The fibre-valued left regular representation. -/
def translation : G →* Op G K where
  toFun g := (reindexIsometry (K := K) (Equiv.mulLeft g⁻¹)).toContinuousLinearMap
  map_one' := by ext ξ x a; simp [reindexIsometry, reindex]
  map_mul' g h := by ext ξ x a; simp [reindexIsometry, reindex]

@[simp] theorem translation_apply (g : G) (ξ : Space G K) (x : G) :
    translation g ξ x = ξ (g⁻¹ * x) := rfl

@[simp] theorem translation_inclusion (g y : G) (v : Fibre K) :
    translation g (inclusion y v) = inclusion (g*y) v := by
  ext x a
  simp only [translation_apply, inclusion_apply, lp.single_apply]
  by_cases h : x = g*y
  · subst x
    simp
  · have h' : g⁻¹*x ≠ y := by intro he; apply h; rw [← he]; simp
    simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h']

def Commutant : Set (Op G K) := {F | ∀ g, Commute F (translation g)}

omit [Group G] in
@[simp] theorem block_sub (A C : Op G K) (x y : G) :
    block (A-C) x y = block A x y - block C x y := by
  ext v a
  rfl

@[simp] theorem coefficients_sub (A C : Fibre K →L[ℂ] Fibre K) :
    coefficients (A-C) = coefficients A - coefficients C := by ext ab; rfl

def energy (A : Op G K) : ℝ := ∑' s, ‖coefficients (block A 1 s)‖^2

end KernelObstruction
end Dixmier

end

end OAI
