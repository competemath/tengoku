import Tengoku.OpenaiMath.OAI.Analysis.Unitarizability.SparseSplitting
import Tengoku

namespace OAI

/-! Regular convolution operators, product lists with multiplicity,
and sparse splitting from a contracting average. -/
noncomputable section
namespace Dixmier
universe u
open Finset
attribute [local instance] Classical.propDecidable

variable {G : Type*}

def reindexL2 (e : G ≃ G) (ξ : ScalarL2 G) : ScalarL2 G :=
  ⟨fun x => ξ (e x), memℓp_gen (((lp.memℓp ξ).summable (by norm_num)).comp_injective e.injective)⟩

@[simp] theorem reindexL2_apply (e : G ≃ G) (ξ : ScalarL2 G) (x : G) :
    reindexL2 e ξ x = ξ (e x) := rfl

theorem l2_norm_sq (ξ : ScalarL2 G) : ‖ξ‖ ^ 2 = ∑' x, ‖ξ x‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) ξ

theorem reindexL2_norm (e : G ≃ G) (ξ : ScalarL2 G) : ‖reindexL2 e ξ‖ = ‖ξ‖ := by
  have hs : ‖reindexL2 e ξ‖ ^ 2 = ‖ξ‖ ^ 2 := by
    rw [l2_norm_sq, l2_norm_sq]
    exact e.tsum_eq (fun x => ‖ξ x‖ ^ 2)
  nlinarith [norm_nonneg (reindexL2 e ξ), norm_nonneg ξ]

def reindexIsometry (e : G ≃ G) : ScalarL2 G →ₗᵢ[ℂ] ScalarL2 G where
  toFun := reindexL2 e
  map_add' ξ η := by ext x; rfl
  map_smul' z ξ := by ext x; rfl
  norm_map' := reindexL2_norm e

variable [Group G]

/-- The right regular representation R_t ξ(x)=ξ(xt). -/
def rightRegular : G →* (ScalarL2 G →L[ℂ] ScalarL2 G) where
  toFun t := (reindexIsometry (Equiv.mulRight t)).toContinuousLinearMap
  map_one' := by ext ξ x; simp [reindexIsometry, reindexL2]
  map_mul' s t := by ext ξ x; simp [reindexIsometry, reindexL2, mul_assoc]

@[simp] theorem rightRegular_apply (t : G) (ξ : ScalarL2 G) (x : G) :
    rightRegular t ξ x = ξ (x * t) := rfl

/-- Left regular operators U_g commute with the right regular operators. -/
def leftRegular : G →* (ScalarL2 G →L[ℂ] ScalarL2 G) where
  toFun g := (reindexIsometry (Equiv.mulLeft g⁻¹)).toContinuousLinearMap
  map_one' := by ext ξ x; simp [reindexIsometry, reindexL2]
  map_mul' g h := by ext ξ x; simp [reindexIsometry, reindexL2]

@[simp] theorem leftRegular_apply (g : G) (ξ : ScalarL2 G) (x : G) :
    leftRegular g ξ x = ξ (g⁻¹ * x) := rfl

def Word (I : Type u) : ℕ → Type u
  | 0 => PUnit
  | n + 1 => I × Word I n

instance wordFintype {I : Type*} [Fintype I] : (n : ℕ) → Fintype (Word I n)
  | 0 => inferInstanceAs (Fintype PUnit)
  | n + 1 => by
    letI : Fintype (Word I n) := wordFintype n
    exact inferInstanceAs (Fintype (I × Word I n))

def wordProduct {I : Type*} (s : I → G) : (n : ℕ) → Word I n → G
  | 0, _ => 1
  | n + 1, w => s w.1 * wordProduct s n w.2

end Dixmier

end

end OAI
