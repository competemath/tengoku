import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.QuaternionSelfAdjointCarrier

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms conjugate_mem` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms actLinearEquiv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms scalarAut` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms scalarAut_grouped` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.QuaternionRow.ScalarJordanAut

open AlbertLean.Generic.QuaternionRow.GroupedBridge
open AlbertLean.Generic.QuaternionRow.SelfAdjointCarrier

universe u
variable {K : Type u} [Field K] [CharZero K]

theorem conjugate_mem (t : K) (ht : t ≠ 0) (P : Carrier K) :
    IsSelfAdjoint
      (scalarSimilitude t * (P : Mat6 K) * scalarSimilitudeInv t) := by
  obtain ⟨a, u, v, hP⟩ := exists_grouped P
  rw [hP, scalarSimilitude_conjugates_grouped t ht]
  exact grouped_symplectic_selfadjoint _ _ _

def actLinear (t : K) (ht : t ≠ 0) : Carrier K →ₗ[K] Carrier K where
  toFun P := ⟨scalarSimilitude t * (P : Mat6 K) * scalarSimilitudeInv t,
    conjugate_mem t ht P⟩
  map_add' A B := by
    apply Subtype.ext
    simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c A := by
    apply Subtype.ext
    simp [Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem actLinear_coe (t : K) (ht : t ≠ 0) (P : Carrier K) :
    ((actLinear t ht P : Carrier K) : Mat6 K) =
      scalarSimilitude t * P * scalarSimilitudeInv t := rfl

/-- The displayed conjugation is an honest linear equivalence of the actual
self-adjoint carrier.-/
def actLinearEquiv (t : K) (ht : t ≠ 0) : Carrier K ≃ₗ[K] Carrier K where
  toLinearMap := actLinear t ht
  invFun := actLinear t⁻¹ (inv_ne_zero ht)
  left_inv P := by
    apply Subtype.ext
    change scalarSimilitude t⁻¹ *
        (scalarSimilitude t * (P : Mat6 K) * scalarSimilitudeInv t) *
          scalarSimilitudeInv t⁻¹ = (P : Mat6 K)
    have hleft : scalarSimilitude t⁻¹ = scalarSimilitudeInv t := rfl
    have hright : scalarSimilitudeInv t⁻¹ = scalarSimilitude t := by
      simp [scalarSimilitudeInv, scalarSimilitude]
    rw [hleft, hright]
    calc
      scalarSimilitudeInv t *
            (scalarSimilitude t * (P : Mat6 K) * scalarSimilitudeInv t) *
          scalarSimilitude t =
          (scalarSimilitudeInv t * scalarSimilitude t) * (P : Mat6 K) *
            (scalarSimilitudeInv t * scalarSimilitude t) := by
              simp only [Matrix.mul_assoc]
      _ = 1 * (P : Mat6 K) * 1 := by rw [scalarSimilitude_inv_mul t ht]
      _ = (P : Mat6 K) := by simp
  right_inv P := by
    apply Subtype.ext
    change scalarSimilitude t *
        (scalarSimilitude t⁻¹ * (P : Mat6 K) * scalarSimilitudeInv t⁻¹) *
          scalarSimilitudeInv t = (P : Mat6 K)
    have hleft : scalarSimilitude t⁻¹ = scalarSimilitudeInv t := rfl
    have hright : scalarSimilitudeInv t⁻¹ = scalarSimilitude t := by
      simp [scalarSimilitudeInv, scalarSimilitude]
    rw [hleft, hright]
    calc
      scalarSimilitude t *
            (scalarSimilitudeInv t * (P : Mat6 K) * scalarSimilitude t) *
          scalarSimilitudeInv t =
          (scalarSimilitude t * scalarSimilitudeInv t) * (P : Mat6 K) *
            (scalarSimilitude t * scalarSimilitudeInv t) := by
              simp only [Matrix.mul_assoc]
      _ = 1 * (P : Mat6 K) * 1 := by rw [scalarSimilitude_mul_inv t ht]
      _ = (P : Mat6 K) := by simp

/-- Minimal genuine unital linear Jordan-automorphism interface for this
carrier; no ambient automorphism-group classification enters the definition.-/
structure Aut where
  linear : Carrier K ≃ₗ[K] Carrier K
  map_one : linear one = one
  map_jordan : ∀ A B, linear (jordan A B) = jordan (linear A) (linear B)

/-- The root-free scalar correction is a genuine Jordan automorphism.-/
def scalarAut (t : K) (ht : t ≠ 0) : Aut (K := K) where
  linear := actLinearEquiv t ht
  map_one := by
    apply Subtype.ext
    exact scalarSimilitude_map_one t ht
  map_jordan A B := by
    apply Subtype.ext
    exact scalarSimilitude_map_jordan t ht A B

@[simp] theorem scalarAut_grouped
    (t : K) (ht : t ≠ 0) (a : ScalarFibre.Mat3 K)
    (u v : ScalarFibre.Vec3 K)
    (P : Carrier K) (hP : (P : Mat6 K) = grouped a u v) :
    (((scalarAut t ht).linear P : Carrier K) : Mat6 K) =
      grouped a (t • u) (t⁻¹ • v) := by
  change scalarSimilitude t * (P : Mat6 K) * scalarSimilitudeInv t = _
  rw [hP, scalarSimilitude_conjugates_grouped t ht]

end AlbertLean.Generic.QuaternionRow.ScalarJordanAut
