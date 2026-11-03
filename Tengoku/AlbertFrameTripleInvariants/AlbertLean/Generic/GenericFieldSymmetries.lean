import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.CoefficientFieldInvolution
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericReorientationMoment
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.GenericOrientationAttachment

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms nu_commutes_deck` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms tau_twice` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms tau_commutes_deck` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms kappa_eq_orientation` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms kappa_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms eta_ne_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms tau_kappa` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms tau_eta` (it only prints; the queue checks the axioms of every declaration). -/

/-! The two concrete commuting symmetries of the existing generic field.
The orientation and determinant-root difference have the required signs.
Literal-ledger invariance and common fixed-field identification are separate. -/

noncomputable section
namespace AlbertLean.Generic.GenericFieldSymmetries

open AlbertLean.Generic.NestedReciprocalField
open AlbertLean.Generic.GenericDeterminantOpen
open AlbertLean.Generic.GenericFieldChart
open AlbertLean.Generic.GenericLedgerFixedField
open AlbertLean.Generic.GenericReorientationBase
open AlbertLean.Generic.CoefficientFieldInvolution

universe u
variable (k : Type u) [Field k] [CharZero k]

def nu : FunctionField k ≃+* FunctionField k :=
  fieldEquiv (reorient k) (reorient_twice k)

@[simp] theorem nu_base (b : Base k) :
    nu k (includeBase k b) = includeBase k (reorient k b) :=
  fieldEquiv_base _ _ b

@[simp] theorem nu_T : nu k (T (Base k)) = T (Base k) := fieldEquiv_T _ _

@[simp] theorem nu_twice (z : FunctionField k) : nu k (nu k z) = z :=
  fieldEquiv_twice _ _ z

@[simp] theorem nu_constant (z : k) :
    nu k (algebraMap k (FunctionField k) z) = algebraMap k (FunctionField k) z := by
  rw [IsScalarTower.algebraMap_apply k (Base k) (FunctionField k)]
  change nu k (includeBase k (algebraMap k (Base k) z)) = _
  rw [nu_base, reorient_constant]
  rfl

theorem nu_commutes_deck : Function.Commute (nu k) (deck k) :=
  fieldEquiv_commutes_reciprocal (reorient k) (reorient_twice k)
    (Matrix.det (rationalM k)) (det_rationalM_ne_zero k) (reorient_det_rationalM k)

def tau : FunctionField k ≃+* FunctionField k := (nu k).trans (deck k)

theorem tau_apply (z : FunctionField k) : tau k z = deck k (nu k z) := rfl

@[simp] theorem deck_twice (z : FunctionField k) : deck k (deck k z) = z :=
  (deck k).left_inv z

@[simp] theorem tau_twice (z : FunctionField k) : tau k (tau k z) = z := by
  simp only [tau_apply]
  rw [nu_commutes_deck, nu_twice, deck_twice]

theorem tau_commutes_deck : Function.Commute (tau k) (deck k) := by
  intro z
  simp only [tau_apply]
  rw [nu_commutes_deck]

def kappa : FunctionField k := includeBase k (ι k (c k) - ι k (a k) * ι k (b k))
def eta : FunctionField k :=
  T (Base k) - includeBase k (Matrix.det (rationalM k)) / T (Base k)

theorem kappa_eq_orientation :
    kappa k = AlbertLean.Residual.FrameIdeal.orientation (genericChart k) := by
  change includeBase k (ι k (c k) - ι k (a k) * ι k (b k)) =
    1 * includeBase k (ι k (c k)) - includeBase k (ι k (b k)) *
      includeBase k (ι k (a k))
  simp only [map_sub, map_mul, one_mul]
  ring

theorem kappa_ne_zero : kappa k ≠ 0 := by
  rw [kappa_eq_orientation]
  exact generic_orientation_ne k

theorem eta_ne_zero : eta k ≠ 0 := by
  intro h
  apply branchPolynomial_ne_zero (Base k) (Matrix.det (rationalM k))
  have ht := T_ne_zero (Base k)
  have he : T (Base k) = includeBase k (Matrix.det (rationalM k)) / T (Base k) :=
    sub_eq_zero.mp h
  have hh := (eq_div_iff ht).mp he
  simpa only [pow_two, sub_eq_zero, includeBase] using hh

@[simp] theorem nu_kappa : nu k (kappa k) = -kappa k := by
  rw [kappa, nu_base, reorient_orientation, map_neg]

@[simp] theorem deck_kappa : deck k (kappa k) = kappa k := deck_base k _

@[simp] theorem nu_eta : nu k (eta k) = eta k := by
  simp only [eta, map_sub, map_div₀, nu_T, nu_base, reorient_det_rationalM]

@[simp] theorem deck_eta : deck k (eta k) = -eta k := by
  have hm : includeBase k (Matrix.det (rationalM k)) ≠ 0 :=
    (map_ne_zero (includeBase k)).mpr (det_rationalM_ne_zero k)
  have ht : deck k (T (Base k)) =
      includeBase k (Matrix.det (rationalM k)) / T (Base k) := deck_Delta k
  simp only [eta, map_sub, map_div₀, ht, deck_base]
  rw [div_div_cancel₀ hm]
  ring

@[simp] theorem tau_kappa : tau k (kappa k) = -kappa k := by
  rw [tau_apply, nu_kappa, map_neg, deck_kappa]

@[simp] theorem tau_eta : tau k (eta k) = -eta k := by
  rw [tau_apply, nu_eta, deck_eta]

@[simp] theorem tau_constant (z : k) :
    tau k (algebraMap k (FunctionField k) z) = algebraMap k (FunctionField k) z := by
  rw [tau_apply, nu_constant, IsScalarTower.algebraMap_apply k (Base k) (FunctionField k)]
  exact deck_base k _

end AlbertLean.Generic.GenericFieldSymmetries
