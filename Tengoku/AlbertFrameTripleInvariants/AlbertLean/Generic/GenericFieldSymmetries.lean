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

/--
@isnad1 id=eq.0h2v.s13.b8a7127ae7a0 from=translated src=- shape=c1de2b67 vocab=35db9408
-/
@[simp] theorem nu_base (b : Base k) :
    nu k (includeBase k b) = includeBase k (reorient k b) :=
  fieldEquiv_base _ _ b

/--
@isnad1 id=eq.0h1v.s13.d8fe5a78d441 from=translated src=- shape=12d1b4ab vocab=5656ebb6
-/
@[simp] theorem nu_T : nu k (T (Base k)) = T (Base k) := fieldEquiv_T _ _

/--
@isnad1 id=eq.0h2v.s14.333a3dae0dbf from=translated src=- shape=f34d1248 vocab=f1a46016
-/
@[simp] theorem nu_twice (z : FunctionField k) : nu k (nu k z) = z :=
  fieldEquiv_twice _ _ z

/--
@isnad1 id=eq.0h2v.s13.1cc769965a03 from=translated src=- shape=4789a508 vocab=e81c8adf
-/
@[simp] theorem nu_constant (z : k) :
    nu k (algebraMap k (FunctionField k) z) = algebraMap k (FunctionField k) z := by
  rw [IsScalarTower.algebraMap_apply k (Base k) (FunctionField k)]
  change nu k (includeBase k (algebraMap k (Base k) z)) = _
  rw [nu_base, reorient_constant]
  rfl

/--
@isnad1 id=commute.0h1v.s14.2d91ba7700ec from=translated src=- shape=9035629b vocab=f3dc0492
-/
theorem nu_commutes_deck : Function.Commute (nu k) (deck k) :=
  fieldEquiv_commutes_reciprocal (reorient k) (reorient_twice k)
    (Matrix.det (rationalM k)) (det_rationalM_ne_zero k) (reorient_det_rationalM k)

def tau : FunctionField k ≃+* FunctionField k := (nu k).trans (deck k)

/--
@isnad1 id=eq.0h2v.s14.d3753c050f86 from=translated src=- shape=1a7a47a6 vocab=05d529c3
-/
theorem tau_apply (z : FunctionField k) : tau k z = deck k (nu k z) := rfl

/--
@isnad1 id=eq.0h2v.s14.831df5e2c215 from=translated src=- shape=f34d1248 vocab=92cb930c
-/
@[simp] theorem deck_twice (z : FunctionField k) : deck k (deck k z) = z :=
  (deck k).left_inv z

/--
@isnad1 id=eq.0h2v.s14.b6b082af4586 from=translated src=- shape=f34d1248 vocab=d6423663
-/
@[simp] theorem tau_twice (z : FunctionField k) : tau k (tau k z) = z := by
  simp only [tau_apply]
  rw [nu_commutes_deck, nu_twice, deck_twice]

/--
@isnad1 id=commute.0h1v.s14.1115589dc85f from=translated src=- shape=9035629b vocab=087e80c7
-/
theorem tau_commutes_deck : Function.Commute (tau k) (deck k) := by
  intro z
  simp only [tau_apply]
  rw [nu_commutes_deck]

def kappa : FunctionField k := includeBase k (ι k (c k) - ι k (a k) * ι k (b k))
def eta : FunctionField k :=
  T (Base k) - includeBase k (Matrix.det (rationalM k)) / T (Base k)

/--
@isnad1 id=eq.0h1v.s7.716212dfbc4f from=translated src=- shape=303a3d49 vocab=2789bfd5
-/
theorem kappa_eq_orientation :
    kappa k = AlbertLean.Residual.FrameIdeal.orientation (genericChart k) := by
  change includeBase k (ι k (c k) - ι k (a k) * ι k (b k)) =
    1 * includeBase k (ι k (c k)) - includeBase k (ι k (b k)) *
      includeBase k (ι k (a k))
  simp only [map_sub, map_mul, one_mul]
  ring

/--
@isnad1 id=ne.0h1v.s9.29e9c0deb294 from=translated src=- shape=37fa0090 vocab=8210fa59
-/
theorem kappa_ne_zero : kappa k ≠ 0 := by
  rw [kappa_eq_orientation]
  exact generic_orientation_ne k

/--
@isnad1 id=ne.0h1v.s9.49cc44ed1f6b from=translated src=- shape=37fa0090 vocab=6a459a2e
-/
theorem eta_ne_zero : eta k ≠ 0 := by
  intro h
  apply branchPolynomial_ne_zero (Base k) (Matrix.det (rationalM k))
  have ht := T_ne_zero (Base k)
  have he : T (Base k) = includeBase k (Matrix.det (rationalM k)) / T (Base k) :=
    sub_eq_zero.mp h
  have hh := (eq_div_iff ht).mp he
  simpa only [pow_two, sub_eq_zero, includeBase] using hh

/--
@isnad1 id=eq.0h1v.s13.cd4c8821b044 from=translated src=- shape=d859ff64 vocab=8cccfe7c
-/
@[simp] theorem nu_kappa : nu k (kappa k) = -kappa k := by
  rw [kappa, nu_base, reorient_orientation, map_neg]

/--
@isnad1 id=eq.0h1v.s13.f44101049280 from=translated src=- shape=53f1d7f8 vocab=421ac7eb
-/
@[simp] theorem deck_kappa : deck k (kappa k) = kappa k := deck_base k _

/--
@isnad1 id=eq.0h1v.s13.94ea0e5db968 from=translated src=- shape=53f1d7f8 vocab=e5ea75f6
-/
@[simp] theorem nu_eta : nu k (eta k) = eta k := by
  simp only [eta, map_sub, map_div₀, nu_T, nu_base, reorient_det_rationalM]

/--
@isnad1 id=eq.0h1v.s13.26b63f36182a from=translated src=- shape=d859ff64 vocab=c43f62b8
-/
@[simp] theorem deck_eta : deck k (eta k) = -eta k := by
  have hm : includeBase k (Matrix.det (rationalM k)) ≠ 0 :=
    (map_ne_zero (includeBase k)).mpr (det_rationalM_ne_zero k)
  have ht : deck k (T (Base k)) =
      includeBase k (Matrix.det (rationalM k)) / T (Base k) := deck_Delta k
  simp only [eta, map_sub, map_div₀, ht, deck_base]
  rw [div_div_cancel₀ hm]
  ring

/--
@isnad1 id=eq.0h1v.s13.898a4e02e398 from=translated src=- shape=d859ff64 vocab=980a8d8c
-/
@[simp] theorem tau_kappa : tau k (kappa k) = -kappa k := by
  rw [tau_apply, nu_kappa, map_neg, deck_kappa]

/--
@isnad1 id=eq.0h1v.s13.0602de2b651b from=translated src=- shape=d859ff64 vocab=dc9128e5
-/
@[simp] theorem tau_eta : tau k (eta k) = -eta k := by
  rw [tau_apply, nu_eta, deck_eta]

/--
@isnad1 id=eq.0h2v.s13.e631745d84ca from=translated src=- shape=4789a508 vocab=b328bcd3
-/
@[simp] theorem tau_constant (z : k) :
    tau k (algebraMap k (FunctionField k) z) = algebraMap k (FunctionField k) z := by
  rw [tau_apply, nu_constant, IsScalarTower.algebraMap_apply k (Base k) (FunctionField k)]
  exact deck_base k _

end AlbertLean.Generic.GenericFieldSymmetries
