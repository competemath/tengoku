import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SourceEvenAutomorphism

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms norm_center` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms center_root` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms center_eq` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms familyAut` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Rational coordinates for the even-action family

The chart solves the norm-product root equation with eight free
coordinates. Its coverage statement retains the chosen root sign and
requires the displayed nonzero pivot. Localization and invariant
transport are treated separately.
-/
noncomputable section
namespace AlbertLean.Triality.RationalEvenFamily

open ExteriorSix CoordinateTensor SourceEvenAutomorphism

universe u
variable {K : Type u} [Field K] [CharZero K]
local instance : Invertible (2 : K) := invertibleOfNonzero (by norm_num)

/-- Eight free coordinates when alpha is fixed: r, six exterior entries, rho.-/
def center (alpha r : K) (omega : W K) (rho : K) : VCoord K :=
  { r := r, z := (rho ^ 2 / alpha - Pf omega) / r, omega := omega }

theorem norm_center (alpha r : K) (omega : W K) (rho : K) (hr : r ≠ 0) :
    nV (center alpha r omega rho) = rho ^ 2 / alpha := by
  change r * ((rho ^ 2 / alpha - Pf omega) / r) + Pf omega = rho ^ 2 / alpha
  rw [mul_div_cancel₀ _ hr]
  ring

theorem center_root (alpha r : K) (omega : W K) (rho : K)
    (ha : alpha ≠ 0) (hr : r ≠ 0) :
    rho ^ 2 = alpha * nV (center alpha r omega rho) := by
  rw [norm_center alpha r omega rho hr]
  exact (mul_div_cancel₀ _ ha).symm

theorem norm_center_ne_zero (alpha r : K) (omega : W K) (rho : K)
    (ha : alpha ≠ 0) (hr : r ≠ 0) (hp : rho ≠ 0) :
    nV (center alpha r omega rho) ≠ 0 := by
  rw [norm_center alpha r omega rho hr]
  exact div_ne_zero (pow_ne_zero 2 hp) ha

/-- Every actual root-bearing center with nonzero r is in this chart,
including its specified rho sign.-/
theorem center_eq (alpha : K) (B : VCoord K) (rho : K)
    (ha : alpha ≠ 0) (hr : B.r ≠ 0)
    (hroot : rho ^ 2 = alpha * nV B) :
    center alpha B.r B.omega rho = B := by
  have hn : nV B = rho ^ 2 / alpha :=
    (eq_div_iff ha).2 (by simpa only [mul_comm] using hroot.symm)
  apply VCoord.ext
  · rfl
  · change (rho ^ 2 / alpha - Pf B.omega) / B.r = B.z
    apply (div_eq_iff hr).2
    rw [← hn]
    change B.r * B.z + Pf B.omega - Pf B.omega = B.z * B.r
    ring
  · rfl

/-- This is the existing genuine source product automorphism, with its root
relation proved by the rational chart rather than supplied as a new premise.-/
def familyAut (A : VCoord K) (hA : nV A ≠ 0)
    (r : K) (omega : W K) (rho : K) (hr : r ≠ 0) (hp : rho ≠ 0) :=
  sourceEvenAut A (center (nV A) r omega rho) rho hA
    (norm_center_ne_zero (nV A) r omega rho hA hr hp)
    (center_root (nV A) r omega rho hA hr) hp

end AlbertLean.Triality.RationalEvenFamily
