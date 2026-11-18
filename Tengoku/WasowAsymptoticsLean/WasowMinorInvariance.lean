import Tengoku.WasowAsymptoticsLean.WasowMinorExpansion
import Tengoku.WasowAsymptoticsLean.WasowReductionDescent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms WasowMinorInvariance.minorGCD_dvd_left_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMinorInvariance.minorGCD_dvd_right_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMinorInvariance.minorGCD_left_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMinorInvariance.minorGCD_right_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMinorInvariance.minorGCD_equivalent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMinorInvariance.minorDegree_equivalent` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms WasowMinorInvariance.degreeMass_equivalent` (it only prints; the queue checks the axioms of every declaration). -/

/-! Exact determinantal-divisor invariance under invertible polynomial row
and column operations. This includes the unimodular transformations used in
reducing characteristic pencils; no assumed invariant-preservation property
is supplied by the caller. -/
set_option autoImplicit false
noncomputable section
open Matrix Polynomial
namespace WasowMinorInvariance
open WasowReductionDescent WasowMinorExpansion
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Left multiplication can only increase the divisibility of minor gcds.
@isnad1 id=dvd.0h4v.s6.ee04ca681350 from=translated src=- shape=770d662f vocab=5f547e2a
-/
theorem minorGCD_dvd_left_mul (A T : Matrix ι ι (Polynomial ℂ)) (k : ℕ) :
    minorGCD T k ∣ minorGCD (A*T) k := by
  rw [dvd_minorGCD_iff]
  exact dvd_minor_mul A T k (minorGCD T k) (minorGCD_dvd_minor T k)

/-- The analogous statement for right multiplication.
@isnad1 id=dvd.0h4v.s6.bd7bdf59daf0 from=translated src=- shape=2f9bc693 vocab=5f547e2a
-/
theorem minorGCD_dvd_right_mul (T A : Matrix ι ι (Polynomial ℂ)) (k : ℕ) :
    minorGCD T k ∣ minorGCD (T*A) k := by
  rw [dvd_minorGCD_iff]
  exact dvd_minor_mul_left T A k (minorGCD T k) (minorGCD_dvd_minor T k)

/-- Exact normalized gcd invariance under a polynomial left inverse.
@isnad1 id=eq.1h5v.s7.694e55c862d1 from=translated src=- shape=c531fe41 vocab=e7260a3f
-/
theorem minorGCD_left_mul (A S T : Matrix ι ι (Polynomial ℂ))
    (hSA : S*A=1) (k : ℕ) : minorGCD (A*T) k = minorGCD T k := by
  have hnorm (U : Matrix ι ι (Polynomial ℂ)) : normalize (minorGCD U k) = minorGCD U k :=
    Finset.normalize_gcd
  apply dvd_antisymm_of_normalize_eq (hnorm _) (hnorm _)
  · have h := minorGCD_dvd_left_mul S (A*T) k
    simpa only [← Matrix.mul_assoc, hSA, Matrix.one_mul] using h
  · exact minorGCD_dvd_left_mul A T k

/-- Exact normalized gcd invariance under a polynomial right inverse.
@isnad1 id=eq.1h5v.s7.751e2314109e from=translated src=- shape=6f2b3763 vocab=e7260a3f
-/
theorem minorGCD_right_mul (T A S : Matrix ι ι (Polynomial ℂ))
    (hAS : A*S=1) (k : ℕ) : minorGCD (T*A) k = minorGCD T k := by
  have hnorm (U : Matrix ι ι (Polynomial ℂ)) : normalize (minorGCD U k) = minorGCD U k :=
    Finset.normalize_gcd
  apply dvd_antisymm_of_normalize_eq (hnorm _) (hnorm _)
  · have h := minorGCD_dvd_right_mul (T*A) S k
    simpa only [Matrix.mul_assoc, hAS, Matrix.mul_one] using h
  · exact minorGCD_dvd_right_mul T A k

/-- Both sides may be transformed by actual unimodular polynomial matrices.
@isnad1 id=eq.2h7v.s8.6ab5ed711c12 from=translated src=- shape=330a00a2 vocab=e7260a3f
-/
theorem minorGCD_equivalent (L Linv T R Rinv : Matrix ι ι (Polynomial ℂ))
    (hL : Linv*L=1) (hR : R*Rinv=1) (k : ℕ) :
    minorGCD (L*T*R) k = minorGCD T k := by
  rw [minorGCD_right_mul (L*T) R Rinv hR, minorGCD_left_mul L Linv T hL]

/-- The degree invariant used in descent is consequently basis independent.
@isnad1 id=eq.2h7v.s8.41c7522a71b2 from=translated src=- shape=11e0a653 vocab=8d0cc06a
-/
theorem minorDegree_equivalent (L Linv T R Rinv : Matrix ι ι (Polynomial ℂ))
    (hL : Linv*L=1) (hR : R*Rinv=1) (k : ℕ) :
    (minorGCD (L*T*R) k).natDegree = (minorGCD T k).natDegree := by
  rw [minorGCD_equivalent L Linv T R Rinv hL hR k]

/-- The complete finite degree mass is unchanged by unimodular equivalence.
@isnad1 id=eq.2h6v.s8.a6b1ac60f5df from=translated src=- shape=f4eb89f3 vocab=668bcba7
-/
theorem degreeMass_equivalent {n : ℕ}
    (L Linv T R Rinv : Matrix (Fin n) (Fin n) (Polynomial ℂ))
    (hL : Linv*L=1) (hR : R*Rinv=1) :
    degreeMass (L*T*R) = degreeMass T := by
  unfold degreeMass
  apply Finset.sum_congr rfl
  intro k _
  exact minorDegree_equivalent L Linv T R Rinv hL hR k.val

end WasowMinorInvariance

