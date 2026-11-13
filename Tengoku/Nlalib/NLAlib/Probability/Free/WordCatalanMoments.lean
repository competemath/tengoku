import Tengoku.Nlalib.NLAlib.Probability.Free.WordFieldCommutation
import Tengoku.Nlalib.NLAlib.ForMathlib.Algebra.Ring.CommutatorPower
import Tengoku.Nlalib.NLAlib.ForMathlib.Combinatorics.Enumerative.CatalanRecurrence

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Actual single-field vacuum moments are the even Catalan sequence

The actual left-annihilation/right-field commutator is the rank-one vacuum
projection. Its finite power commutator and the projection's genuine vacuum
factorization give the exact Catalan convolution recursion for the concrete
operators. This derives all moments without a distribution or moment premise.

Source: Nica--Speicher, Lectures on the Combinatorics of Free Probability,
the full-Fock realization of Proposition 7.16.
-/

noncomputable section
set_option autoImplicit false
open scoped Classical InnerProduct

namespace NLAlib

variable {ι : Type*}
local notation "B" => WordHilbertSpace ι →L[ℂ] WordHilbertSpace ι

/-- The mixed left-annihilation/right-field commutator is its actual
Kronecker coefficient times the vacuum rank-one projection.
@isnad1 id=eq.0h3v.s15.99ba84005eff from=translated src=- shape=88f94bea vocab=33e37a7d
-/
theorem wordAnnihilation_mul_wordRightField_sub (i j : ι) :
    wordAnnihilation i * wordRightField j - wordRightField j * wordAnnihilation i =
      if i = j then wordVacuumProjection ι else 0 := by
  have hAA : Commute (wordAnnihilation i) (wordRightAnnihilation j) := by
    simpa only [wordAnnihilation, wordRightAnnihilation,
      ← ContinuousLinearMap.star_eq_adjoint] using
      (commute_wordCreation_wordRightCreation i j).star_star
  calc
    _ = (wordAnnihilation i * (wordRightCreation j).toContinuousLinearMap -
        (wordRightCreation j).toContinuousLinearMap * wordAnnihilation i) +
        (wordAnnihilation i * wordRightAnnihilation j -
          wordRightAnnihilation j * wordAnnihilation i) := by
      unfold wordRightField
      noncomm_ring
    _ = _ := by rw [hAA.eq, sub_self, add_zero, wordAnnihilation_mul_wordRightCreation_sub]

/-- Left and right powers have the same actual vacuum vector because the
fields commute and have identical action on that vacuum.
@isnad1 id=eq.0h3v.s15.b5a71a1f589b from=translated src=- shape=b43c83fc vocab=08f7984d
-/
theorem wordField_pow_wordVacuum_eq_wordRightField_pow (i : ι) (n : ℕ) :
    (wordField i ^ n) (wordVacuum ι) = (wordRightField i ^ n) (wordVacuum ι) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      wordField_wordVacuum, ← wordRightField_wordVacuum]
    have h := congrArg (fun T : B => T (wordVacuum ι))
      ((commute_wordField_wordRightField i i).pow_left n).eq
    change (wordField i ^ n) (wordRightField i (wordVacuum ι)) =
      wordRightField i ((wordField i ^ n) (wordVacuum ι)) at h
    rw [h, ih]
    simp only [pow_succ', ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply]

/-- The actual right-field and left-field powers have the same vacuum
expectation; no distributional equality premise is supplied.
@isnad1 id=eq.0h3v.s16.c7d2df040cf7 from=translated src=- shape=95a56f95 vocab=058f4b3b
-/
theorem wordVacuumExpectation_wordRightField_pow_eq (i : ι) (n : ℕ) :
    wordVacuumExpectation ι (wordRightField i ^ n) =
      wordVacuumExpectation ι (wordField i ^ n) := by
  rw [wordVacuumExpectation_apply, wordVacuumExpectation_apply,
    ← wordField_pow_wordVacuum_eq_wordRightField_pow]

/-- Inserting the actual rank-one vacuum projection factors its matrix
coefficient into the two genuine vacuum expectations.
@isnad1 id=eq.0h3v.s16.b803c513c1d8 from=translated src=- shape=a34fb3b4 vocab=c36469d1
-/
theorem wordVacuumExpectation_mul_projection_mul (S T : B) :
    wordVacuumExpectation ι (S * wordVacuumProjection ι * T) =
      wordVacuumExpectation ι S * wordVacuumExpectation ι T := by
  simp only [wordVacuumExpectation_apply, ContinuousLinearMap.mul_def,
    ContinuousLinearMap.comp_apply, wordVacuumProjection, InnerProductSpace.rankOne_apply,
    map_smul, inner_smul_right]
  exact mul_comm _ _

private theorem wordVacuumExpectation_wordField_mul_eq_annihilation (i : ι) (T : B) :
    wordVacuumExpectation ι (wordField i * T) =
      wordVacuumExpectation ι (wordAnnihilation i * T) := by
  have hCreation : wordVacuumExpectation ι ((wordCreation i).toContinuousLinearMap * T) = 0 := by
    rw [wordVacuumExpectation_apply, ContinuousLinearMap.mul_def, ContinuousLinearMap.comp_apply,
      ← ContinuousLinearMap.adjoint_inner_left (wordCreation i).toContinuousLinearMap
        (T (wordVacuum ι)) (wordVacuum ι)]
    change inner ℂ (wordAnnihilation i (wordVacuum ι)) (T (wordVacuum ι)) = 0
    simp only [wordAnnihilation_wordVacuum, inner_zero_left]
  rw [wordField, add_mul, map_add, hCreation, zero_add]

/-- The actual concrete-field moments satisfy the exact Catalan convolution
recursion, derived from the mixed vacuum defect and not assumed as a law.
@isnad1 id=eq.0h3v.s16.3494b8827760 from=translated src=- shape=b1905449 vocab=8a2a2bef
-/
theorem wordVacuumExpectation_wordField_pow_succ_succ (i : ι) (n : ℕ) :
    wordVacuumExpectation ι (wordField i ^ (n + 2)) =
      ∑ k ∈ Finset.range (n + 1), wordVacuumExpectation ι (wordField i ^ k) *
        wordVacuumExpectation ι (wordField i ^ (n - k)) := by
  have hDef : wordAnnihilation i * wordRightField i -
      wordRightField i * wordAnnihilation i = wordVacuumProjection ι := by
    simpa using wordAnnihilation_mul_wordRightField_sub i i
  have hPow := mul_pow_sub_pow_mul_eq_sum (wordAnnihilation i) (wordRightField i) (n + 1)
  rw [hDef] at hPow
  have hPhi := congrArg (wordVacuumExpectation ι) hPow
  simp only [map_sub, map_sum, Nat.add_sub_cancel] at hPhi
  have hKill : wordVacuumExpectation ι (wordRightField i ^ (n + 1) * wordAnnihilation i) = 0 := by
    simp only [wordVacuumExpectation_apply, ContinuousLinearMap.mul_def,
      ContinuousLinearMap.comp_apply, wordAnnihilation_wordVacuum, map_zero, inner_zero_right]
  rw [hKill, sub_zero] at hPhi
  simp_rw [wordVacuumExpectation_mul_projection_mul,
    wordVacuumExpectation_wordRightField_pow_eq] at hPhi
  calc
    _ = wordVacuumExpectation ι (wordField i * wordField i ^ (n + 1)) := by
      rw [← pow_succ']
    _ = wordVacuumExpectation ι (wordAnnihilation i * wordField i ^ (n + 1)) :=
      wordVacuumExpectation_wordField_mul_eq_annihilation i _
    _ = wordVacuumExpectation ι (wordAnnihilation i * wordRightField i ^ (n + 1)) := by
      simp only [wordVacuumExpectation_apply, ContinuousLinearMap.mul_def,
        ContinuousLinearMap.comp_apply]
      rw [wordField_pow_wordVacuum_eq_wordRightField_pow]
    _ = _ := hPhi

/-- Every single-field vacuum moment is derived exactly: odd powers have
expectation zero and the `2k`-th moment is the native Catalan number `catalan k`.
This includes the zeroth moment and assumes no distribution or moment formula.
@isnad1 id=eq.0h3v.s15.d56f2a3679dd from=translated src=- shape=034d301e vocab=54041a68
-/
theorem wordVacuumExpectation_wordField_pow_eq (i : ι) (n : ℕ) :
    wordVacuumExpectation ι (wordField i ^ n) =
      if Even n then (catalan (n / 2) : ℂ) else 0 := by
  exact eq_ite_even_catalan_of_recursion
    (fun n => wordVacuumExpectation ι (wordField i ^ n))
    (by simp) (by simpa only [pow_one] using wordVacuumExpectation_wordField i)
    (wordVacuumExpectation_wordField_pow_succ_succ i) n

/-- The native even Catalan moments of the actual concrete self-adjoint field.
@isnad1 id=eq.0h3v.s15.30b7d3f12d72 from=translated src=- shape=4f02d08f vocab=a0ab6cf5
-/
theorem wordVacuumExpectation_wordField_pow_even (i : ι) (k : ℕ) :
    wordVacuumExpectation ι (wordField i ^ (2 * k)) = (catalan k : ℂ) := by
  rw [wordVacuumExpectation_wordField_pow_eq,
    ite_eq_left (Nat.even_iff.mpr (by omega)), show (2 * k) / 2 = k by omega]

/-- All actual odd moments of the concrete self-adjoint field vanish.
@isnad1 id=eq.0h3v.s15.3b4758f1106e from=translated src=- shape=9b378ece vocab=00d368f9
-/
theorem wordVacuumExpectation_wordField_pow_odd (i : ι) (k : ℕ) :
    wordVacuumExpectation ι (wordField i ^ (2 * k + 1)) = 0 := by
  rw [wordVacuumExpectation_wordField_pow_eq, ite_eq_right (Nat.not_even_two_mul_add_one k)]

end NLAlib
