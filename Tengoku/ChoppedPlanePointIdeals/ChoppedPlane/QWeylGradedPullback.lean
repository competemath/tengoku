module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylQuartic
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylGrading
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QuarticSubstitution

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Actual quartic semilinear pullback, with its exact weighted degrees. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open MvPolynomial
variable {K : Type*} [Field K]
set_option maxHeartbeats 1200000

def profileMultiplicity : CubicProfile → ℕ
  | .degreeThree => 3
  | .degreeTwo => 2
  | .degreeOne => 1

def quarticRootMultiplier : BinaryRing K := binaryU K ^ 3 - binaryV K ^ 3

/--
@isnad1 id=eq.0h1v.s8.9a353198db42 from=translated src=- shape=9b56b64b vocab=242c1797
-/
theorem quarticSubstitution_cubic :
    quarticSubstitution K (binaryCubic K) =
      binaryCubic K * quarticRootMultiplier (K := K) ^ 3 := by
  simpa [binaryCubic, quarticRootMultiplier] using
    quartic_binary_cubic (binaryU K) (binaryV K)

def quarticCubicHom :
    CyclicCubicRing (BinaryRing K) (binaryCubic K) →+*
      CyclicCubicRing (BinaryRing K) (binaryCubic K) :=
  cyclicScaledBaseChangeHom (quarticSubstitution K).toRingHom
    (binaryCubic K) (binaryCubic K) quarticRootMultiplier quarticSubstitution_cubic

/--
@isnad1 id=eq.0h1v.s11.dbeea6e24392 from=translated src=- shape=7572838b vocab=aacfca20
-/
@[simp] theorem quarticCubicHom_root :
    quarticCubicHom (K := K) (cyclicRoot (binaryCubic K)) =
      cyclicCoefficientHom (binaryCubic K) quarticRootMultiplier * cyclicRoot (binaryCubic K) :=
  cyclicScaledBaseChangeHom_root _ _ _ _ _

/--
@isnad1 id=eq.0h2v.s11.158a75b6307e from=translated src=- shape=4eb1de1c vocab=8dc1a923
-/
@[simp] theorem quarticCubicHom_coefficient (b : BinaryRing K) :
    quarticCubicHom (K := K) (cyclicCoefficientHom (binaryCubic K) b) =
      cyclicCoefficientHom (binaryCubic K) (quarticSubstitution K b) :=
  cyclicScaledBaseChangeHom_coefficient _ _ _ _ _ b

def binaryProfilePullbackWeights (q : K) (s : CubicProfile) : Fin 3 → BinaryRing K :=
  profilePullbackWeights (binaryU K) (binaryV K) (C q) s

def binaryProfileDualPullbackWeights (q : K) (s : CubicProfile) : Fin 3 → BinaryRing K :=
  profileDualPullbackWeights (binaryU K) (binaryV K) (C q) s

def profilePullback (q : K) (s : CubicProfile) :
    BinaryVector K →ₛₗ[(quarticSubstitution K).toRingHom] BinaryVector K :=
  weightedVectorBaseChange (quarticSubstitution K).toRingHom
    (binaryProfilePullbackWeights q s)

def profileDualPullback (q : K) (s : CubicProfile) :
    BinaryVector K →ₛₗ[(quarticSubstitution K).toRingHom] BinaryVector K :=
  weightedVectorBaseChange (quarticSubstitution K).toRingHom
    (binaryProfileDualPullbackWeights q s)

/--
@isnad1 id=eq.0h3v.s7.5113e7ffd911 from=translated src=- shape=5690fb71 vocab=77b9aa10
-/
theorem profileFactors_eq_cyclicCoefficients (q : K) (s : CubicProfile) :
    profileFactors q s = cyclicProfileCoefficients (binaryU K) (binaryV K) (C q) s := by
  funext i
  cases s <;> fin_cases i <;>
    simp [profileFactors, cubicLinearFactors, cyclicProfileCoefficients, map_pow]

/--
@isnad1 id=eq.0h4v.s9.0e88e8478302 from=translated src=- shape=a11b433e vocab=1e8eca56
-/
theorem quarticSubstitution_profileFactors (q : K) (s : CubicProfile) (i : Fin 3) :
    quarticSubstitution K (profileFactors q s i) =
      cyclicProfileCoefficients (quarticU (binaryU K) (binaryV K))
        (quarticV (binaryU K) (binaryV K)) (C q) s i := by
  cases s <;> fin_cases i <;>
    simp [profileFactors, cubicLinearFactors, cyclicProfileCoefficients, map_pow]

/--
@isnad1 id=eq.1h4v.s12.b39257c57590 from=translated src=- shape=282c4709 vocab=7584d404
-/
theorem profilePullback_intertwines (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : BinaryVector K) :
    profilePullback q s (cyclicZ (profileFactors q s) m) =
      quarticRootMultiplier (K := K) • cyclicZ (profileFactors q s) (profilePullback q s m) := by
  refine weightedVectorBaseChange_cyclicZ (quarticSubstitution K).toRingHom
    (profileFactors q s) (profileFactors q s) (binaryProfilePullbackWeights q s)
    (quarticRootMultiplier (K := K)) ?_ m
  intro i
  have hq' : (C q : BinaryRing K) ^ 2 + C q + 1 = 0 := by
    simpa using congrArg (C : K →+* BinaryRing K) hq
  change quarticSubstitution K (profileFactors q s i) *
    binaryProfilePullbackWeights q s (cyclicNext i) = _
  rw [quarticSubstitution_profileFactors, profileFactors_eq_cyclicCoefficients]
  simpa only [binaryProfilePullbackWeights, quarticRootMultiplier] using
    profilePullbackWeights_intertwine (binaryU K) (binaryV K) (C q) hq' s i

/--
@isnad1 id=eq.1h4v.s12.62184ea4587f from=translated src=- shape=282c4709 vocab=a2fac1d5
-/
theorem profileDualPullback_intertwines (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : BinaryVector K) :
    profileDualPullback q s (cyclicZDual (profileFactors q s) m) =
      quarticRootMultiplier (K := K) • cyclicZDual (profileFactors q s) (profileDualPullback q s m) := by
  refine weightedVectorBaseChange_cyclicZDual (quarticSubstitution K).toRingHom
    (profileFactors q s) (profileFactors q s) (binaryProfileDualPullbackWeights q s)
    (quarticRootMultiplier (K := K)) ?_ m
  intro i
  have hq' : (C q : BinaryRing K) ^ 2 + C q + 1 = 0 := by
    simpa using congrArg (C : K →+* BinaryRing K) hq
  change quarticSubstitution K (profileFactors q s i) *
    binaryProfileDualPullbackWeights q s i = _
  rw [quarticSubstitution_profileFactors, profileFactors_eq_cyclicCoefficients]
  simpa only [binaryProfileDualPullbackWeights, quarticRootMultiplier] using
    profileDualPullbackWeights_intertwine (binaryU K) (binaryV K) (C q) hq' s i

def profileModulePullback (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZ (profileFactors q s))
      (profileZ_cube q hq s)
    BinaryVector K →ₛₗ[quarticCubicHom (K := K)] BinaryVector K :=
  cyclicModuleScaledBaseChange (quarticSubstitution K).toRingHom
    (binaryCubic K) (binaryCubic K) quarticRootMultiplier quarticSubstitution_cubic
    (profilePullback q s) (cyclicZ (profileFactors q s)) (cyclicZ (profileFactors q s))
    (profileZ_cube q hq s) (profileZ_cube q hq s) (profilePullback_intertwines q hq s)

def profileDualModulePullback (q : K) (hq : q ^ 2 + q + 1 = 0) (s : CubicProfile) :
    letI := cyclicModuleStructure (binaryCubic K) (cyclicZDual (profileFactors q s))
      (profileZDual_cube q hq s)
    BinaryVector K →ₛₗ[quarticCubicHom (K := K)] BinaryVector K :=
  cyclicModuleScaledBaseChange (quarticSubstitution K).toRingHom
    (binaryCubic K) (binaryCubic K) quarticRootMultiplier quarticSubstitution_cubic
    (profileDualPullback q s) (cyclicZDual (profileFactors q s)) (cyclicZDual (profileFactors q s))
    (profileZDual_cube q hq s) (profileZDual_cube q hq s) (profileDualPullback_intertwines q hq s)

/--
@isnad1 id=eq.1h4v.s11.99b90a9d3870 from=translated src=- shape=d09d2545 vocab=5e6f9226
-/
@[simp] theorem profileModulePullback_apply (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : BinaryVector K) :
    profileModulePullback q hq s m = profilePullback q s m := rfl

/--
@isnad1 id=eq.1h4v.s11.2e75a16e4580 from=translated src=- shape=d09d2545 vocab=ffb605f1
-/
@[simp] theorem profileDualModulePullback_apply (q : K) (hq : q ^ 2 + q + 1 = 0)
    (s : CubicProfile) (m : BinaryVector K) :
    profileDualModulePullback q hq s m = profileDualPullback q s m := rfl

/--
@isnad1 id=ne.0h2v.s8.88ee3426b689 from=translated src=- shape=28d0d210 vocab=32cbb8d0
-/
theorem binaryLinearDifference_ne_zero (q : K) :
    binaryU K - C q * binaryV K ≠ 0 := by
  intro h
  have he := congrArg (MvPolynomial.eval ![(1 : K), 0]) h
  simp [binaryU, binaryV] at he

/--
@isnad1 id=ne.0h4v.s6.45f6712be146 from=translated src=- shape=4ed6fc46 vocab=c6825d76
-/
theorem binaryProfilePullbackWeights_ne_zero (q : K) (s : CubicProfile) (i : Fin 3) :
    binaryProfilePullbackWeights q s i ≠ 0 := by
  have h0 := binaryLinearDifference_ne_zero (K := K) 1
  have h1 := binaryLinearDifference_ne_zero (K := K) q
  have h2 := binaryLinearDifference_ne_zero (K := K) (q ^ 2)
  simp only [map_one, one_mul] at h0
  rw [map_pow] at h2
  cases s <;> fin_cases i <;>
    simp [binaryProfilePullbackWeights, profilePullbackWeights, weightZero, weightOne,
      weightTwo, h0, h1, h2]

/--
@isnad1 id=ne.0h4v.s6.c71836954d1e from=translated src=- shape=4ed6fc46 vocab=3c73c0a5
-/
theorem binaryProfileDualPullbackWeights_ne_zero (q : K) (s : CubicProfile) (i : Fin 3) :
    binaryProfileDualPullbackWeights q s i ≠ 0 := by
  have h0 := binaryLinearDifference_ne_zero (K := K) 1
  have h1 := binaryLinearDifference_ne_zero (K := K) q
  have h2 := binaryLinearDifference_ne_zero (K := K) (q ^ 2)
  simp only [map_one, one_mul] at h0
  rw [map_pow] at h2
  cases s <;> fin_cases i <;>
    simp [binaryProfileDualPullbackWeights, profileDualPullbackWeights, h0, h1, h2]

/--
@isnad1 id=injectiv.0h3v.s10.e0dbd6d93ed0 from=translated src=- shape=c8a976bf vocab=12fda0dc
-/
theorem profilePullback_injective [CharZero K] (q : K) (s : CubicProfile) :
    Function.Injective (profilePullback q s) :=
  weightedVectorBaseChange_injective _ quarticSubstitution_injective _
    (binaryProfilePullbackWeights_ne_zero q s)

/--
@isnad1 id=injectiv.0h3v.s10.a9e12b66a145 from=translated src=- shape=c8a976bf vocab=b84b06fd
-/
theorem profileDualPullback_injective [CharZero K] (q : K) (s : CubicProfile) :
    Function.Injective (profileDualPullback q s) :=
  weightedVectorBaseChange_injective _ quarticSubstitution_injective _
    (binaryProfileDualPullbackWeights_ne_zero q s)

def pullbackWeightDegrees (s : CubicProfile) (i : Fin 3) : ℕ :=
  profileMultiplicity s + 3 * generatorWeights s i

def dualPullbackWeightDegrees (s : CubicProfile) (i : Fin 3) : ℕ :=
  3 * dualGeneratorWeights s i - profileMultiplicity s

/--
@isnad1 id=ishomoge.0h2v.s8.6eec6694de4f from=translated src=- shape=2c81f7c2 vocab=df0a6f98
-/
theorem binaryLinearDifference_homogeneous (q : K) :
    (binaryU K - C q * binaryV K).IsHomogeneous 1 :=
  (isHomogeneous_X K 0).sub ((isHomogeneous_X K 1).C_mul q)

/--
@isnad1 id=ishomoge.0h4v.s5.3485f801e09f from=translated src=- shape=3e60f262 vocab=62c79731
-/
theorem binaryProfilePullbackWeights_homogeneous (q : K) (s : CubicProfile) (i : Fin 3) :
    (binaryProfilePullbackWeights q s i).IsHomogeneous (pullbackWeightDegrees s i) := by
  have h0 : (binaryU K - binaryV K).IsHomogeneous 1 :=
    (isHomogeneous_X K 0).sub (isHomogeneous_X K 1)
  have h1 := binaryLinearDifference_homogeneous (K := K) q
  have h2 := binaryLinearDifference_homogeneous (K := K) (q ^ 2)
  rw [map_pow] at h2
  cases s <;> fin_cases i
  · exact (h0.pow 2).mul h1
  · exact (h1.pow 2).mul h2
  · exact (h2.pow 2).mul h0
  · exact h0.pow 2
  · exact h1.mul h2
  · exact ((h2.pow 2).mul h0).mul (h1.pow 2)
  · exact h1
  · exact (h0.mul (h1.pow 2)).mul h2
  · exact (h0.pow 2).mul (h2.pow 2)

/--
@isnad1 id=ishomoge.0h4v.s5.e5ec6d938bb1 from=translated src=- shape=3e60f262 vocab=8f2067a1
-/
theorem binaryProfileDualPullbackWeights_homogeneous (q : K) (s : CubicProfile) (i : Fin 3) :
    (binaryProfileDualPullbackWeights q s i).IsHomogeneous (dualPullbackWeightDegrees s i) := by
  have h0 : (binaryU K - binaryV K).IsHomogeneous 1 :=
    (isHomogeneous_X K 0).sub (isHomogeneous_X K 1)
  have h1 := binaryLinearDifference_homogeneous (K := K) q
  have h2 := binaryLinearDifference_homogeneous (K := K) (q ^ 2)
  rw [map_pow] at h2
  cases s <;> fin_cases i
  · exact h1.mul (h2.pow 2)
  · exact h2.mul (h0.pow 2)
  · exact h0.mul (h1.pow 2)
  · exact (h1.pow 2).mul (h2.pow 2)
  · exact (h1.mul h2).mul (h0.pow 2)
  · exact h0
  · exact ((h0.pow 2).mul h1).mul (h2.pow 2)
  · exact h0.mul h2
  · exact h1.pow 2

/-- Signed components, including negative degrees, pull back to four times
their original degree.
@isnad1 id=mem.1h3v.s9.ebe23ae88c2f from=translated src=- shape=f52cd67e vocab=f350cf5f
-/
theorem quarticSubstitution_mem_signedForms {t : ℤ} {p : BinaryRing K}
    (hp : p ∈ signedForms K 2 t) :
    quarticSubstitution K p ∈ signedForms K 2 (4 * t) := by
  by_cases ht : 0 ≤ t
  · have h4 : 0 ≤ 4 * t := by omega
    have hf : p.IsHomogeneous t.toNat := by simpa [signedForms, ht] using hp
    have hnat : (4 * t).toNat = 4 * t.toNat := by omega
    simpa [signedForms, h4, hnat] using quarticSubstitution_homogeneous hf
  · have hp0 : p = 0 := by simpa [signedForms, ht] using hp
    simp [hp0]

/-- The quartic coefficient map with fixed component multipliers is linear
for the original coefficient field.-/
def weightedQuarticLinear (ρ : Fin 3 → BinaryRing K) : BinaryVector K →ₗ[K] BinaryVector K :=
  LinearMap.pi fun i => (LinearMap.mulRight K (ρ i)).comp
    ((quarticSubstitution K).toLinearMap.comp (LinearMap.proj i))

/--
@isnad1 id=eq.0h4v.s9.ab195e3c8c13 from=translated src=- shape=7f85f644 vocab=c8184216
-/
@[simp] theorem weightedQuarticLinear_apply (ρ : Fin 3 → BinaryRing K)
    (m : BinaryVector K) (i : Fin 3) :
    weightedQuarticLinear ρ m i = quarticSubstitution K (m i) * ρ i := rfl

/-- The actual forward pullback has weighted degree `4*t+s`.-/
def gradedProfilePullback (q : K) (s : CubicProfile) (t : ℤ) :
    GradedBinaryVector (K := K) (generatorWeights s) t →ₗ[K]
      GradedBinaryVector (K := K) (generatorWeights s) (4 * t + profileMultiplicity s) :=
  LinearMap.pi fun i =>
    (((LinearMap.proj i).comp (weightedQuarticLinear (binaryProfilePullbackWeights q s))).comp
      (gradedBinaryVectorVal (generatorWeights s) t)).codRestrict
      (signedForms K 2 (4*t+profileMultiplicity s-generatorWeights s i)) (fun m => by
        change quarticSubstitution K (m i).val * binaryProfilePullbackWeights q s i ∈ _
        have hm := quarticSubstitution_mem_signedForms (m i).property
        have h := homogeneous_mul_mem_signedForms
          (binaryProfilePullbackWeights_homogeneous q s i) hm
        have he : 4 * (t - (generatorWeights s i : ℤ)) + (pullbackWeightDegrees s i : ℤ) =
            4 * t + profileMultiplicity s - generatorWeights s i := by
          simp only [pullbackWeightDegrees, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
          ring
        rw [he] at h
        simpa only [mul_comm] using h)

/-- The actual dual pullback has weighted degree `4*t-s`.-/
def gradedProfileDualPullback (q : K) (s : CubicProfile) (t : ℤ) :
    GradedBinaryVector (K := K) (dualGeneratorWeights s) t →ₗ[K]
      GradedBinaryVector (K := K) (dualGeneratorWeights s) (4 * t - profileMultiplicity s) :=
  LinearMap.pi fun i =>
    (((LinearMap.proj i).comp (weightedQuarticLinear (binaryProfileDualPullbackWeights q s))).comp
      (gradedBinaryVectorVal (dualGeneratorWeights s) t)).codRestrict
      (signedForms K 2 (4*t-profileMultiplicity s-dualGeneratorWeights s i)) (fun m => by
        change quarticSubstitution K (m i).val * binaryProfileDualPullbackWeights q s i ∈ _
        have hm := quarticSubstitution_mem_signedForms (m i).property
        have h := homogeneous_mul_mem_signedForms
          (binaryProfileDualPullbackWeights_homogeneous q s i) hm
        have hd : (dualPullbackWeightDegrees s i : ℤ) =
            3 * (dualGeneratorWeights s i : ℤ) - profileMultiplicity s := by
          cases s <;> fin_cases i <;>
            norm_num [dualPullbackWeightDegrees, dualGeneratorWeights,
              generatorWeights, profileMultiplicity]
        have he : 4 * (t - (dualGeneratorWeights s i : ℤ)) +
            (dualPullbackWeightDegrees s i : ℤ) =
            4 * t - profileMultiplicity s - dualGeneratorWeights s i := by rw [hd]; ring
        rw [he] at h
        simpa only [mul_comm] using h)

/--
@isnad1 id=eq.0h5v.s12.4b451041d7e7 from=translated src=- shape=b326066b vocab=5cb89cce
-/
@[simp] theorem gradedProfilePullback_val (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (generatorWeights s) t) :
    gradedBinaryVectorVal (generatorWeights s) (4*t+profileMultiplicity s)
      (gradedProfilePullback q s t m) =
    profilePullback q s (gradedBinaryVectorVal (generatorWeights s) t m) := rfl

/--
@isnad1 id=eq.0h5v.s12.6353979fd3ff from=translated src=- shape=b326066b vocab=dd71267a
-/
@[simp] theorem gradedProfileDualPullback_val (q : K) (s : CubicProfile) (t : ℤ)
    (m : GradedBinaryVector (K := K) (dualGeneratorWeights s) t) :
    gradedBinaryVectorVal (dualGeneratorWeights s) (4*t-profileMultiplicity s)
      (gradedProfileDualPullback q s t m) =
    profileDualPullback q s (gradedBinaryVectorVal (dualGeneratorWeights s) t m) := rfl

/--
@isnad1 id=injectiv.0h4v.s11.5cf35d21d6f0 from=translated src=- shape=ad3404aa vocab=a915670a
-/
theorem gradedProfilePullback_injective [CharZero K] (q : K) (s : CubicProfile) (t : ℤ) :
    Function.Injective (gradedProfilePullback (K := K) q s t) := by
  intro m n h
  apply gradedBinaryVectorVal_injective (generatorWeights s) t
  apply profilePullback_injective q s
  simpa using congrArg (gradedBinaryVectorVal (K := K) (generatorWeights s)
    (4*t+profileMultiplicity s)) h

/--
@isnad1 id=injectiv.0h4v.s11.b41a248615a6 from=translated src=- shape=ad3404aa vocab=f8dc0a92
-/
theorem gradedProfileDualPullback_injective [CharZero K] (q : K) (s : CubicProfile) (t : ℤ) :
    Function.Injective (gradedProfileDualPullback (K := K) q s t) := by
  intro m n h
  apply gradedBinaryVectorVal_injective (dualGeneratorWeights s) t
  apply profileDualPullback_injective q s
  simpa using congrArg (gradedBinaryVectorVal (K := K) (dualGeneratorWeights s)
    (4*t-profileMultiplicity s)) h

end ChoppedPlane.QWeyl
