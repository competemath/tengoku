import Tengoku.Nlalib.NLAlib.Probability.Free.WordMatrixVacuumCompression
import Tengoku.Nlalib.NLAlib.ForMathlib.Algebra.ResolventCommutator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The actual native free resolvent satisfies the matrix Dyson equation

The right-annihilator commutator is the true rank-one vacuum defect. Its
genuine resolvent commutator factors under vacuum compression, giving the
Dyson equation for the actual concrete operator resolvent. No moment,
limiting-law or Dyson-equation premise is supplied.

Source: the full-Fock realization of Nica--Speicher, Proposition 7.16;
the native free endpoint in Theorem 6.2 of arXiv:2108.06312v2.
-/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped Classical InnerProduct
namespace NLAlib
variable {D ι : Type*} [Fintype D] [DecidableEq D] [Fintype ι]
local notation "W" => WordHilbertSpace ι
local notation "B" => W →L[ℂ] W
local notation "M" => CStarMatrix D D B

omit [Fintype ι] in
/-- The actual right-annihilation/left-field commutator is the vacuum projection defect.
@isnad1 id=eq.0h3v.s15.c78c9594f922 from=translated src=- shape=88f94bea vocab=c93eed74
-/
theorem wordRightAnnihilation_mul_wordField_sub (i j : ι) :
    wordRightAnnihilation i*wordField j-wordField j*wordRightAnnihilation i=
      if i=j then wordVacuumProjection ι else 0 := by
  have ha : Commute (wordRightAnnihilation i) (wordAnnihilation j) := by
    simpa only [wordAnnihilation,wordRightAnnihilation,
      ← ContinuousLinearMap.star_eq_adjoint] using
      (commute_wordCreation_wordRightCreation j i).star_star.symm
  have hc : wordRightAnnihilation i*(wordCreation j).toContinuousLinearMap-
      (wordCreation j).toContinuousLinearMap*wordRightAnnihilation i=
      if i=j then wordVacuumProjection ι else 0 := by
    have h := congrArg star (wordAnnihilation_mul_wordRightCreation_sub j i)
    by_cases hij : i=j
    · simpa only [star_sub,star_mul,wordAnnihilation,wordRightAnnihilation,
        ← ContinuousLinearMap.star_eq_adjoint,star_star,ite_eq_left hij,ite_eq_left hij.symm,
        star_wordVacuumProjection] using h
    · simpa only [star_sub,star_mul,wordAnnihilation,wordRightAnnihilation,
        ← ContinuousLinearMap.star_eq_adjoint,star_star,ite_eq_right hij,ite_eq_right (Ne.symm hij),
        star_zero] using h
  calc
    _ = (wordRightAnnihilation i*(wordCreation j).toContinuousLinearMap-
      (wordCreation j).toContinuousLinearMap*wordRightAnnihilation i)+
        (wordRightAnnihilation i*wordAnnihilation j-
          wordAnnihilation j*wordRightAnnihilation i) := by
      unfold wordField
      noncomm_ring
    _ = _ := by rw [ha.eq,sub_self,add_zero,hc]

/-- Diagonal amplification of the actual right annihilator to the native operator matrix.-/
def wordMatrixRightAnnihilation (i : ι) : M :=
  CStarMatrix.ofMatrix (Matrix.diagonal (fun _ => wordRightAnnihilation i))

omit [Fintype ι] in
/-- Left multiplication by the amplified right annihilator acts entrywise.
@isnad1 id=eq.0h6v.s14.69eaafddff99 from=translated src=- shape=3c87e09c vocab=74e5c405
-/
theorem wordMatrixRightAnnihilation_mul_apply (i : ι) (t : M) (a b : D) :
    (wordMatrixRightAnnihilation (D := D) i*t) a b=wordRightAnnihilation i*t a b := by
  change (Matrix.diagonal (fun _ : D => wordRightAnnihilation i)*CStarMatrix.ofMatrix.symm t) a b=_
  rw [Matrix.diagonal_mul]
  rfl

omit [Fintype ι] in
/-- Right multiplication by the amplified right annihilator acts entrywise.
@isnad1 id=eq.0h6v.s14.caa9e7303589 from=translated src=- shape=b61978c5 vocab=74e5c405
-/
theorem mul_wordMatrixRightAnnihilation_apply (i : ι) (t : M) (a b : D) :
    (t*wordMatrixRightAnnihilation (D := D) i) a b=t a b*wordRightAnnihilation i := by
  change (CStarMatrix.ofMatrix.symm t*Matrix.diagonal (fun _ : D => wordRightAnnihilation i)) a b=_
  rw [Matrix.mul_diagonal]
  rfl

omit [Fintype D] [DecidableEq D] in
private theorem sum_entry (f : ι → M) (a b : D) :
    (∑ i, f i) a b=∑ i, f i a b := by
  have hs (s : Finset ι) : (∑ i∈s, f i) a b=∑ i∈s, f i a b := by
    induction s using Finset.induction_on with
    | empty => rfl
    | @insert i s hi ih =>
      rw [Finset.sum_insert hi,Finset.sum_insert hi,CStarMatrix.add_apply,ih]
  exact hs Finset.univ

/-- The native free model has its actual coefficientwise linear-combination entries.
@isnad1 id=eq.0h6v.s15.feaa2077ba3d from=translated src=- shape=3f79364b vocab=1d47ba08
-/
theorem wordNativeMatrixLinearCombination_apply (A₀ : Matrix D D ℂ)
    (A : ι → Matrix D D ℂ) (a b : D) :
    wordNativeMatrixLinearCombination A₀ A a b=
      A₀ a b•(1 : B)+∑ i, A i a b•wordField i := by
  unfold wordNativeMatrixLinearCombination
  rw [CStarMatrix.add_apply,sum_entry]
  rfl

/-- The amplified commutator with the actual free model is the coefficient vacuum sandwich.
@isnad1 id=eq.0h5v.s15.4a1211819ef8 from=translated src=- shape=31e61a76 vocab=140b11d5
-/
theorem wordMatrixRightAnnihilation_mul_linearCombination_sub
    (A₀ : Matrix D D ℂ) (A : ι → Matrix D D ℂ) (i : ι) :
    wordMatrixRightAnnihilation i*wordNativeMatrixLinearCombination A₀ A-
      wordNativeMatrixLinearCombination A₀ A*wordMatrixRightAnnihilation i=
      wordMatrixVacuumSandwich (ι := ι) (A i) := by
  apply CStarMatrix.ext
  intro a b
  rw [CStarMatrix.sub_apply,wordMatrixRightAnnihilation_mul_apply,
    mul_wordMatrixRightAnnihilation_apply,wordNativeMatrixLinearCombination_apply]
  change _=A i a b•wordVacuumProjection ι
  calc
    _ = ∑ j, A j a b•(wordRightAnnihilation i*wordField j-
        wordField j*wordRightAnnihilation i) := by
      simp only [mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,
        mul_smul_comm,smul_mul_assoc,mul_one,one_mul,smul_sub,Finset.sum_sub_distrib]
      abel
    _ = _ := by simp [wordRightAnnihilation_mul_wordField_sub]

/-- The actual annihilator/resolvent compression factors into two native compressed resolvents.
@isnad1 id=eq.1h6v.s17.d316b2c8e743 from=translated src=- shape=a4b851ee vocab=e592241d
-/
theorem wordMatrixVacuumCompression_rightAnnihilation_resolvent
    (A₀ : Matrix D D ℂ) (A : ι → Matrix D D ℂ) (i : ι)
    {z : ℂ} (hz : z∈resolventSet ℂ (wordNativeMatrixLinearCombination A₀ A)) :
    wordMatrixVacuumCompression
      (wordMatrixRightAnnihilation i*resolvent (wordNativeMatrixLinearCombination A₀ A) z)=
      wordMatrixVacuumCompression (resolvent (wordNativeMatrixLinearCombination A₀ A) z)*
        A i*wordMatrixVacuumCompression (resolvent (wordNativeMatrixLinearCombination A₀ A) z) := by
  have hc := congrArg (wordMatrixVacuumCompression (D := D) (ι := ι))
    (spectrum.mul_resolvent_sub_resolvent_mul (wordNativeMatrixLinearCombination A₀ A)
      (wordMatrixRightAnnihilation i) hz)
  rw [map_sub,wordMatrixRightAnnihilation_mul_linearCombination_sub,
    wordMatrixVacuumCompression_mul_sandwich_mul] at hc
  have hz0 : wordMatrixVacuumCompression
      (resolvent (wordNativeMatrixLinearCombination A₀ A) z*
        wordMatrixRightAnnihilation i)=0 := by
    ext a b
    rw [wordMatrixVacuumCompression_apply,mul_wordMatrixRightAnnihilation_apply,
      wordVacuumExpectation_mul_rightAnnihilation]
    rfl
  rwa [hz0,sub_zero] at hc

/-- The genuine model multiplication has its coefficientwise compressed identity.
@isnad1 id=eq.0h5v.s16.55639dce5df1 from=translated src=- shape=1312a565 vocab=ce392082
-/
theorem wordMatrixVacuumCompression_linearCombination_mul
    (A₀ : Matrix D D ℂ) (A : ι → Matrix D D ℂ) (t : M) :
    wordMatrixVacuumCompression (wordNativeMatrixLinearCombination A₀ A*t)=
      A₀*wordMatrixVacuumCompression t+
        ∑ i, A i*wordMatrixVacuumCompression (wordMatrixRightAnnihilation i*t) := by
  ext a b
  simp only [Matrix.add_apply,Matrix.sum_apply,Matrix.mul_apply,
    wordMatrixVacuumCompression_apply,wordMatrixRightAnnihilation_mul_apply]
  simp only [CStarMatrix.mul_apply,map_sum,
    wordNativeMatrixLinearCombination_apply,add_mul,Finset.sum_mul,map_add,
    smul_mul_assoc,one_mul,map_smul,smul_eq_mul,
    wordVacuumExpectation_wordField_mul_eq_rightAnnihilation,Finset.sum_add_distrib]
  congr 1
  exact Finset.sum_comm

/-- The actual native free resolvent compression satisfies the matrix Dyson equation. Source: arXiv:2108.06312v2, Theorem 6.2 endpoint. This is an endpoint prerequisite, not the spectral comparison.
atlas: gaussian-free-spectrum-two-sided (partial)
@isnad1 id=eq.1h5v.s16.4cc55aafe166 from=translated src=- shape=62818e34 vocab=a65d7723
-/
theorem wordMatrixVacuumCompression_resolvent_dyson
    (A₀ : Matrix D D ℂ) (A : ι → Matrix D D ℂ)
    {z : ℂ} (hz : z∈resolventSet ℂ (wordNativeMatrixLinearCombination A₀ A)) :
    (z•(1 : Matrix D D ℂ)-A₀-
      ∑ i, A i*wordMatrixVacuumCompression (resolvent (wordNativeMatrixLinearCombination A₀ A) z)*A i)*
        wordMatrixVacuumCompression (resolvent (wordNativeMatrixLinearCombination A₀ A) z)=1 := by
  have h := congrArg (wordMatrixVacuumCompression (D := D) (ι := ι))
    (Ring.mul_inverse_cancel (algebraMap ℂ M z-wordNativeMatrixLinearCombination A₀ A) hz)
  change wordMatrixVacuumCompression
    ((algebraMap ℂ M z-wordNativeMatrixLinearCombination A₀ A)*
      resolvent (wordNativeMatrixLinearCombination A₀ A) z)=_ at h
  rw [sub_mul,map_sub,Algebra.algebraMap_eq_smul_one,smul_mul_assoc,one_mul,map_smul,
    wordMatrixVacuumCompression_linearCombination_mul,wordMatrixVacuumCompression_one] at h
  simp_rw [wordMatrixVacuumCompression_rightAnnihilation_resolvent A₀ A _ hz] at h
  rw [sub_mul,sub_mul,smul_mul_assoc,one_mul,Finset.sum_mul]
  simpa only [mul_assoc,sub_sub] using h

end NLAlib
