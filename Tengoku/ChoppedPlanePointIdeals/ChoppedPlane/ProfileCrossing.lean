module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.QWeylGrading
public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.LinearMatrix

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Exact coefficient degrees at the two critical twists of the cubic
excess-three witnesses. -/
noncomputable section
namespace ChoppedPlane.QWeyl
open Module
variable {K : Type*} [Field K]

/-- The dimension of the degree-r piece of a profile.-/
def profileRows (s : CubicProfile) (r : ℕ) : ℕ := 3*r+3-profileIndex s

/-- The auxiliary degree of the differential dual to the lower critical
matrix twist.-/
def profileCriticalDegree (s : CubicProfile) (r : ℕ) : ℕ := 2*profileRows s r/3

/--
@isnad1 id=lt.0h2v.s3.46f2bc28be6e from=translated src=- shape=787c1379 vocab=8eafb9b0
-/
theorem profileRows_pos (s : CubicProfile) (r : ℕ) : 0 < profileRows s r := by
  cases s <;> simp only [profileRows, profileIndex] <;> omega

/--
@isnad1 id=eq.0h2v.s5.6b2afb638bc7 from=translated src=- shape=d4057deb vocab=4e657102
-/
theorem profileRows_succ (s : CubicProfile) (r : ℕ) :
    profileRows s (r+1) = profileRows s r+3 := by
  cases s <;> simp only [profileRows, profileIndex] <;> omega

/--
@isnad1 id=eq.0h3v.s9.f4304cc2ec46 from=translated src=- shape=ef6da212 vocab=1e24bb5d
-/
theorem finrank_gradedProfile_eq_rows (s : CubicProfile) (r : ℕ) :
    finrank K (GradedBinaryVector (K := K) (generatorWeights s) (r : ℤ)) =
      profileRows s r := finrank_gradedProfile_nat s r

/-- All positive row counts are represented, including the two small cases.
@isnad1 id=ex.1h1v.s4.3262a2a6bb6f from=translated src=- shape=c77d6296 vocab=8eafb9b0
-/
theorem exists_profileRows (a : ℕ) (ha : 0 < a) :
    ∃ s : CubicProfile, ∃ r : ℕ, profileRows s r = a := by
  by_cases h0 : a%3 = 0
  · refine ⟨.degreeThree, a/3-1, ?_⟩
    simp only [profileRows, profileIndex]
    omega
  · by_cases h1 : a%3 = 1
    · refine ⟨.degreeOne, a/3, ?_⟩
      simp only [profileRows, profileIndex]
      omega
    · refine ⟨.degreeTwo, a/3, ?_⟩
      simp only [profileRows, profileIndex]
      omega

/-- The original quartic pullback lies strictly below every symmetric-kernel
generator at the upper critical differential degree.
@isnad1 id=lt.0h3v.s6.3292ca721491 from=translated src=- shape=0054e2aa vocab=5164b704
-/
theorem profile_right_degree_bound (s : CubicProfile) (r : ℕ) (i : Fin 3) :
    4*(r : ℤ)+(3-(profileIndex s : ℤ)) <
      2*((profileCriticalDegree s r : ℤ)+1)+(generatorWeights s i : ℤ) := by
  cases s <;> fin_cases i <;>
    norm_num [profileCriticalDegree, profileRows, profileIndex, generatorWeights] <;> omega

/-- The lower critical transpose uses the actual dual module in total degree
n-r. Its quartic pullback is below every degree-2n kernel generator.
@isnad1 id=lt.0h3v.s6.1b6ecfa58eb2 from=translated src=- shape=e9c9650a vocab=f7d2e483
-/
theorem profile_left_dual_degree_bound (s : CubicProfile) (r : ℕ) (i : Fin 3) :
    4*((profileCriticalDegree s r : ℤ)-(r : ℤ))-(3-(profileIndex s : ℤ)) <
      2*(profileCriticalDegree s r : ℤ)+(dualGeneratorWeights s i : ℤ) := by
  cases s <;> fin_cases i <;>
    norm_num [profileCriticalDegree, profileRows, profileIndex, dualGeneratorWeights, generatorWeights] <;> omega

/-- The divisible-by-three case is square at the lower critical twist and
can use the original module's injectivity directly.
@isnad1 id=lt.0h2v.s6.dd1420a67f1a from=translated src=- shape=6808288c vocab=d7624582
-/
theorem profile_square_degree_bound (r : ℕ) (i : Fin 3) :
    4*(r : ℤ)+3 < 2*(profileCriticalDegree .degreeThree r : ℤ)+
      (generatorWeights .degreeThree i : ℤ) := by
  fin_cases i <;>
    norm_num [profileCriticalDegree, profileRows, profileIndex, generatorWeights] <;> omega

end ChoppedPlane.QWeyl
