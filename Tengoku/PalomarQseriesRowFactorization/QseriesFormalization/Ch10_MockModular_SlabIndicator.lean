import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_MockModular_Pell
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_MockModular_Sigma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ch10: Slab Indicator = Zwegers Cone Sign Difference

The slab indicator function equals ½(sgn B(v,c₁) − sgn B(v,c₂)),
stated in integer form: 2 · slabInd(k,r) = sgnZ(BAff(v,c₁)) − sgnZ(BAff(v,c₂)).

## Main result

* `two_mul_slabInd_eq_sign_diff`: the doubled identity over ℤ
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Custom integer sign function -/

def sgnZ (n : Int) : Int := if 0 < n then 1 else -1

/--
@isnad1 id=eq.1h1v.s4.c9917c324a62 from=translated src=- shape=97c35add vocab=9d823021
-/
@[simp] theorem sgnZ_pos {n : Int} (h : 0 < n) : sgnZ n = 1 := by
  simp [sgnZ, h]

/--
@isnad1 id=eq.1h1v.s4.7c64fbba4057 from=translated src=- shape=539d01fc vocab=902257b7
-/
@[simp] theorem sgnZ_neg {n : Int} (h : n < 0) : sgnZ n = -1 := by
  have : ¬ (0 < n) := by omega
  simp [sgnZ, this]

/--
@isnad1 id=eq.2h1v.s5.a92912237d2e from=translated src=- shape=35383a47 vocab=1c56581c
-/
@[simp] theorem sgnZ_neg' {n : Int} (h : n ≤ 0) (h2 : n ≠ 0) : sgnZ n = -1 := by
  have : n < 0 := by omega
  exact sgnZ_neg this

/-! ## Slab indicator (integer-valued, ±1 or 0) -/

def slabInd (k r : Int) : Int :=
  if 0 ≤ k ∧ r ≤ -(6 * k + 1) then -1
  else if k ≤ -1 ∧ -6 * k ≤ r then 1
  else 0

/-! ## The doubled cone-indicator identity -/

/--
@isnad1 id=eq.0h2v.s5.f54226e255aa from=translated src=- shape=6d99f70e vocab=bb46c3bf
-/
theorem two_mul_slabInd_eq_sign_diff (k r : Int) :
    2 * slabInd k r =
      sgnZ (BAff (pellCoord k r) c1) -
      sgnZ (BAff (pellCoord k r) c2) := by
  simp only [BAff_pellCoord_c1, BAff_pellCoord_c2]
  unfold slabInd sgnZ
  split_ifs <;> omega

end Ch10
end QseriesFormalization
