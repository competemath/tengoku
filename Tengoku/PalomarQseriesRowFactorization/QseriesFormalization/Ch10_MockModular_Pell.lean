import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_NormTheta_Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ch10: Pell Coordinates, Cusp Vectors, Bilinear Form

The quadratic form Q(k,r) = 4k² + 6kr + r² + 2k + r factors through
Pell coordinates (x,y) = (r+3k, k) as Q_form(x,y) = x² - 5y².

## Main results

* `pellQ_pellCoord`: Q_form in Pell coordinates = the polynomial in (k,r)
* `pellQ_Mmul`: M preserves the Pell form
* Cusp norms: pellQ c₁ = -5, pellQ c₂ = -20
* `BAff_pellCoord_c1/c2`: affine bilinear pairings in (k,r)
* `pellB_Mc1_c2 = -470`: cone indecomposability
-/

namespace QseriesFormalization
namespace Ch10

/-! ## Pell coordinate vectors -/

@[ext]
structure ZVec where
  x : Int
  y : Int
  deriving DecidableEq, Repr

instance : Zero ZVec := ⟨⟨0, 0⟩⟩
instance : Neg ZVec := ⟨fun v => ⟨-v.x, -v.y⟩⟩
instance : Add ZVec := ⟨fun u v => ⟨u.x + v.x, u.y + v.y⟩⟩

/-! ## Pell quadratic form and bilinear form -/

def pellQ (v : ZVec) : Int := v.x ^ 2 - 5 * v.y ^ 2

def pellB (u v : ZVec) : Int := 2 * u.x * v.x - 10 * u.y * v.y

/-! ## Affine bilinear form (clearing denominators from μ = (1/2, 1/10)) -/

def BAff (v c : ZVec) : Int := (2 * v.x + 1) * c.x - (10 * v.y + 1) * c.y

/-! ## Coordinate change: (k,r) ↦ Pell coordinates -/

def pellCoord (k r : Int) : ZVec := ⟨r + 3 * k, k⟩

/--
@isnad1 id=eq.0h2v.s4.318204f64620 from=translated src=- shape=d6fecd78 vocab=6060868d
-/
@[simp] theorem pellCoord_x (k r : Int) : (pellCoord k r).x = r + 3 * k := rfl
/--
@isnad1 id=eq.0h2v.s3.bf6124838963 from=translated src=- shape=a92ce29b vocab=ec5455d5
-/
@[simp] theorem pellCoord_y (k r : Int) : (pellCoord k r).y = k := rfl

/-! ## Pell automorph M = ((9,20),(4,9)) -/

def Mmul (v : ZVec) : ZVec := ⟨9 * v.x + 20 * v.y, 4 * v.x + 9 * v.y⟩

/--
@isnad1 id=eq.0h1v.s5.1f0e29428850 from=translated src=- shape=7e2e68fa vocab=03e488f4
-/
@[simp] theorem Mmul_x (v : ZVec) : (Mmul v).x = 9 * v.x + 20 * v.y := rfl
/--
@isnad1 id=eq.0h1v.s5.285dc5960a99 from=translated src=- shape=26de507b vocab=03e488f4
-/
@[simp] theorem Mmul_y (v : ZVec) : (Mmul v).y = 4 * v.x + 9 * v.y := rfl

/--
@isnad1 id=eq.0h1v.s3.8a34e496e118 from=translated src=- shape=8d4cac31 vocab=49284b94
-/
@[simp] theorem pellQ_Mmul (v : ZVec) : pellQ (Mmul v) = pellQ v := by
  rcases v with ⟨x, y⟩; unfold pellQ Mmul; ring

/--
@isnad1 id=eq.0h1v.s5.38006873729c from=translated src=- shape=6af0c38a vocab=67c39244
-/
theorem Mmul_mod2_x (v : ZVec) : (Mmul v).x % 2 = v.x % 2 := by
  show (9 * v.x + 20 * v.y) % 2 = v.x % 2
  have : 9 * v.x + 20 * v.y = v.x + 2 * (4 * v.x + 10 * v.y) := by ring
  rw [this]; omega

/--
@isnad1 id=eq.0h1v.s5.2b60efb2d731 from=translated src=- shape=6af0c38a vocab=1b3043bc
-/
theorem Mmul_mod2_y (v : ZVec) : (Mmul v).y % 2 = v.y % 2 := by
  show (4 * v.x + 9 * v.y) % 2 = v.y % 2
  have : 4 * v.x + 9 * v.y = v.y + 2 * (2 * v.x + 4 * v.y) := by ring
  rw [this]; omega

/-! ## Cusp vectors -/

def c1 : ZVec := ⟨0, 1⟩
def c2 : ZVec := ⟨-5, 3⟩

/--
@isnad1 id=eq.0h0v.s3.c3100f69d68b from=translated src=- shape=f7285ee8 vocab=c6d2e735
-/
@[simp] theorem pellQ_c1 : pellQ c1 = -5 := by
  unfold pellQ c1; norm_num

/--
@isnad1 id=eq.0h0v.s3.5b0efe7fd13b from=translated src=- shape=f7285ee8 vocab=00723a21
-/
@[simp] theorem pellQ_c2 : pellQ c2 = -20 := by
  unfold pellQ c2; norm_num

/--
@isnad1 id=ne.0h0v.s2.4d0cf32cc5ee from=translated src=- shape=7bded134 vocab=139f2a5d
-/
theorem cusp_norms_ne : pellQ c1 ≠ pellQ c2 := by
  simp

/-! ## Affine bilinear pairings -/

/--
@isnad1 id=eq.0h2v.s5.a6d197c15d07 from=translated src=- shape=e3b459d8 vocab=ce8ff1c4
-/
@[simp] theorem BAff_pellCoord_c1 (k r : Int) :
    BAff (pellCoord k r) c1 = -(10 * k + 1) := by
  unfold BAff pellCoord c1; ring

/--
@isnad1 id=eq.0h2v.s5.fb383553d95c from=translated src=- shape=404780ee vocab=550a8403
-/
@[simp] theorem BAff_pellCoord_c2 (k r : Int) :
    BAff (pellCoord k r) c2 = -(10 * (6 * k + r) + 8) := by
  unfold BAff pellCoord c2; ring

/--
@isnad1 id=ne.0h2v.s4.c4fdad96c0d2 from=translated src=- shape=fbc29d95 vocab=e4782c12
-/
theorem BAff_pellCoord_c1_ne_zero (k : Int) (r : Int) :
    BAff (pellCoord k r) c1 ≠ 0 := by
  simp; omega

/--
@isnad1 id=ne.0h2v.s4.0af39f2ade7e from=translated src=- shape=fbc29d95 vocab=ba9f4e68
-/
theorem BAff_pellCoord_c2_ne_zero (k r : Int) :
    BAff (pellCoord k r) c2 ≠ 0 := by
  simp; omega

/-! ## Cone indecomposability -/

/--
@isnad1 id=eq.0h0v.s3.4f3868fea99a from=translated src=- shape=bf73f9a4 vocab=cea40316
-/
@[simp] theorem pellB_Mc1_c2 : pellB (Mmul c1) c2 = -470 := by
  unfold pellB Mmul c1 c2; norm_num

/--
@isnad1 id=lt.0h0v.s3.8004e1300ee6 from=translated src=- shape=6afa1142 vocab=e1f287f6
-/
theorem cone_indecomposable' : pellB (Mmul c1) c2 < 0 := by
  simp

/-! ## Q-invariance implies orbit separation -/

end Ch10
end QseriesFormalization
