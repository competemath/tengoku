import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_NormTheta_Defs
import Tengoku.PalomarQseriesRowFactorization.QseriesFormalization.Ch10_NormTheta_Algebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Ch10: Sigma Involution and Slab Decomposition

The sigma involution σ_k(r) = -(6k+1)-r cancels the interior of the
cone-difference sum, leaving a thin "slab" residual.

## Main results

* `sigma_preserves_Q`: Q(k, σ_k(r)) = Q(k, r)
* `sigma_flips_sign`: negOnePowInt(σ_k(r)) = -negOnePowInt(r)
* `sigma_no_fixed_point`: σ_k(r) ≠ r
* `sigma_involutive`: σ_k(σ_k(r)) = r

These are the algebraic ingredients for Theorem (slab) in the paper.
-/

namespace QseriesFormalization
namespace Ch10

/-! ## The sigma involution -/

def sigma (k r : Int) : Int := -(6 * k + 1) - r

/--
@isnad1 id=eq.0h2v.s5.9d8e8dc620a4 from=translated src=- shape=7be54c40 vocab=c6f680c8
-/
theorem sigma_eq (k r : Int) : sigma k r = -(6 * k + 1) - r := rfl

/-! ## σ preserves Q -/

/--
@isnad1 id=eq.0h2v.s3.a9d33a825717 from=translated src=- shape=f3897cf7 vocab=7f396ce4
-/
theorem sigma_preserves_Q (k r : Int) : Q k (sigma k r) = Q k r := by
  unfold Q sigma
  ring

/-! ## σ flips parity -/

/--
@isnad1 id=ne.0h2v.s5.de9b9e649eb1 from=translated src=- shape=55f8f53d vocab=96ec8c5a
-/
theorem sigma_flips_parity (k r : Int) :
    (sigma k r) % 2 ≠ r % 2 := by
  unfold sigma
  omega

/--
@isnad1 id=eq.0h2v.s3.113b1a6d627c from=translated src=- shape=e6bff783 vocab=1e398b0a
-/
theorem sigma_flips_sign (k r : Int) :
    negOnePowInt (sigma k r) = -negOnePowInt r := by
  unfold negOnePowInt sigma
  split_ifs with h1 h2 <;> omega

/-! ## σ has no fixed points -/

/--
@isnad1 id=ne.0h2v.s3.bc64b0650003 from=translated src=- shape=bf83e09e vocab=29adb852
-/
theorem sigma_no_fixed_point (k r : Int) : sigma k r ≠ r := by
  unfold sigma; omega

/-! ## σ is an involution -/

/--
@isnad1 id=eq.0h2v.s3.adf667868576 from=translated src=- shape=94dc243a vocab=29adb852
-/
theorem sigma_involutive (k r : Int) : sigma k (sigma k r) = r := by
  unfold sigma; ring

/-! ## Slab and Interior regions -/

def InSlabPlus (k r : Int) : Prop := 0 ≤ k ∧ r ≤ -(6 * k + 1)

def InSlabMinus (k r : Int) : Prop := k ≤ -1 ∧ -6 * k ≤ r

def InSlab (k r : Int) : Prop := InSlabPlus k r ∨ InSlabMinus k r

def InHalfB (k r : Int) : Prop :=
  (0 ≤ k ∧ r ≤ -1) ∨ (k ≤ -1 ∧ 0 ≤ r)

def InInterior (k r : Int) : Prop :=
  InHalfB k r ∧ ¬ InSlab k r

instance (k r : Int) : Decidable (InSlabPlus k r) :=
  show Decidable (0 ≤ k ∧ r ≤ -(6 * k + 1)) from inferInstance

instance (k r : Int) : Decidable (InSlabMinus k r) :=
  show Decidable (k ≤ -1 ∧ -6 * k ≤ r) from inferInstance

instance (k r : Int) : Decidable (InSlab k r) :=
  show Decidable (InSlabPlus k r ∨ InSlabMinus k r) from inferInstance

instance (k r : Int) : Decidable (InHalfB k r) :=
  show Decidable ((0 ≤ k ∧ r ≤ -1) ∨ (k ≤ -1 ∧ 0 ≤ r)) from inferInstance

instance (k r : Int) : Decidable (InInterior k r) :=
  show Decidable (InHalfB k r ∧ ¬ InSlab k r) from inferInstance

/-! ## σ maps Interior to Interior -/

/--
@isnad1 id=and.3h2v.s6.57b09df14bea from=translated src=- shape=9a1604c3 vocab=8b7cec64
-/
theorem sigma_maps_interior_nonneg (k r : Int) (_hk : 0 ≤ k)
    (hr_lo : -(6 * k) ≤ r) (hr_hi : r ≤ -1) :
    -(6 * k) ≤ sigma k r ∧ sigma k r ≤ -1 := by
  constructor <;> (unfold sigma; omega)

/--
@isnad1 id=and.3h2v.s6.65086b14a371 from=translated src=- shape=6892f3c8 vocab=5c2620ec
-/
theorem sigma_maps_interior_neg (k r : Int) (_hk : k ≤ -1)
    (hr_lo : 0 ≤ r) (hr_hi : r ≤ -6 * k - 1) :
    0 ≤ sigma k r ∧ sigma k r ≤ -6 * k - 1 := by
  constructor <;> (unfold sigma; omega)

/-! ## Pell coordinates -/

def pellX (k r : Int) : Int := r + 3 * k
def pellY (k _r : Int) : Int := k

def Q_form (x y : Int) : Int := x ^ 2 - 5 * y ^ 2

/-! ## Pell automorph (in Pell coordinates) -/

def pellAutomorphX (x y : Int) : Int := 9 * x + 20 * y
def pellAutomorphY (x y : Int) : Int := 4 * x + 9 * y

/--
@isnad1 id=eq.0h2v.s5.bdf48356ade9 from=translated src=- shape=bf52afae vocab=51b28252
-/
theorem pell_automorph_mod2_x (x y : Int) :
    (pellAutomorphX x y) % 2 = x % 2 := by
  unfold pellAutomorphX; omega

/--
@isnad1 id=eq.0h2v.s5.d2a63cb54483 from=translated src=- shape=55f8f53d vocab=df3aa4d4
-/
theorem pell_automorph_mod2_y (x y : Int) :
    (pellAutomorphY x y) % 2 = y % 2 := by
  unfold pellAutomorphY; omega

/-! ## Cusp vectors and their norms -/

def c1_x : Int := 0
def c1_y : Int := 1
def c2_x : Int := -5
def c2_y : Int := 3

/-! ## Bilinear form B(u,v) = 2(u₁v₁ - 5u₂v₂) -/

def bilinearB (u1 u2 v1 v2 : Int) : Int :=
  2 * (u1 * v1 - 5 * u2 * v2)

/-! ## Mc₁ is outside the slab cone (cone indecomposability) -/

def Mc1_x : Int := pellAutomorphX c1_x c1_y  -- = 20
def Mc1_y : Int := pellAutomorphY c1_x c1_y  -- = 9

/--
@isnad1 id=eq.0h0v.s4.a4ba1afe5837 from=translated src=- shape=4f0c63c3 vocab=a3c07e25
-/
theorem Mc1_val : (Mc1_x, Mc1_y) = (20, 9) := by
  unfold Mc1_x Mc1_y pellAutomorphX pellAutomorphY c1_x c1_y
  norm_num

/--
@isnad1 id=eq.0h0v.s3.0e92b6f8faa2 from=translated src=- shape=f06cb865 vocab=8811a05d
-/
theorem Mc1_bilinear_c2 : bilinearB Mc1_x Mc1_y c2_x c2_y = -470 := by
  unfold bilinearB Mc1_x Mc1_y pellAutomorphX pellAutomorphY c1_x c1_y c2_x c2_y
  norm_num

/--
@isnad1 id=lt.0h0v.s3.7cdf910f79a5 from=translated src=- shape=39fda607 vocab=10d91080
-/
theorem cone_indecomposable : bilinearB Mc1_x Mc1_y c2_x c2_y < 0 := by
  rw [Mc1_bilinear_c2]; norm_num

end Ch10
end QseriesFormalization
