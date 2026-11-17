import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.SourceEquivalence
import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.CoreGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The source-coordinate symplectic form

Formal one-forms and two-forms are represented by their complete coefficient
arrays in the independent coordinate order (X,Y,W,E₀).
-/

set_option maxHeartbeats 0
namespace RankTwoPoisson
namespace SourceCoordinates
namespace Forms
open MvPolynomial
noncomputable section

@[simp] private theorem pderiv_numeral (i : Var) (n : ℕ) [n.AtLeastTwo] :
    pderiv i (ofNat(n) : P) = 0 := (pderiv i).map_natCast n

/-- Alternating coefficient of a wedge of two exact polynomial one-forms.-/
def wedge (f g : P) (i j : Var) := pderiv i f * pderiv j g - pderiv j f * pderiv i g

/-- Residual two-form on (X,Y,W,E₀), with zero fourth row and column.-/
def theta : Matrix Var Var P :=
  !![0,coreLift Core.A1,coreLift Core.A2,0;
     -coreLift Core.A1,0,coreLift Core.A3,0;
     -coreLift Core.A2,-coreLift Core.A3,0,0;
     0,0,0,0]

variable (K : Type*) [Field K] [CharZero K]

def wedgeK (f g : MvPolynomial Var K) (i j : Var) :=
  pderiv i f * pderiv j g - pderiv j f * pderiv i g

/--
@isnad1 id=eq.0h5v.s8.0077e4e511fe from=translated src=- shape=901c808e vocab=6f5c0df0
-/
theorem wedge_map (f g : P) (i j : Var) :
    wedgeK K (mapK K f) (mapK K g) i j = mapK K (wedge f g i j) := by
  simp only [wedgeK,wedge,mapK,pderiv_map,map_sub,map_mul]

end
end Forms
end SourceCoordinates
end RankTwoPoisson
