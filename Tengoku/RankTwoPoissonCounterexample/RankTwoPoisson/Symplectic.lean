import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.ExactFiber

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The four - dimensional symplectic criterion and Jacobian

Source columns are ordered (x,q,p,z), output rows (R,T,D,S). The matrix omega
represents dx∧dp+dq∧dz, while its inverse -omega represents the bracket.
All coefficient equalities are identities of multivariate polynomials.
The determinant formula is proved directly over any commutative coefficient
ring; it yields +1, without passing through a determinant-squared equation.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RankTwoPoisson
namespace Symplectic
open Matrix
variable {A : Type*} [CommRing A]

/-- The alternating matrix for dx∧dp+dq∧dz in order (x,q,p,z).-/
def omega : Matrix (Fin 4) (Fin 4) A :=
  !![0, 0, 1, 0; 0, 0, 0, 1; -1, 0, 0, 0; 0,-1, 0, 0]

/-- Contraction of two row vectors with the canonical bracket matrix -omega.-/
def pair (u v : Fin 4 → A) : A := u 2 * v 0 - u 0 * v 2 + u 3 * v 1 - u 1 * v 3

section Polynomials
variable (K : Type*) [Field K] [CharZero K]

/-- Rows are outputs; columns are source coordinates (x,q,p,z).-/
noncomputable def jacobian (F : Var → MvPolynomial Var K) : Matrix Var Var (MvPolynomial Var K) :=
  fun i j => MvPolynomial.pderiv j (F i)

omit [CharZero K] in
@[simp] theorem bracket_selfK (f : MvPolynomial Var K) : bracketK K f f = 0 := by
  dsimp [bracketK]
  ring

end Polynomials

end Symplectic
end RankTwoPoisson
