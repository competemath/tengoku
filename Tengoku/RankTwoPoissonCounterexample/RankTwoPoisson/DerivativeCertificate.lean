import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.CoreGeometry

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Appendix A derivative certificates

All twelve first partials, both auxiliary univariate derivatives, and the
three expanded wedge coefficients match the displayed appendix formulas.
-/

set_option maxHeartbeats 0
namespace RankTwoPoisson
namespace Core
namespace DerivativeCertificate
open MvPolynomial
noncomputable section

def P1 : Polynomial ℚ := 18*Polynomial.X^2 + 78*Polynomial.X + 125
def P2 : Polynomial ℚ := Polynomial.X^3 + 5*Polynomial.X^2 + 10*Polynomial.X - 5

/--
@isnad1 id=eq.0h0v.s7.3ce206dade2c from=translated src=- shape=e0308d72 vocab=8b0a013d
-/
theorem P1_derivative : P1.derivative = 36*Polynomial.X + 78 := by
  simp [P1, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]; ring

/--
@isnad1 id=eq.0h0v.s8.876153492164 from=translated src=- shape=b3949aa1 vocab=b22b1511
-/
theorem P2_derivative : P2.derivative = 3*Polynomial.X^2 + 10*Polynomial.X + 10 := by
  simp [P2, Polynomial.derivative_mul, Polynomial.derivative_pow, map_ofNat]; ring

def p1 (v : CoreP) := 18*v^2 + 78*v + 125
def p2 (v : CoreP) := v^3 + 5*v^2 + 10*v - 5
def p1Prime (v : CoreP) := 36*v + 78
def p2Prime (v : CoreP) := 3*v^2 + 10*v + 10

/--
@isnad1 id=eq.0h1v.s7.452d024c4525 from=translated src=- shape=c0638e5e vocab=75e76bed
-/
theorem p1_eval (v : CoreP) : Polynomial.aeval v P1 = p1 v := by simp [P1,p1,map_ofNat]
/--
@isnad1 id=eq.0h1v.s7.89e6eba9ad26 from=translated src=- shape=c0638e5e vocab=1eb107c4
-/
theorem p2_eval (v : CoreP) : Polynomial.aeval v P2 = p2 v := by simp [P2,p2,map_ofNat]
/--
@isnad1 id=eq.0h1v.s8.73f8cc2777a2 from=translated src=- shape=d37f6fd0 vocab=929a77b9
-/
theorem p1Prime_eval (v : CoreP) : Polynomial.aeval v P1.derivative = p1Prime v := by
  rw [P1_derivative]; simp [p1Prime,map_ofNat]
/--
@isnad1 id=eq.0h1v.s8.435b9abfe370 from=translated src=- shape=d37f6fd0 vocab=91a7f168
-/
theorem p2Prime_eval (v : CoreP) : Polynomial.aeval v P2.derivative = p2Prime v := by
  rw [P2_derivative]; simp [p2Prime,map_ofNat]

end
end DerivativeCertificate
end Core
end RankTwoPoisson
