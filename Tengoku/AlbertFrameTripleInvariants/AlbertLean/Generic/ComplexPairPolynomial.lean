import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms reconstructed_determinant_numerator` (it only prints; the queue checks the axioms of every declaration). -/

/-! The denominator-cleared scalar identity for the dephased complex pair.
No matrix reconstruction or generic-coverage statement is asserted here. -/

namespace AlbertLean.Generic.ComplexPairPolynomial

variable {K : Type*} [CommRing K]

def nu (p q r s z : K) : K :=
  (1 - p - q - r) * z + (p + q + r + s - 1)

def pairQuadratic (p q r s z : K) : K :=
  (1 - p - q) * (1 - p - r) * z ^ 2 +
    (p * (1 - p - q - r) + (1 - p) * (p + q + r + s - 1) - q * r) * z +
    p * (p + q + r + s - 1)

/-- If n=nu(d), A=s*d, B=d*n+q*d*(d-1), C=d*n+r*d*(d-1),
then the left side is n² times det(X_reconstructed)-d*(d-1)/n
whenever division by n is legal. This theorem itself uses no division.-/
theorem reconstructed_determinant_numerator (p q r s d : K) :
    (s * d - nu p q r s d) * (d - 1) * nu p q r s d -
      (d * nu p q r s d + q * d * (d - 1) - nu p q r s d) *
        (d * nu p q r s d + r * d * (d - 1) - nu p q r s d) -
      d * (d - 1) * nu p q r s d =
        -(d * (d - 1)) * pairQuadratic p q r s d := by
  unfold nu pairQuadratic
  ring

end AlbertLean.Generic.ComplexPairPolynomial
