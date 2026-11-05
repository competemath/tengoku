module

public import Tengoku.ChoppedPlanePointIdeals.ChoppedPlane.Homogeneous
public import Tengoku.Seed.Algebra.MvPolynomial.Division

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

@[expose] public section

/-! Homogeneous division by a coordinate variable. -/

namespace ChoppedPlane

open MvPolynomial

variable {K : Type*} [Field K]

/-- Removing one `x` factor lowers the homogeneous degree by one. Terms
without an `x` factor are discarded by `divMonomial`.
@isnad1 id=ishomoge.1h3v.s6.14e5cfbab117 from=translated src=- shape=a518a795 vocab=1df45f93
-/
theorem homogeneous_div_x {t : ℕ} (p : Poly K 3)
    (hp : p.IsHomogeneous (t + 1)) :
    (p.divMonomial (Finsupp.single 0 1)).IsHomogeneous t := by
  intro e he
  have hcoeff : p.coeff (Finsupp.single 0 1 + e) ≠ 0 := by
    simpa only [coeff_divMonomial] using he
  have hdeg : (Finsupp.single 0 1 + e).degree = t + 1 := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp hcoeff
  have hedeg : e.degree = t := by
    simp only [map_add, Finsupp.degree_single] at hdeg
    omega
  simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hedeg

/-- The quotient by `x` reconstructs a polynomial when `x` divides it.
@isnad1 id=eq.1h2v.s8.f476baf71c7c from=translated src=- shape=42461669 vocab=575f9fd6
-/
theorem x_mul_div_of_x_dvd (p : Poly K 3) (hdiv : X 0 ∣ p) :
    X 0 * p.divMonomial (Finsupp.single 0 1) = p := by
  have hmod := (X_dvd_iff_modMonomial_eq_zero).mp hdiv
  simpa only [hmod, add_zero] using p.divMonomial_add_modMonomial_single 0

end ChoppedPlane
