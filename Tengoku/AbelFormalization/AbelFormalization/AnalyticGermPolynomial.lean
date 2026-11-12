import Tengoku.AbelFormalization.AbelFormalization.AnalyticGermDomain
import Tengoku.AbelFormalization.AbelFormalization.AnalyticGermDerivation
import Tengoku.Seed.Analysis.Analytic.Polynomial
import Tengoku.Seed.Algebra.MvPolynomial.Funext

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Polynomial coordinates inside the analytic-germ ring

Polynomial evaluation gives a faithful real algebra map into the actual
analytic-germ ring. Injectivity follows from the analytic identity principle
and polynomial extensionality over the infinite field of real numbers.
-/

noncomputable section

open Filter Set
open scoped Topology

namespace AbelFormalization

/-- Evaluate a polynomial at the coordinate germs.-/
def analyticGermPolynomialMap (p : ℕ) :
    MvPolynomial (Fin p) ℝ →ₐ[ℝ] RealAnalyticGerm p :=
  MvPolynomial.aeval (analyticGermCoordinate p)

/--
@isnad1 id=eq.0h2v.s12.c6ae2ee195ed from=translated src=- shape=9705d6fd vocab=7dbaefb8
-/
@[simp]
theorem analyticGermPolynomialMap_X (p : ℕ) (i : Fin p) :
    analyticGermPolynomialMap p (MvPolynomial.X i) = analyticGermCoordinate p i :=
  MvPolynomial.aeval_X _ _

/-- This algebra map is represented by ordinary polynomial evaluation.
@isnad1 id=eq.0h2v.s12.81c1d08c6690 from=translated src=- shape=1b59da3b vocab=9af9bdfd
-/
theorem analyticGermPolynomialMap_eq_of (p : ℕ) (P : MvPolynomial (Fin p) ℝ) :
    analyticGermPolynomialMap p P =
      analyticGermOf (fun x => MvPolynomial.eval x P)
        (AnalyticOnNhd.eval_mvPolynomial P 0 (mem_univ _)) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    change MvPolynomial.aeval _ (MvPolynomial.C c) = _
    rw [MvPolynomial.aeval_C, analyticGerm_algebraMap]
    apply (analyticGermOf_eq_iff _ _).mpr
    exact Eventually.of_forall fun x => (MvPolynomial.eval_C c).symm
  | add P Q hP hQ =>
    rw [map_add, hP, hQ, ← analyticGermOf_add]
    apply (analyticGermOf_eq_iff _ _).mpr
    exact Eventually.of_forall fun x => by simp
  | mul_X P i hP =>
    rw [map_mul, hP, analyticGermPolynomialMap_X]
    apply Subtype.ext
    change ((fun x : Fin p → ℝ => MvPolynomial.eval x P * x i) :
        Germ (𝓝 (0 : Fin p → ℝ)) ℝ) =
      ((fun x => MvPolynomial.eval x (P * MvPolynomial.X i)) :
        Germ (𝓝 (0 : Fin p → ℝ)) ℝ)
    apply Germ.coe_eq.mpr
    exact Eventually.of_forall fun x => by simp

/--
@isnad1 id=eq.0h2v.s13.671b05d9fbc8 from=translated src=- shape=0f6e10d1 vocab=627fb242
-/
@[simp]
theorem analyticGermValue_polynomial (p : ℕ) (P : MvPolynomial (Fin p) ℝ) :
    analyticGermValue (0 : Fin p → ℝ) (analyticGermPolynomialMap p P) =
      MvPolynomial.eval 0 P := by
  rw [analyticGermPolynomialMap_eq_of, analyticGermValue_of]

/-- No nonzero real polynomial becomes the zero analytic germ.
@isnad1 id=injectiv.0h1v.s12.61cd661560fb from=translated src=- shape=fbb01949 vocab=2baeb0ec
-/
theorem analyticGermPolynomialMap_injective (p : ℕ) :
    Function.Injective (analyticGermPolynomialMap p) := by
  intro P Q h
  rw [analyticGermPolynomialMap_eq_of, analyticGermPolynomialMap_eq_of,
    analyticGermOf_eq_iff] at h
  have he := (AnalyticOnNhd.eval_mvPolynomial P).eq_of_eventuallyEq
    (AnalyticOnNhd.eval_mvPolynomial Q) h
  exact MvPolynomial.funext (congrFun he)

end AbelFormalization
