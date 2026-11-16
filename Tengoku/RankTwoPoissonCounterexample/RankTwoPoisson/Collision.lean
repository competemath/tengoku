import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.Poisson

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit collision and nonautomorphism

Rather than formalizing the prime-ideal argument first, this file uses the
manuscript's explicit collision.  An algebra equivalence of a polynomial ring
induces an injective map on rational points, so the collision rules out an
algebra automorphism.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RankTwoPoisson

noncomputable section

open MvPolynomial

/-- First rational point in the displayed four-dimensional fiber.-/
def point0 : Var → ℚ := ![0, 0, 1 / 24, -1 / 8]

/-- Second rational point in the displayed four-dimensional fiber.-/
def point1 : Var → ℚ := ![1, 2 / 3, 247 / 96, -89 / 64]

/-- Third rational point in the displayed four-dimensional fiber.-/
def point2 : Var → ℚ := ![-1, -2 / 3, 247 / 96, -89 / 64]

/-- Their common image under `(R,T,D,S)`.-/
def target : Var → ℚ := ![0, 1 / 8, 0, 0]

/-- The first point maps to the common target.
@isnad1 id=eq.0h0v.s3.7696da4f5f54 from=translated src=- shape=40c40af5 vocab=6f5b4595
-/
theorem point0_image : pointMap Phi point0 = target := by
  funext i
  fin_cases i <;>
    simp [pointMap, Phi, output, point0, target,
      R, T, D, S, D0, H, u, y, beta, B, a, rat, x, q, p, z] <;>
    norm_num

/-- The second point maps to the common target.
@isnad1 id=eq.0h0v.s3.7737a1dda9d7 from=translated src=- shape=40c40af5 vocab=ee08cfa2
-/
theorem point1_image : pointMap Phi point1 = target := by
  funext i
  fin_cases i <;>
    simp [pointMap, Phi, output, point1, target,
      R, T, D, S, D0, H, u, y, beta, B, a, rat, x, q, p, z] <;>
    norm_num

/-- The third point maps to the common target.
@isnad1 id=eq.0h0v.s3.22621d101695 from=translated src=- shape=40c40af5 vocab=1d318f29
-/
theorem point2_image : pointMap Phi point2 = target := by
  funext i
  fin_cases i <;>
    simp [pointMap, Phi, output, point2, target,
      R, T, D, S, D0, H, u, y, beta, B, a, rat, x, q, p, z] <;>
    norm_num

/-- The first two source points are distinct.
@isnad1 id=ne.0h0v.s2.750a68e49cab from=translated src=- shape=db2d4fff vocab=0f18d982
-/
theorem point0_ne_point1 : point0 ≠ point1 := by
  intro h
  have h0 := congrFun h 0
  simpa [point0, point1] using h0

/--
A polynomial algebra equivalence induces an injective map on rational points.
The proof compares the two evaluation homomorphisms after composition with the
equivalence and then evaluates the resulting equality on `e.symm (X i)`.
@isnad1 id=injectiv.0h1v.s7.1d622a818dce from=translated src=- shape=eeb83906 vocab=300bfd01
-/
theorem pointMap_of_equiv_injective (e : P ≃ₐ[ℚ] P) :
    Function.Injective (pointMap e.toAlgHom) := by
  intro v w h
  funext i
  have hcomp :
      (MvPolynomial.aeval v).comp e.toAlgHom =
      (MvPolynomial.aeval w).comp e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa [pointMap] using congrFun h j
  have hi := congrArg
    (fun φ : P →ₐ[ℚ] ℚ => φ (e.symm (X i))) hcomp
  simpa using hi

/-- The explicit substitution endomorphism is not induced by an algebra equivalence.
@isnad1 id=not.0h0v.s1.2270404fcf68 from=translated src=- shape=87ceb31f vocab=877df097
-/
theorem Phi_not_automorphism : ¬ IsAlgAutomorphism Phi := by
  rintro ⟨e, he⟩
  have hcollision : pointMap Phi point0 = pointMap Phi point1 :=
    point0_image.trans point1_image.symm
  have hcollision' :
      pointMap e.toAlgHom point0 = pointMap e.toAlgHom point1 := by
    simpa [he] using hcollision
  have hp : point0 = point1 := pointMap_of_equiv_injective e hcollision'
  exact point0_ne_point1 hp

/-- The formalized algebraic counterexample.
@isnad1 id=and.0h0v.s2.d94673e679ec from=translated src=- shape=c12ba993 vocab=a4dc25a7
-/
theorem explicit_counterexample :
    IsPoisson Phi ∧ ¬ IsAlgAutomorphism Phi :=
  ⟨Phi_isPoisson, Phi_not_automorphism⟩

end
end RankTwoPoisson
