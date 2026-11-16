import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.Collision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complex rank-two Poisson counterexample

The explicit polynomials have rational coefficients.  This file extends them
coefficientwise from `ℚ` to `ℂ`, proves that formal differentiation and the
canonical Poisson bracket commute with that extension, and derives the standard
complex form of the counterexample.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RankTwoPoisson

noncomputable section

open MvPolynomial

/-- The complex polynomial algebra `ℂ[x,q,p,z]`.-/
abbrev PC := MvPolynomial Var ℂ

/-- Coefficientwise extension from rational to complex polynomials.-/
def mapC : P →+* PC := MvPolynomial.map (algebraMap ℚ ℂ)

/-- Formal polynomial differentiation over `ℂ`.-/
def polyDerivC (i : Var) (f : PC) : PC := MvPolynomial.pderiv i f

/-- The canonical Poisson bracket on `ℂ[x,q,p,z]`.-/
def bracketC (f g : PC) : PC :=
    polyDerivC 2 f * polyDerivC 0 g - polyDerivC 0 f * polyDerivC 2 g
  + polyDerivC 3 f * polyDerivC 1 g - polyDerivC 1 f * polyDerivC 3 g

/-- The rational output tuple after coefficient extension to `ℂ`.-/
def outputC (i : Var) : PC := mapC (output i)

/-- The complex substitution endomorphism.-/
def PhiC : PC →ₐ[ℂ] PC := MvPolynomial.aeval outputC

/-- Preservation of the complex canonical Poisson bracket.-/
def IsPoissonC (φ : PC →ₐ[ℂ] PC) : Prop :=
  ∀ f g : PC, bracketC (φ f) (φ g) = φ (bracketC f g)

/-- Being induced by a complex algebra equivalence.-/
def IsAlgAutomorphismC (φ : PC →ₐ[ℂ] PC) : Prop :=
  ∃ e : PC ≃ₐ[ℂ] PC, e.toAlgHom = φ

/-- The complex point map associated with a polynomial algebra endomorphism.-/
def pointMapC (φ : PC →ₐ[ℂ] PC) (v : Var → ℂ) : Var → ℂ :=
  fun i => MvPolynomial.aeval v (φ (X i))

/-- Formal differentiation commutes with coefficient extension.-/
theorem polyDeriv_mapC (i : Var) (f : P) :
    polyDerivC i (mapC f) = mapC (polyDeriv i f) := by
  simp [polyDerivC, polyDeriv, mapC, MvPolynomial.pderiv_map]

/-- The canonical bracket commutes with coefficient extension.-/
theorem bracket_mapC (f g : P) :
    bracketC (mapC f) (mapC g) = mapC (bracket f g) := by
  simp only [bracketC, bracket, polyDeriv_mapC, map_sub, map_add, map_mul]

/-- Additivity in the first complex argument.-/
theorem bracketC_add_left (f g k : PC) :
    bracketC (f + g) k = bracketC f k + bracketC g k := by
  simp [bracketC, polyDerivC] ; ring

/-- Additivity in the second complex argument.-/
theorem bracketC_add_right (f g k : PC) :
    bracketC f (g + k) = bracketC f g + bracketC f k := by
  simp [bracketC, polyDerivC] ; ring

/-- Leibniz rule in the first complex argument.-/
theorem bracketC_mul_left (f g k : PC) :
    bracketC (f * g) k = f * bracketC g k + g * bracketC f k := by
  simp [bracketC, polyDerivC] ; ring

/-- Leibniz rule in the second complex argument.-/
theorem bracketC_mul_right (f g k : PC) :
    bracketC f (g * k) = g * bracketC f k + k * bracketC f g := by
  simp [bracketC, polyDerivC] ; ring

@[simp] theorem bracketC_C_left (c : ℂ) (f : PC) : bracketC (C c) f = 0 := by
  simp [bracketC, polyDerivC]

@[simp] theorem bracketC_C_right (f : PC) (c : ℂ) : bracketC f (C c) = 0 := by
  simp [bracketC, polyDerivC]

/-- The canonical bracket matrix after embedding its entries in `ℂ`.-/
def canonicalMatrixC (i j : Var) : ℂ := algebraMap ℚ ℂ (canonicalMatrix i j)

/-- The complex source generators have the canonical bracket matrix.-/
theorem bracketC_X_X (i j : Var) :
    bracketC (X i) (X j) = C (canonicalMatrixC i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [bracketC, polyDerivC, canonicalMatrixC, canonicalMatrix]

/-- The complex output generators have the same canonical bracket matrix.-/
theorem bracketC_outputC_outputC (i j : Var) :
    bracketC (outputC i) (outputC j) = C (canonicalMatrixC i j) := by
  calc
    bracketC (outputC i) (outputC j)
        = mapC (bracket (output i) (output j)) := by
            simp [outputC, bracket_mapC]
    _ = mapC (C (canonicalMatrix i j)) := by
          exact congrArg mapC (bracket_output_output i j)
    _ = C (canonicalMatrixC i j) := by
          simp [mapC, canonicalMatrixC]

@[simp] theorem PhiC_X (i : Var) : PhiC (X i) = outputC i := by
  simp [PhiC]

/-- Preservation of brackets on the four complex polynomial generators.-/
theorem PhiC_generator_bracket (i j : Var) :
    bracketC (PhiC (X i)) (PhiC (X j)) = PhiC (bracketC (X i) (X j)) := by
  rw [PhiC_X, PhiC_X, bracketC_outputC_outputC, bracketC_X_X]
  simp [PhiC]

/-- Preservation against a generator, promoted to every complex polynomial.-/
lemma PhiC_preserves_right_generator (i : Var) (f : PC) :
    bracketC (PhiC f) (PhiC (X i)) = PhiC (bracketC f (X i)) := by
  refine MvPolynomial.induction_on
    (motive := fun h : PC =>
      bracketC (PhiC h) (PhiC (X i)) = PhiC (bracketC h (X i)))
    f ?_ ?_ ?_
  · intro c
    simp
  · intro f g hf hg
    simp only [map_add, bracketC_add_left]
    exact congrArg₂ (· + ·) hf hg
  · intro f j hf
    simp only [map_mul, map_add, bracketC_mul_left]
    rw [PhiC_generator_bracket, hf]

/-- The complex substitution preserves the bracket on all polynomials.-/
theorem PhiC_isPoisson : IsPoissonC PhiC := by
  intro f g
  refine MvPolynomial.induction_on
    (motive := fun h : PC =>
      bracketC (PhiC f) (PhiC h) = PhiC (bracketC f h))
    g ?_ ?_ ?_
  · intro c
    simp
  · intro g k hg hk
    simp only [map_add, bracketC_add_right]
    exact congrArg₂ (· + ·) hg hk
  · intro g j hg
    simp only [map_mul, map_add, bracketC_mul_right]
    rw [PhiC_preserves_right_generator, hg]

/-- Embed a rational point coefficientwise into complex affine space.-/
def complexPoint (v : Var → ℚ) : Var → ℂ :=
  fun i => algebraMap ℚ ℂ (v i)

/-- Evaluation of a coefficient-extended polynomial at an embedded rational point.-/
theorem aeval_mapC_complexPoint (v : Var → ℚ) (f : P) :
    MvPolynomial.aeval (complexPoint v) (mapC f)
      = algebraMap ℚ ℂ (MvPolynomial.aeval v f) := by
  have hpoint : complexPoint v = (algebraMap ℚ ℂ) ∘ v := by
    funext i
    rfl
  rw [hpoint]
  simpa only [mapC, MvPolynomial.aeval_eq_eval] using
    (MvPolynomial.map_eval (algebraMap ℚ ℂ) v f).symm

/-- The complex point map on embedded rational points is the embedded rational point map.-/
theorem pointMapC_PhiC_complexPoint (v : Var → ℚ) :
    pointMapC PhiC (complexPoint v) = complexPoint (pointMap Phi v) := by
  funext i
  simp [pointMapC, PhiC, outputC, pointMap, Phi,
    complexPoint, aeval_mapC_complexPoint]

/-- The two rational collision points viewed as complex points.-/
def point0C : Var → ℂ := complexPoint point0
def point1C : Var → ℂ := complexPoint point1

/-- Their common complex target.-/
def targetC : Var → ℂ := complexPoint target

/-- The first complex point maps to the common target.-/
theorem point0C_image : pointMapC PhiC point0C = targetC := by
  rw [point0C, targetC, pointMapC_PhiC_complexPoint, point0_image]

/-- The second complex point maps to the common target.-/
theorem point1C_image : pointMapC PhiC point1C = targetC := by
  rw [point1C, targetC, pointMapC_PhiC_complexPoint, point1_image]

/-- The two complex source points remain distinct.-/
theorem point0C_ne_point1C : point0C ≠ point1C := by
  intro h
  have h0 := congrFun h 0
  norm_num [point0C, point1C, complexPoint, point0, point1] at h0

/-- A complex polynomial algebra equivalence induces an injective map on complex points.-/
theorem pointMapC_of_equiv_injective (e : PC ≃ₐ[ℂ] PC) :
    Function.Injective (pointMapC e.toAlgHom) := by
  intro v w h
  funext i
  have hcomp :
      (MvPolynomial.aeval v).comp e.toAlgHom =
      (MvPolynomial.aeval w).comp e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa [pointMapC] using congrFun h j
  have hi := congrArg
    (fun φ : PC →ₐ[ℂ] ℂ => φ (e.symm (X i))) hcomp
  simpa using hi

/-- The complex substitution is not induced by a complex algebra equivalence.-/
theorem PhiC_not_automorphism : ¬ IsAlgAutomorphismC PhiC := by
  rintro ⟨e, he⟩
  have hcollision : pointMapC PhiC point0C = pointMapC PhiC point1C :=
    point0C_image.trans point1C_image.symm
  have hcollision' :
      pointMapC e.toAlgHom point0C = pointMapC e.toAlgHom point1C := by
    simpa [he] using hcollision
  have hp : point0C = point1C := pointMapC_of_equiv_injective e hcollision'
  exact point0C_ne_point1C hp

/-- The standard complex rank-two Poisson counterexample.-/
theorem explicit_counterexample_complex :
    IsPoissonC PhiC ∧ ¬ IsAlgAutomorphismC PhiC :=
  ⟨PhiC_isPoisson, PhiC_not_automorphism⟩

end

end RankTwoPoisson
