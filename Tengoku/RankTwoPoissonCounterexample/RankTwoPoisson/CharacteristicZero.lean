import Tengoku.RankTwoPoissonCounterexample.RankTwoPoisson.Collision

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The rank-two Poisson counterexample over every characteristic-zero field

The explicit polynomials have rational coefficients. This file extends them
coefficientwise from `ℚ` to an arbitrary field `K` of characteristic zero,
proves that formal differentiation and the canonical Poisson bracket commute
with this extension, and transports the explicit rational collision to `K`.

The main theorem is `explicit_counterexample_charZero`.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace RankTwoPoisson

noncomputable section

open MvPolynomial

universe u

section CharacteristicZero

variable (K : Type u) [Field K] [CharZero K]

/-- Coefficientwise extension from rational polynomials to polynomials over `K`.-/
def mapK : P →+* MvPolynomial Var K :=
  MvPolynomial.map (algebraMap ℚ K)

/-- Formal polynomial differentiation over `K`.-/
def polyDerivK (i : Var) (f : MvPolynomial Var K) : MvPolynomial Var K :=
  MvPolynomial.pderiv i f

/-- The canonical Poisson bracket on `K[x,q,p,z]`.-/
def bracketK (f g : MvPolynomial Var K) : MvPolynomial Var K :=
    polyDerivK K 2 f * polyDerivK K 0 g - polyDerivK K 0 f * polyDerivK K 2 g
  + polyDerivK K 3 f * polyDerivK K 1 g - polyDerivK K 1 f * polyDerivK K 3 g

/-- The rational output tuple after coefficient extension to `K`.-/
def outputK (i : Var) : MvPolynomial Var K := mapK K (output i)

/-- The substitution endomorphism over `K`.-/
def PhiK : MvPolynomial Var K →ₐ[K] MvPolynomial Var K :=
  MvPolynomial.aeval (outputK K)

/-- Preservation of the canonical Poisson bracket over `K`.-/
def IsPoissonK (φ : MvPolynomial Var K →ₐ[K] MvPolynomial Var K) : Prop :=
  ∀ f g : MvPolynomial Var K, bracketK K (φ f) (φ g) = φ (bracketK K f g)

/-- Being induced by a `K`-algebra equivalence.-/
def IsAlgAutomorphismK
    (φ : MvPolynomial Var K →ₐ[K] MvPolynomial Var K) : Prop :=
  ∃ e : MvPolynomial Var K ≃ₐ[K] MvPolynomial Var K, e.toAlgHom = φ

/-- The point map associated with a polynomial algebra endomorphism over `K`.-/
def pointMapK
    (φ : MvPolynomial Var K →ₐ[K] MvPolynomial Var K)
    (v : Var → K) : Var → K :=
  fun i => MvPolynomial.aeval v (φ (X i))

/-- Formal differentiation commutes with coefficient extension.-/
theorem polyDeriv_mapK (i : Var) (f : P) :
    polyDerivK K i (mapK K f) = mapK K (polyDeriv i f) := by
  simp [polyDerivK, polyDeriv, mapK, MvPolynomial.pderiv_map]

/-- The canonical bracket commutes with coefficient extension.-/
theorem bracket_mapK (f g : P) :
    bracketK K (mapK K f) (mapK K g) = mapK K (bracket f g) := by
  simp only [bracketK, bracket, polyDeriv_mapK, map_sub, map_add, map_mul]

/-- Additivity in the first argument.-/
theorem bracketK_add_left (f g h : MvPolynomial Var K) :
    bracketK K (f + g) h = bracketK K f h + bracketK K g h := by
  simp [bracketK, polyDerivK]
  ring

/-- Additivity in the second argument.-/
theorem bracketK_add_right (f g h : MvPolynomial Var K) :
    bracketK K f (g + h) = bracketK K f g + bracketK K f h := by
  simp [bracketK, polyDerivK]
  ring

/-- Leibniz rule in the first argument.-/
theorem bracketK_mul_left (f g h : MvPolynomial Var K) :
    bracketK K (f * g) h = f * bracketK K g h + g * bracketK K f h := by
  simp [bracketK, polyDerivK]
  ring

/-- Leibniz rule in the second argument.-/
theorem bracketK_mul_right (f g h : MvPolynomial Var K) :
    bracketK K f (g * h) = g * bracketK K f h + h * bracketK K f g := by
  simp [bracketK, polyDerivK]
  ring

@[simp] theorem bracketK_C_left (c : K) (f : MvPolynomial Var K) :
    bracketK K (C c) f = 0 := by
  simp [bracketK, polyDerivK]

@[simp] theorem bracketK_C_right (f : MvPolynomial Var K) (c : K) :
    bracketK K f (C c) = 0 := by
  simp [bracketK, polyDerivK]

/-- The canonical bracket matrix after casting its rational entries into `K`.-/
def canonicalMatrixK (i j : Var) : K := algebraMap ℚ K (canonicalMatrix i j)

/-- The source generators over `K` have the canonical bracket matrix.-/
theorem bracketK_X_X (i j : Var) :
    bracketK K (X i) (X j) = C (canonicalMatrixK K i j) := by
  fin_cases i <;> fin_cases j <;>
    simp [bracketK, polyDerivK, canonicalMatrixK, canonicalMatrix]

/-- The output generators over `K` have the same canonical bracket matrix.-/
theorem bracketK_outputK_outputK (i j : Var) :
    bracketK K (outputK K i) (outputK K j) = C (canonicalMatrixK K i j) := by
  calc
    bracketK K (outputK K i) (outputK K j)
        = mapK K (bracket (output i) (output j)) := by
            simp [outputK, bracket_mapK]
    _ = mapK K (C (canonicalMatrix i j)) := by
          exact congrArg (mapK K) (bracket_output_output i j)
    _ = C (canonicalMatrixK K i j) := by
          simp [mapK, canonicalMatrixK]

@[simp] theorem PhiK_X (i : Var) : PhiK K (X i) = outputK K i := by
  simp [PhiK]

/-- Preservation of brackets on the four polynomial generators over `K`.-/
theorem PhiK_generator_bracket (i j : Var) :
    bracketK K (PhiK K (X i)) (PhiK K (X j))
      = PhiK K (bracketK K (X i) (X j)) := by
  rw [PhiK_X, PhiK_X, bracketK_outputK_outputK, bracketK_X_X]
  simp [PhiK]

/-- Preservation against a generator, promoted to every polynomial over `K`.-/
lemma PhiK_preserves_right_generator
    (i : Var) (f : MvPolynomial Var K) :
    bracketK K (PhiK K f) (PhiK K (X i))
      = PhiK K (bracketK K f (X i)) := by
  refine MvPolynomial.induction_on
    (motive := fun h : MvPolynomial Var K =>
      bracketK K (PhiK K h) (PhiK K (X i))
        = PhiK K (bracketK K h (X i)))
    f ?_ ?_ ?_
  · intro c
    simp
  · intro f g hf hg
    simp only [map_add, bracketK_add_left]
    exact congrArg₂ (· + ·) hf hg
  · intro f j hf
    simp only [map_mul, map_add, bracketK_mul_left]
    rw [PhiK_generator_bracket, hf]

/-- The substitution over `K` preserves the bracket on all polynomials.-/
theorem PhiK_isPoisson : IsPoissonK K (PhiK K) := by
  intro f g
  refine MvPolynomial.induction_on
    (motive := fun h : MvPolynomial Var K =>
      bracketK K (PhiK K f) (PhiK K h) = PhiK K (bracketK K f h))
    g ?_ ?_ ?_
  · intro c
    simp
  · intro g h hg hh
    simp only [map_add, bracketK_add_right]
    exact congrArg₂ (· + ·) hg hh
  · intro g j hg
    simp only [map_mul, map_add, bracketK_mul_right]
    rw [PhiK_preserves_right_generator, hg]

/-- Embed a rational point into affine space over `K`.-/
def fieldPoint (v : Var → ℚ) : Var → K :=
  fun i => algebraMap ℚ K (v i)

/-- Evaluation commutes with extending coefficients and rational points to `K`.-/
theorem aeval_mapK_fieldPoint (v : Var → ℚ) (f : P) :
    MvPolynomial.aeval (fieldPoint K v) (mapK K f)
      = algebraMap ℚ K (MvPolynomial.aeval v f) := by
  have hpoint : fieldPoint K v = (algebraMap ℚ K) ∘ v := by
    funext i
    rfl
  rw [hpoint]
  simpa only [mapK, MvPolynomial.aeval_eq_eval] using
    (MvPolynomial.map_eval (algebraMap ℚ K) v f).symm

/-- The point map over `K` on embedded rational points is the embedded rational point map.-/
theorem pointMapK_PhiK_fieldPoint (v : Var → ℚ) :
    pointMapK K (PhiK K) (fieldPoint K v) = fieldPoint K (pointMap Phi v) := by
  funext i
  simp [pointMapK, PhiK, outputK, pointMap, Phi,
    fieldPoint, aeval_mapK_fieldPoint]

/-- The first two rational collision points viewed as points over `K`.-/
def point0K : Var → K := fieldPoint K point0

def point1K : Var → K := fieldPoint K point1

/-- Their common target over `K`.-/
def targetK : Var → K := fieldPoint K target

/-- The first point over `K` maps to the common target.-/
theorem point0K_image : pointMapK K (PhiK K) (point0K K) = targetK K := by
  rw [point0K, targetK, pointMapK_PhiK_fieldPoint, point0_image]

/-- The second point over `K` maps to the common target.-/
theorem point1K_image : pointMapK K (PhiK K) (point1K K) = targetK K := by
  rw [point1K, targetK, pointMapK_PhiK_fieldPoint, point1_image]

/-- The two source points remain distinct over every characteristic-zero field.-/
theorem point0K_ne_point1K : point0K K ≠ point1K K := by
  intro h
  have h0 := congrFun h 0
  have h01 : (0 : K) = 1 := by
    simpa [point0K, point1K, fieldPoint, point0, point1] using h0
  exact zero_ne_one h01

/-- A polynomial algebra equivalence induces an injective map on `K`-points.-/
theorem pointMapK_of_equiv_injective
    (e : MvPolynomial Var K ≃ₐ[K] MvPolynomial Var K) :
    Function.Injective (pointMapK K e.toAlgHom) := by
  intro v w h
  funext i
  have hcomp :
      (MvPolynomial.aeval v).comp e.toAlgHom =
      (MvPolynomial.aeval w).comp e.toAlgHom := by
    apply MvPolynomial.algHom_ext
    intro j
    simpa [pointMapK] using congrFun h j
  have hi := congrArg
    (fun φ : MvPolynomial Var K →ₐ[K] K => φ (e.symm (X i))) hcomp
  simpa using hi

/-- The explicit substitution over `K` is not induced by an algebra equivalence.-/
theorem PhiK_not_automorphism : ¬ IsAlgAutomorphismK K (PhiK K) := by
  rintro ⟨e, he⟩
  have hcollision :
      pointMapK K (PhiK K) (point0K K) = pointMapK K (PhiK K) (point1K K) :=
    (point0K_image K).trans (point1K_image K).symm
  have hcollision' :
      pointMapK K e.toAlgHom (point0K K) = pointMapK K e.toAlgHom (point1K K) := by
    simpa [he] using hcollision
  have hp : point0K K = point1K K :=
    pointMapK_of_equiv_injective K e hcollision'
  exact point0K_ne_point1K K hp

/--
The explicit rank-two Poisson counterexample over every characteristic-zero
field. The same rational formulas define a bracket-preserving endomorphism of
`K[x,q,p,z]` that is not an automorphism.-/
theorem explicit_counterexample_charZero :
    IsPoissonK K (PhiK K) ∧ ¬ IsAlgAutomorphismK K (PhiK K) :=
  ⟨PhiK_isPoisson K, PhiK_not_automorphism K⟩

end CharacteristicZero

end

end RankTwoPoisson
