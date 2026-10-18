import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.FiltrationSeparation
import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.StableCoordinate.FilteredRees
import Tengoku.Seed.Algebra.MvPolynomial.Eval
import Tengoku.Seed.RingTheory.MvPolynomial.WeightedHomogeneous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace OAI

/-!
# The polynomial map onto the actual associated graded algebra

For the source's exact integer weight and the quotient/image filtration,
this file constructs the algebra map from the five-variable polynomial ring
to the Rees special fiber and proves surjectivity. No identification of the
associated graded ring is assumed.
-/

namespace StableCoordinate.GradedPresentationMap

open MvPolynomial
open Filtration FilteredRees

noncomputable section

variable {k A : Type*} [CommRing k] [CommRing A] [Algebra k A]
variable (φ : MvPolynomial (Fin 5) k →ₐ[k] A)

abbrev imageGr := Gr (imagePiece φ) (imagePiece_mono φ)

/-- A variable as a member of its assigned image-filtration piece. -/
def variableElement (i : Fin 5) :
    imagePiece φ (monomialWeight (Finsupp.single i 1)) :=
  ⟨φ (X i), X i, X_mem_piece i, rfl⟩

/-- The homogeneous polynomial map into the extended Rees algebra. -/
def reesMap : MvPolynomial (Fin 5) k →ₐ[k] rees (imagePiece φ) :=
  aeval fun i => homogeneous (imagePiece φ)
    (monomialWeight (Finsupp.single i 1)) (variableElement φ i)

/-- The natural ring map from the source polynomial ring into the actual
associated graded algebra. -/
def gradedMap : MvPolynomial (Fin 5) k →ₐ[k] imageGr φ :=
  (Ideal.Quotient.mkₐ k (parameterIdeal (imagePiece φ) (imagePiece_mono φ))).comp (reesMap φ)

@[simp] theorem gradedMap_X (i : Fin 5) :
    gradedMap φ (X i) = initial (imagePiece φ) (imagePiece_mono φ)
      (monomialWeight (Finsupp.single i 1)) (variableElement φ i) := by
  simp [gradedMap, reesMap, initial]

theorem monomialWeight_single (i : Fin 5) (n : ℕ) :
    monomialWeight (Finsupp.single i n) =
      (n : ℤ) * monomialWeight (Finsupp.single i 1) := by
  fin_cases i <;> simp [monomialWeight]

/-- Compatibility of the source's explicit exponent formula with mathlib's
general weighted-polynomial API. -/
theorem monomialWeight_eq_weight (w : Fin 5 → ℤ)
    (hw : ∀ i, w i = monomialWeight (Finsupp.single i 1)) :
    monomialWeight = Finsupp.weight w := by
  apply Finsupp.addHom_ext
  intro i n
  rw [monomialWeight_single, Finsupp.weight_single, hw]
  simp only [nsmul_eq_mul]

/-- A monomial as a member of its assigned image-filtration piece. -/
def monomialElement (e : Fin 5 →₀ ℕ) (c : k) :
    imagePiece φ (monomialWeight e) :=
  ⟨φ (monomial e c), monomial e c, monomial_mem_piece k le_rfl c, rfl⟩

/-- The Rees map preserves each monomial with its exact integer weight. -/
theorem reesMap_monomial_coe (e : Fin 5 →₀ ℕ) (c : k) :
    (reesMap φ (monomial e c) : LaurentPolynomial A) =
      AddMonoidAlgebra.single (monomialWeight e) (φ (monomial e c)) := by
  induction e using Finsupp.induction with
  | zero =>
      rw [monomial_zero', map_zero, algHom_C, algHom_C]
      rfl
  | single_add i n e hi hn ih =>
      rw [add_comm (Finsupp.single i n) e, monomial_add_single,
        map_mul, map_pow]
      change (reesMap φ (monomial e c) : LaurentPolynomial A) *
        (reesMap φ (X i) : LaurentPolynomial A) ^ n = _
      rw [ih]
      rw [map_add, monomialWeight_single i n]
      simp only [reesMap, aeval_X, homogeneous_coe, variableElement,
        AddMonoidAlgebra.single_pow, AddMonoidAlgebra.single_mul_single,
        nsmul_eq_mul]
      congr 1
      simp only [map_mul, map_pow]

/-- The exact coefficient formula, useful for identifying the kernel of
the polynomial map degree by degree. -/
theorem reesMap_coeff (p : MvPolynomial (Fin 5) k) (d : ℤ) :
    (reesMap φ p : LaurentPolynomial A).coeff d =
      φ (∑ e ∈ p.support, if monomialWeight e = d then monomial e (p.coeff e) else 0) := by
  classical
  have hp : reesMap φ p = ∑ e ∈ p.support, reesMap φ (monomial e (p.coeff e)) := by
    rw [← map_sum]
    exact congrArg (reesMap φ) p.as_sum
  rw [hp]
  change ((rees (imagePiece φ)).val
    (∑ e ∈ p.support, reesMap φ (monomial e (p.coeff e)))).coeff d = _
  rw [map_sum]
  simp only [AddMonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  change (reesMap φ (monomial e (p.coeff e)) : LaurentPolynomial A).coeff d = _
  rw [reesMap_monomial_coe]
  by_cases h : monomialWeight e = d <;>
    simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply, h,
      ite_true, ite_false, map_zero]

/-- The Rees representative's degree-`d` coefficient is the image of the
mathlib weighted homogeneous component. -/
theorem reesMap_coeff_weightedComponent (w : Fin 5 → ℤ)
    (hw : ∀ i, w i = monomialWeight (Finsupp.single i 1))
    (p : MvPolynomial (Fin 5) k) (d : ℤ) :
    (reesMap φ p : LaurentPolynomial A).coeff d =
      φ (weightedHomogeneousComponent w d p) := by
  classical
  rw [reesMap_coeff, weightedHomogeneousComponent_apply]
  simp only [← monomialWeight_eq_weight w hw, Finset.sum_filter]

/-- A homogeneous source polynomial has precisely its expected Rees symbol. -/
theorem reesMap_coe_of_homogeneous (p : MvPolynomial (Fin 5) k) (d : ℤ)
    (hp : ∀ e ∈ p.support, monomialWeight e = d) :
    (reesMap φ p : LaurentPolynomial A) = AddMonoidAlgebra.single d (φ p) := by
  classical
  have he : reesMap φ p = ∑ e ∈ p.support, reesMap φ (monomial e (p.coeff e)) := by
    rw [← map_sum]
    exact congrArg (reesMap φ) p.as_sum
  rw [he]
  change (rees (imagePiece φ)).val
    (∑ e ∈ p.support, reesMap φ (monomial e (p.coeff e))) = _
  rw [map_sum]
  calc
    ∑ e ∈ p.support, (reesMap φ (monomial e (p.coeff e)) : LaurentPolynomial A) =
        ∑ e ∈ p.support, AddMonoidAlgebra.single d (φ (monomial e (p.coeff e))) := by
          apply Finset.sum_congr rfl
          intro e he
          rw [reesMap_monomial_coe, hp e he]
    _ = AddMonoidAlgebra.single d (φ p) := by
      change (∑ e ∈ p.support,
        (AddMonoidAlgebra.singleAddHom d) (φ (monomial e (p.coeff e)))) =
          (AddMonoidAlgebra.singleAddHom d) (φ p)
      rw [← map_sum (AddMonoidAlgebra.singleAddHom d), ← map_sum]
      exact congrArg (fun q => AddMonoidAlgebra.single d (φ q)) p.as_sum.symm

/-- The homogeneous symbol is linear within a fixed filtration degree. -/
def initialLinear (d : ℤ) : imagePiece φ d →ₗ[k] imageGr φ where
  toFun := initial (imagePiece φ) (imagePiece_mono φ) d
  map_add' a b := initial_add (imagePiece φ) (imagePiece_mono φ) d a b
  map_smul' c a := by
    change (Ideal.Quotient.mkₐ k _) (homogeneous _ d (c • a)) =
      c • (Ideal.Quotient.mkₐ k _) (homogeneous _ d a)
    rw [← map_smul]
    congr 1
    apply Subtype.ext
    exact (AddMonoidAlgebra.smul_single c d (a : A)).symm

/-- The presentation map restricted to one source filtration piece. -/
def imagePieceMap (d : ℤ) : piece k d →ₗ[k] imagePiece φ d where
  toFun p := ⟨φ p, p, p.property, rfl⟩
  map_add' p q := Subtype.ext (map_add φ (p : MvPolynomial (Fin 5) k) q)
  map_smul' c p := Subtype.ext (map_smul φ c (p : MvPolynomial (Fin 5) k))

/-- A source polynomial of weight at most `d` has a degree-`d` symbol. -/
def sourceInitial (d : ℤ) : piece k d →ₗ[k] imageGr φ :=
  (initialLinear φ d).comp (imagePieceMap φ d)

@[simp] theorem sourceInitial_apply (d : ℤ) (p : piece k d) :
    sourceInitial φ d p = initial (imagePiece φ) (imagePiece_mono φ) d
      ⟨φ p, p, p.property, rfl⟩ := rfl

end

end StableCoordinate.GradedPresentationMap

end OAI
